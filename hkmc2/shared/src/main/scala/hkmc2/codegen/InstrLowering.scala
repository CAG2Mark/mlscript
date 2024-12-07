package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import hkmc2.{semantics => sem}
import hkmc2.semantics.{Term => st}

import syntax.{Literal, Tree, ParamBind}
import semantics.*
import Elaborator.State

import Subst.subst
import scala.annotation.tailrec
import hkmc2.syntax.Keyword.`val`

import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet

object InstrLowering:

  private val pcIdent: Tree.Ident = Tree.Ident("__pc")
  private val isContIdent: Tree.Ident = Tree.Ident("__isCont") // FIXME: hack
  private val nextIdent: Tree.Ident = Tree.Ident("next")
  private val tailIdent: Tree.Ident = Tree.Ident("tail")
  private val handlerIdent: Tree.Ident = Tree.Ident("handler")
  private val handlerFunIdent: Tree.Ident = Tree.Ident("handlerFun")
  private val paramsIdent: Tree.Ident = Tree.Ident("params")
  extension (k: Block => Block)
    
    def chain(other: Block => Block): Block => Block = b => k(other(b))
    def rest(b: Block): Block = k(b)
    def transform(f: (Block => Block) => (Block => Block)) = f(k)
    
    def assign(l: Local, r: Result) = k.chain(Assign(l, r, _))
    def assignFieldN(lhs: Path, nme: Tree.Ident, rhs: Result) = k.chain(AssignField(lhs, nme, rhs, _)(N))
    def break(l: Local): Block = k.rest(Break(l))
    def continue(l: Local): Block = k.rest(Continue(l))
    def define(defn: Defn) = k.chain(Define(defn, _))
    def end() = k.rest(End())
    def ifthen(scrut: Path, cse: Case, trm: Block): Block => Block = k.chain(Match(scrut, cse -> trm :: Nil, N, _))
    def label(label: Local, body: Block) = k.chain(Label(label, body, _))
    def ret(r: Result) = k.rest(Return(r, false))
    def staticif(b: Boolean, f: (Block => Block) => (Block => Block)) = if b then k.transform(f) else k
    
  private def blockBuilder: Block => Block = identity
  extension (p: Path)
    def selN(id: Tree.Ident) = Select(p, id)(N)
    def pc = p.selN(pcIdent)
    def isContHack = p.selN(isContIdent)
    def next = p.selN(nextIdent)
    def tail = p.selN(tailIdent)
    def asArg = Arg(false, p)
  extension (l: Local)
    def asPath: Path = Value.Ref(l)
  
import InstrLowering.*

class InstrLowering(using TL, Raise, Elaborator.State) extends Lowering:
  
  // Opt-Level 1 => builtin is not function call
  // Opt-Level 2 => Tail-Call & Cont class elimination
  private val optimize: Int = 1
  
  private val contCls: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(Tree.Ident("__Cont")).selN(Tree.Ident("class"))
  private val resumeFun: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(Tree.Ident("__resume"))
  private class HandlerCtx:
    private var handlers: List[Result => Block] = (_ => Throw(
      Instantiate(State.globalThisSymbol.asPath.selN(Tree.Ident("Error")),
      Value.Lit(Tree.StrLit("Unhandled effects")) :: Nil)
    )) :: Nil
    private var allLocals: List[Set[Local]] = Set.empty :: Nil
    private var toSave: List[Set[Local]] = Set.empty :: Nil
    private var contClasses: List[ClassSymbol] = Nil
    private var tailCallEligible: List[Bool] = false :: Nil
    private var levels: Int = 0
    def canPreserveTailCall(): Bool = tailCallEligible.head
    def linkAndHandle(pc: BigInt, res: Path, tmp: Local, symbolResolver: (ClassSymbol, Local) => TermSymbol): Block =
      if levels == 0 then handlers.head(res) else instCont(pc, res, tmp, symbolResolver)(handlers.head(_))
    def addSavedVar(l: Local)(scoped: => Block): Block =
      allLocals = allLocals.head + l :: allLocals.tail
      val oldSave = toSave
      toSave = toSave.head + l :: toSave.tail
      val result = scoped
      toSave = oldSave
      result
    def addSavedVars(l: IterableOnce[Local])(scoped: => Block): Block =
      allLocals = allLocals.head ++ l :: allLocals.tail
      val oldSave = toSave
      toSave = toSave.head ++ l :: toSave.tail
      val result = scoped
      toSave = oldSave
      result
    private def instCont(pc: BigInt, res: Path, tmp: Local, symbolResolver: (ClassSymbol, Local) => TermSymbol)(k: Result => Block): Block =
      blockBuilder
        .assign(tmp, Instantiate(BlockMemberSymbol(contClasses.head.id.name, Nil).asPath, Value.Lit(Tree.IntLit(pc)) :: Value.Lit(Tree.UnitLit(true)) :: Nil))
        .assignFieldN(tmp.asPath, pcIdent, Value.Lit(Tree.IntLit(pc)))
        .assignFieldN(tmp.asPath, isContIdent, Value.Lit(Tree.BoolLit(true)))
        .transform(toSave.head.foldLeft(_)((res, loc) =>
          res.assignFieldN(tmp.asPath, symbolResolver(contClasses.head, loc).id, loc.asPath)
        ))
        .assignFieldN(tmp.asPath, nextIdent, res.tail.next)
        .assignFieldN(res.tail, nextIdent, tmp.asPath)
        .assignFieldN(res, tailIdent, tmp.asPath)
        .rest(k(res))
    def handleScoped(contClass: ClassSymbol, handler: Result => Block, tce: Bool = false)(scoped: => Block): (Set[Local], Block) =
      handlers ::= handler
      allLocals ::= Set.empty
      toSave ::= Set.empty
      contClasses ::= contClass
      tailCallEligible ::= tce
      levels += 1
      val result = scoped
      val locals = allLocals.head
      levels -= 1
      tailCallEligible = tailCallEligible.tail
      contClasses = contClasses.tail
      toSave = toSave.tail
      allLocals = allLocals.tail
      handlers = handlers.tail
      (locals, result)
    def handleFun(contClass: ClassSymbol)(scoped: => Block): (Set[Local], Block) =
      handleScoped(contClass, Return(_, false), true)(scoped)
  private def instCont(resume: Path): Result =
    Instantiate(contCls, resume :: Value.Lit(Tree.BoolLit(false)) :: Value.Lit(Tree.UnitLit(true)) :: Value.Lit(Tree.BoolLit(true)) :: Nil)
  
  
  private val handlerCtx = HandlerCtx()

  private def freshTmp(dbgNme: Str = "tmp") = new TempSymbol(N, dbgNme)
  // special function denoting state transitions, transitionFn should never appear in the real output
  private val transitionSymbol = freshTmp("transition")
  private val separationSymbol = freshTmp("separator")
  private class FreshId:
    var id: Int = 0
    def apply() =
      val tmp = id
      id += 1
      tmp
  private val freshId = FreshId()

  type StateId = BigInt

  // id: the id of the current state
  // blk: the block of code within this state
  // sym: the variable to which the resumed value should set
  class BlockState(val id: StateId, val blk: Block, val sym: Opt[Local])
  
  object SimpleCall:
    def apply(fun: Path, args: List[Path]) = Call(fun, args.map(Arg(false, _)))(true)
    def unapply(res: Result) = res match
      case Call(fun, args) => args.foldRight[Opt[List[Path]]](S(Nil))((arg, acc) => acc.flatMap(acc => arg match
        case Arg(false, p) => S(p :: acc)
        case _ => N
      )).map((fun, _))
      case _ => N

  // Note: can construct StateTransition and pattern match on it as if it were a case class
  object StateTransition:
    def apply(uid: StateId) = Return(SimpleCall(Value.Ref(transitionSymbol), List(Value.Lit(Tree.IntLit(uid)))), false)
    def unapply(blk: Block) = blk match
      case Return(SimpleCall(Value.Ref(`transitionSymbol`), List(Value.Lit(Tree.IntLit(uid)))), false) if uid >= 0 =>
        S(uid)
      case _ => N 

  object Separation:
    def apply(res: Local, uid: StateId, rest: Block) =
      Assign(res, SimpleCall(Value.Ref(separationSymbol), List(Value.Lit(Tree.IntLit(uid)))), rest)
    def unapply(blk: Block) = blk match
      case Assign(res, SimpleCall(Value.Ref(`separationSymbol`), List(Value.Lit(Tree.IntLit(uid)))), rest) => 
        Some(res, uid, rest)
      case _ => None
  
  object ReturnCont:
    private val returnContSymbol = freshTmp("returnCont")
    def apply(res: Local, uid: StateId, rest: Block) =
      Assign(res, SimpleCall(Value.Ref(returnContSymbol), List(Value.Lit(Tree.IntLit(uid)))), rest)
    def unapply(blk: Block) = blk match
      case Assign(res, SimpleCall(Value.Ref(`returnContSymbol`), List(Value.Lit(Tree.IntLit(uid)))), rest) => 
        Some(res, uid, rest)
      case _ => None
  
  extension (k: Block => Block)
    def separation(res: Local, uid: StateId): Block => Block = b => k(Separation(res, uid, b))
    def returnCont(res: Local, uid: StateId): Block => Block = b => k(ReturnCont(res, uid, b))

  object FnEnd:
    def apply() = Return(SimpleCall(Value.Ref(transitionSymbol), List(Value.Lit(Tree.IntLit(-1)))), false)
    def unapply(blk: Block) = blk match
      case Return(SimpleCall(Value.Ref(`transitionSymbol`), List(Value.Lit(Tree.IntLit(uid)))), false) if  uid == -1 =>
        true
      case _ => false 


  /* 
  Partition a function into a graph of states
  where states are separated by function calls
  the truncated blocks includes the delimiting function call
  
  for example:
  let a = whatever
  if a then
    let x1 = foo()
    x1 + 1
  else
    let x2 = bar()
    x1 + 2
  becomes
  state 0:
  let a = whatever
  if a then
    let x1 = foo()
    <state transition into state 1>
  else
    let x2 = bar()
    <state transition into state 2>

  state 1:
    x1 + 1

  state 2:
    x2 + 2
  */
  def partitionBlock(blk: Block, labelIds: Map[Symbol, (StateId, StateId)] = Map.empty): Ls[BlockState] = 
    // for readability :)
    case class PartRet(head: Block, states: Ls[BlockState])

    // Note: can construct StateTransition and pattern match on it as if it were a case class
    object StateTransition:
      def apply(uid: StateId) = Return(SimpleCall(Value.Ref(transitionSymbol), List(Value.Lit(Tree.IntLit(uid)))), false)
      def unapply(blk: Block) = blk match
        case Return(SimpleCall(Value.Ref(`transitionSymbol`), List(Value.Lit(Tree.IntLit(uid)))), false) =>
          S(uid)
        case _ => N 

    // used to analyze whether to touch labels, currently unused.
    val labelCallCache: scala.collection.mutable.Map[Symbol, Bool] = scala.collection.mutable.Map()
    def containsCallRec(blk: Block): Bool = containsCall(blk)
    @tailrec
    def containsCall(blk: Block): Bool = blk match
      case Match(scrut, arms, dflt, rest) => arms.find((_, blk) => containsCallRec(blk)).isDefined || containsCall(rest)
      case Return(c: Call, implct) => true
      case Return(_, _) => false 
      case Throw(c: Call) => true
      case Throw(_) => false
      case l @ Label(label, body, rest) => 
        labelBodyHasCall(l) || containsCall(rest)
      case Break(label) => false
      case Continue(label) => false
      case Begin(sub, rest) => containsCallRec(sub) || containsCall(rest)
      case TryBlock(sub, finallyDo, rest) => containsCallRec(sub) || containsCallRec(finallyDo) || containsCall(rest)
      case Assign(lhs, c: Call, rest) => true
      case Assign(_, _, rest) => containsCall(rest)
      case AssignField(lhs, nme, c: Call, rest) => true
      case AssignField(_, _, _, rest) => containsCall(rest)
      case Define(defn, rest) => containsCall(rest)
      case End(msg) => false
    
    def labelBodyHasCall(blk: Label) =
      val Label(label, body, rest) = blk
      labelCallCache.get(label) match
        case N =>
          val res = containsCallRec(body)
          labelCallCache.addOne(label -> res)
          res
        case S(value) =>
          value

    // returns (truncated input block, child block states)
    // TODO: don't split within Match, Begin and Labels when not needed, ideally keep it intact. Need careful analysis for this
    // blk: The block to transform
    // labelIds: maps label IDs to the state at the start of the label and the state after the label
    // jumpTo: what state End should jump to, if at all 
    // freshState: uid generator
    def go(blk: Block)(implicit labelIds: Map[Symbol, (StateId, StateId)], afterEnd: Option[StateId]): PartRet = blk match
      case Separation(result, uid, rest) =>
        val PartRet(head, states) = go(rest)
        PartRet(StateTransition(uid), BlockState(uid, head, S(result)) :: states)

      case Match(scrut, arms, dflt, rest) => 
        val restParts = go(rest)
        val restId: StateId = restParts.head match
          case StateTransition(uid) => uid
          case _ => freshId()
        
        val armsParts = arms.map((cse, blkk) => (cse, go(blkk)(afterEnd = S(restId))))
        val dfltParts = dflt.map(blkk => go(blkk)(afterEnd = S(restId)))
        

        val states_ = restParts.states ::: armsParts.flatMap(_._2.states)
        val states = dfltParts match
          case N => states_
          case S(value) => value.states ::: states_

        val newArms = armsParts.map((cse, partRet) => (cse, partRet.head))
        
        restParts.head match
          case StateTransition(_) =>
            PartRet(
              Match(scrut, newArms, dfltParts.map(_.head), StateTransition(restId)),
              states
            )
          case _ =>
            PartRet(
              Match(scrut, newArms, dfltParts.map(_.head), StateTransition(restId)),
              BlockState(restId, restParts.head, N) :: states
            )
      case l @ Label(label, body, rest) =>
        val startId = freshId() // start of body

        val PartRet(restNew, restParts) = go(rest)

        val endId: StateId = restNew match // start of rest
          case StateTransition(uid) => uid 
          case _ => freshId()

        val PartRet(bodyNew, parts) = go(body)(using labelIds + (label -> (startId, endId)), S(endId))
        
        restNew match
          case StateTransition(_) =>
            PartRet(
              StateTransition(startId), 
              BlockState(startId, bodyNew, N) :: parts ::: restParts
            )
          case _ =>
            PartRet(
              StateTransition(startId), 
              BlockState(startId, bodyNew, N) :: BlockState(endId, restNew, N) :: parts ::: restParts
            )

      case Break(label) =>
        val (start, end) = labelIds.get(label) match
          case N => raise(ErrorReport(
            msg"Could not find label '${label.nme}'" ->
            label.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
            return PartRet(blk, Nil)
          case S(value) => value
        PartRet(StateTransition(end), Nil)
      case Continue(label) =>
        val (start, end) = labelIds.get(label) match
          case N => raise(ErrorReport(
            msg"Could not find label '${label.nme}'" ->
            label.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
            return PartRet(blk, Nil)
          case S(value) => value
        PartRet(StateTransition(start), Nil)

      case Begin(sub, rest) => 
        val PartRet(restNew, restParts) = go(rest)
        restNew match
          case StateTransition(uid) => 
            val PartRet(subNew, subParts) = go(sub)(afterEnd = S(uid))
            PartRet(subNew, subParts ::: restParts)
          case _ =>
            val restId = freshId()
            val PartRet(subNew, subParts) = go(sub)(afterEnd = S(restId))
            PartRet(subNew, BlockState(restId, restNew, N) :: subParts ::: restParts)

      case Define(defn, rest) => 
        val PartRet(head, parts) = go(rest)
        PartRet(Define(defn, head), parts)
      case End(_) | Return(Value.Lit(Tree.UnitLit(true)), true) => afterEnd match
        case None => PartRet(FnEnd(), Nil)
        case Some(value) => PartRet(StateTransition(value), Nil)
      // identity cases
      case Assign(lhs, rhs, rest) =>
        val PartRet(head, parts) = go(rest)
        PartRet(Assign(lhs, rhs, head), parts)
      case blk @ AssignField(lhs, nme, rhs, rest) =>
        val PartRet(head, parts) = go(rest)
        PartRet(blk.mapChildBlocks(_ => head), parts)
      case Return(_, _) => PartRet(blk, Nil)
      // ignored cases
      case TryBlock(sub, finallyDo, rest) => ??? // ignore
      case Throw(_) => PartRet(blk, Nil)

    val headId = freshId()

    val result = go(blk)(using labelIds, N)
    BlockState(headId, result.head, N) :: result.states
  
  val localsMap: MutMap[(ClassSymbol, Local), TermSymbol] = MutMap()
  private val freshFieldId = freshId
  // NOTE: Should only be used for function parameters or variables/values strictly defined in the function body!
  // TODO: for class methods, map `this.whatever` to `this.this$.whatever` ($this is the current class)
  def getContLocalSymbol(cls: ClassSymbol, sym: Local): TermSymbol =
    localsMap.get((cls, sym)) match
      case Some(value) => value
      case None => 
        val ret = TermSymbol(ParamBind, S(cls), Tree.Ident(s"${sym.nme}$$${freshFieldId()}"))
        localsMap.addOne((cls, sym) -> ret)
        ret

  // HACK: remove once match is fixed
  def unrollMatch(b: Match): Block =
    val Match(scrut, arms, dflt, rest) = b
    arms match
      case head :: Nil => b
      case head :: next => Match(
        scrut, List(head), 
        S(unrollMatch(Match(scrut, next, dflt, End()))),
        rest) 
      case Nil => rest
    
  // TODO: support class methods
  def createContClass(cls: ClassSymbol, body: Block, params: List[Local]): ClsLikeDefn =
    val parts = partitionBlock(body)

    val locals = params ::: body.definedLocals.toList 
    val localsMap = locals.map(l => l -> getContLocalSymbol(cls, l)).toMap
    def mapSym(l: Local) = localsMap.getOrElse(l, l)
    
    val loopLbl = freshTmp("contLoop")

    val pcSymbol = TermSymbol(ParamBind, S(cls), pcIdent)
    

    // NOTE: Symbols already replaced
    // TODO: set program counter when returning continuation
    def transformPart(blk: Block): Block = 
      def f(blk: Block): Block = blk match
        case ReturnCont(res, uid, rest) =>
          blockBuilder
            .assignFieldN(res.asPath.tail, nextIdent, cls.asPath)
            .assign(pcSymbol, Value.Lit(Tree.IntLit(uid)))
            .ret(res.asPath)
        case StateTransition(uid) =>
          blockBuilder
            .assign(pcSymbol, Value.Lit(Tree.IntLit(uid)))
            .continue(loopLbl)
        case FnEnd() =>
          blockBuilder.break(loopLbl)
        case c => c.mapChildBlocks(f)
      f(blk)

    // match block representing the function body
    val mainMatchCases = parts.toList.map(b => (Case.Lit(Tree.IntLit(b.id)), transformPart(b.blk.mapLocals(mapSym))))
    val mainMatchBlk = unrollMatch(Match(
      pcSymbol.asPath,
      mainMatchCases,
      N,
      End()
    ))

    val lbl = blockBuilder.label(loopLbl, mainMatchBlk).rest(End())
    
    val resumedVal = VarSymbol(Tree.Ident("value$"))

    def createAssignment(sym: Local) = Assign(sym, resumedVal.asPath, End())
    
    val assignedResumedCases = for 
      b   <- parts
      sym <- b.sym
    yield Case.Lit(Tree.IntLit(b.id)) -> createAssignment(localsMap(sym)) // NOTE: assume sym is in localsMap

    // assigns the resumed value
    val resumeBody = 
      if assignedResumedCases.isEmpty then
        lbl
      else
        unrollMatch(Match(
          pcSymbol.asPath,
          assignedResumedCases,
          S(End()),
          lbl
        ))
    
    val sym = BlockMemberSymbol("resume", List())
    val resumeFnDef = FunDefn(
      BlockMemberSymbol("resume", List()),
      List(PlainParamList(List(Param(FldFlags.empty, resumedVal, N)))),
      resumeBody
    )

    // HACK: see JSBuilder:154
    val clsDef = ClassDef(
      None,
      syntax.Cls,
      cls,
      List(),
      S(PlainParamList(List(Param(FldFlags.empty, resumedVal, N)))),
      ObjBody(st.Blk(Nil, st.Lit(Tree.UnitLit(true))))
    )
    sym.defn = S(clsDef)
    
    ClsLikeDefn(
      cls,
      syntax.Cls,
      List(resumeFnDef),
      List(),
      List(),
      End()
    )
    

  // Create the symbol for the continuation
  // This should only be called once because symbols contain a uid internally
  def getContClassSymbol(sym: Opt[BlockMemberSymbol]): ClassSymbol =
    ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
      Tree.Ident("Cont$" + State.suid.nextUid + "$" + sym.map((sym: BlockMemberSymbol) => sym.nme).getOrElse(""))
    )
  
  def removeMarkers(blk: Block): (Bool, Block) =
    var containMarker = false
    def go(blk: Block): Block = blk match
      case Separation(_, _, blk) =>
        containMarker = true
        go(blk)
      case ReturnCont(_, _, blk) =>
        containMarker = true
        go(blk)
      case _ => blk.mapChildBlocks(go)
    val result = go(blk)
    (containMarker, result)
  
  def instrumentBlock(sym: ClassSymbol, body: Block, locals: Set[Symbol], preTransform: Opt[Block => Block]): Block =
    val (containMarker, unmarkedBody) = removeMarkers(body)
    // Optimization: if there is no marker there is nothing to do
    if !containMarker && optimize >= 2 then return body
    val curClass = preTransform match
      case N => createContClass(sym, body, Nil)
      case S(transform) => createContClass(sym, transform(body), Nil)
    sym.defn = S(ClassDef(N, syntax.Cls, sym, Nil, N, ObjBody(st.Blk(Nil, Term.Lit(Tree.UnitLit(true))))))
    Define(curClass, unmarkedBody)

  override def term(t: st)(k: Result => Block)(using Subst): Block =
    t match
    case st.Blk((LetDecl(sym)) :: stats, res) =>
      handlerCtx.addSavedVar(sym) { super.term(t)(k) }
    case st.Blk((DefineVar(sym, rhs)) :: stats, res) =>
      handlerCtx.addSavedVar(sym) { super.term(t)(k) }
    case st.Blk((d: Declaration) :: stats, res) =>
      d match
      case td @ TermDefinition(k = syntax.Fun, body = S(bod)) =>
        val contClassSymbol = getContClassSymbol(S(td.sym))
        val (locals, bodRaw) = handlerCtx.handleFun(contClassSymbol) { returnedTerm(bod) }
        val bodTrm = instrumentBlock(contClassSymbol, bodRaw, locals, N)
        Define(FunDefn(td.sym, td.params, bodTrm),
          term(st.Blk(stats, res))(k))
      case cls: ClassLikeDef =>
        val bodBlk = cls.body.blk
        val (mtds, rest1) = bodBlk.stats.partitionMap:
          case td: TermDefinition if td.k is syntax.Fun => L(td)
          case s => R(s)
        val (privateFlds, rest2) = rest1.partitionMap:
          case LetDecl(sym: TermSymbol) => L(sym)
          case s => R(s)
        val publicFlds = rest2.collect:
          case td @ TermDefinition(k = (_: syntax.Val)) => td
        Define(ClsLikeDefn(cls.sym, syntax.Cls,
            mtds.flatMap: td =>
              td.body.map: bod =>
                val contClassSymbol = getContClassSymbol(S(td.sym))
                val (locals, bodRaw) = handlerCtx.handleFun(contClassSymbol) { returnedTerm(bod) }
                val bodTrm = instrumentBlock(contClassSymbol, bodRaw, locals, N)
                FunDefn(td.sym, td.params, bodTrm)
            ,
            privateFlds,
            publicFlds,
            term(st.Blk(rest2, bodBlk.res))(ImplctRet).mapTail:
              case Return(Value.Lit(syntax.Tree.UnitLit(true)), true) => End()
              case t => t
          ),
        term(st.Blk(stats, res))(k))
      case _ => super.term(t)(k)
    case st.Blk(st.Handle(lhs, rhs, defs) :: stats, res) =>
      tl.log(s"Lowering.term ${t.showDbg.truncate(30, "[...]")}")
      val uid = freshId()
      // FIXME: Assumed defs are in the correct order, which is not checked currently
      val termHandlerFuns = (k: Ls[Value.Lam] => Block) => (defs.reverse.foldRight[Ls[Value.Lam] => Block](k)((df, acc) =>
        df match
        case TermDefinition(sym = sym, params = params) =>
          val realParams = params.head.params.dropRight(1)
          val idFuncX = VarSymbol(Tree.Ident("x"))
          val idFunc = Value.Lam(PlainParamList(Param(FldFlags.empty, idFuncX, N) :: Nil), Return(idFuncX.asPath, false))
          val cont = freshTmp("cont")
          
          val mkHandler: Path => Value.Lam = (sym: Path) => Value.Lam(PlainParamList(realParams),
            blockBuilder
              .assign(cont, instCont(Value.Lit(Tree.UnitLit(true))))
              .assignFieldN(cont.asPath, tailIdent, cont.asPath)
              .assignFieldN(cont.asPath, handlerIdent, lhs.asPath)
              .assignFieldN(cont.asPath, handlerFunIdent, sym)
              .assignFieldN(cont.asPath, paramsIdent, Value.Arr(realParams.map(p => p.sym.asPath.asArg)))
              .ret(cont.asPath)
          )
          // FIXME: do the dummy identifier do any harm?
          // This automatically instrument df as desired
          (args: Ls[Value.Lam]) => subTerm(st.Blk(df :: Nil, st.Ref(sym)(Tree.Ident("dummy"), -1)))(r => acc(mkHandler(r) :: args))
        case _ => _ => End("error") // only term definitions should appear
      ))(Nil)
      termHandlerFuns: handlerFuns =>
        subTerm(rhs): cls =>
          val cur = freshTmp("cur")
          val lblBdy = freshTmp("handlerBody")
          val lblH = freshTmp("handler")
          val handlerTailList = freshTmp("handlerTailList")
          val savedNext = freshTmp("savedNext")
          val tmp = freshTmp()
          
          val contClassSymbol = getContClassSymbol(N)
          val (locals, bodRaw) = handlerCtx.handleScoped(contClassSymbol, r =>
            Assign(cur, r, Break(lblBdy))
          ) { Assign(lhs, Instantiate(cls, handlerFuns), handlerCtx.addSavedVar(lhs){ term(st.Blk(stats, res))(r => Assign(cur, r, Break(lblBdy))) }) }
          
          def transformBodyBreaks(blk: Block): Block = blk match
            case Break(`lblBdy`) => Return(cur.asPath, false)
            case _ => blk.mapChildBlocks(transformBodyBreaks)
          
          val bod = instrumentBlock(contClassSymbol, bodRaw, locals, S(transformBodyBreaks))
          
          def getBinaryBuiltin(nme: Str) = BuiltinSymbol(nme, true, false, false)
          val equalBuiltin = getBinaryBuiltin("===").asPath
          val nequalBuiltin = getBinaryBuiltin("!==").asPath
          
          val equalToCurVal = SimpleCall(equalBuiltin, cur.asPath.selN(handlerIdent) :: lhs.asPath :: Nil)
          val notEqualToSavedNext = SimpleCall(nequalBuiltin, handlerTailList.asPath.next :: savedNext.asPath :: Nil)
          val tailNotEmpty = SimpleCall(nequalBuiltin, handlerTailList.asPath.next :: Value.Lit(Tree.UnitLit(true)) :: Nil)
          handlerCtx.addSavedVars(handlerTailList :: cur :: Nil) { blockBuilder
            .label(lblBdy, bod)
            .separation(cur, uid)
            .assign(handlerTailList, instCont(Value.Lit(Tree.UnitLit(true)))) // just a dummy link list head
            .label(lblH,
              blockBuilder.ifthen(cur.asPath, Case.Lit(Tree.BoolLit(true)), blockBuilder.ifthen(
                cur.asPath.selN(handlerIdent),
                Case.Lit(Tree.BoolLit(true)),
                blockBuilder
                  .assign(tmp, equalToCurVal)
                  .ifthen(tmp.asPath, Case.Lit(Tree.BoolLit(true)), blockBuilder
                    // resume = __resume(cur.next, tail)
                    .assign(tmp, SimpleCall(resumeFun, cur.asPath.next :: handlerTailList.asPath :: Nil))
                    // _ = cur.params.push(resume)
                    .assign(tmp, SimpleCall(cur.asPath.selN(paramsIdent).selN(Tree.Ident("push")), tmp.asPath :: Nil))
                    // savedNext = handlerTailList.next
                    .assign(savedNext, handlerTailList.asPath.next)
                    // cur = cur.handlerFun.apply(cur, cur.params)
                    .assign(cur, SimpleCall(cur.asPath.selN(handlerFunIdent).selN(Tree.Ident("apply")), cur.asPath :: cur.asPath.selN(paramsIdent) :: Nil))
                    // when handlerFun ends, it could be either
                    // 1. handled all effects
                    // 2. new effect raised
                    // In case 2, the handler will appended to the list wrongly, we fix it here
                    .assign(tmp, notEqualToSavedNext)
                    .ifthen(tmp.asPath, Case.Lit(Tree.BoolLit(true)),
                      AssignField(
                        handlerTailList.asPath.next,
                        nextIdent,
                        savedNext.asPath,
                        End()
                      )(N)
                    )
                    .continue(lblH)
                  ).rest(handlerCtx.linkAndHandle(uid, cur.asPath, tmp, getContLocalSymbol))
              ).end())
              .assign(tmp, tailNotEmpty)
              .ifthen(tmp.asPath, Case.Lit(Tree.BoolLit(true)), blockBuilder
                // cur = __resume(handlerTail.next, handlerTail)(cur)
                .assign(tmp, handlerTailList.asPath.next)
                .assignFieldN(handlerTailList.asPath, nextIdent, Value.Lit(Tree.UnitLit(true)))
                .assign(tmp, SimpleCall(resumeFun, tmp.asPath :: handlerTailList.asPath :: Nil))
                .assign(cur, SimpleCall(tmp.asPath, cur.asPath :: Nil))
                .continue(lblH)
              ).end()
            ) // lblH
            .rest(k(cur.asPath))
          }
    case st.App(st.Ref(_: BuiltinSymbol), args) if optimize >= 1 =>
      // Optimization: Assuming builtin symbols cannot have effect
      super.term(t)(k)
    case st.Ret(t: st.App) if handlerCtx.canPreserveTailCall() && optimize >= 2 =>
      // Optimization: we can simply return here
      super.term(t): r =>
        Return(r, false)
    case st.App(f, args) =>
      tl.log(s"Lowering.term ${t.showDbg.truncate(30, "[...]")}")
      val uid = freshId()
      val res = freshTmp("res")
      val tmp = freshTmp()
      super.term(t): r =>
        Assign(res, r,
          Match(
            // res.asPath,
            // Case.Cls(contSym, contTrm) -> handlerCtx.linkAndHandle(uid, res.asPath) :: Nil,
            // N,
            // Separation(res, uid, k(res.asPath))
            res.asPath, // here, res is either undefined or continuation so actually only need to check against undefined
            Case.Lit(Tree.BoolLit(true)) -> Match(
              res.asPath.isContHack,
              Case.Lit(Tree.BoolLit(true)) -> ReturnCont(res, uid, handlerCtx.linkAndHandle(uid, res.asPath, tmp, getContLocalSymbol)) :: Nil,
              N,
              End()
            ) :: Nil,
            N,
            Separation(res, uid, k(res.asPath))
          )
        )
    case st.Lam(params, body) =>
      val contClassSymbol = getContClassSymbol(N)
      val (locals, bodRaw) = handlerCtx.handleFun(contClassSymbol) { returnedTerm(body) }
      k(Value.Lam(params, instrumentBlock(contClassSymbol, bodRaw, locals, N)))
    case _ => super.term(t)(k)

  override def topLevel(t: st): Block =
    removeMarkers(super.topLevel(st.Blk(t :: Nil, st.Lit(Tree.UnitLit(true)))))._2
    