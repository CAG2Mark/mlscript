package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import hkmc2.{semantics => sem}
import hkmc2.semantics.{Term => st}

import syntax.{Literal, Tree, ParamBind}
import semantics.*
import semantics.Term.*

import Subst.subst
import scala.annotation.tailrec
import hkmc2.syntax.Keyword.`val`
import sem.Elaborator.Ctx.globalThisSymbol

import scala.collection.mutable.Map as MutMap
import scala.collection.mutable.Set as MutSet

object InstrLowering:
  extension (k: Block => Block)
    def assign(l: Local, r: Result): Block => Block = b => k(Assign(l, r, b))
    def assignField(lhs: Path, nme: Tree.Ident, rhs: Result): Block => Block = b => k(AssignField(lhs, nme, rhs, b))
    def break(l: Local): Block = k(Break(l, false))
    def chain(other: Block => Block): Block => Block = b => k(other(b))
    def continue(l: Local): Block = k(Break(l, true))
    def define(defn: Defn): Block => Block = b => k(Define(defn, b))
    def end(): Block = rest(End())
    def label(label: Local, body: Block): Block => Block = b => k(Label(label, body, b))
    def ret(r: Result): Block = k(Return(r, false))
    def rest(b: Block): Block = k(b)
  private def blockBuilder: Block => Block = identity
  private class HandlerCtx:
    private var handlers: List[Result => Block] = (_ => Throw(
      Instantiate(Select(Value.Ref(Elaborator.Ctx.globalThisSymbol), Tree.Ident("Error")),
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
      val resultHead = blockBuilder
        .assign(tmp, Instantiate(Value.Ref(BlockMemberSymbol(contClasses.head.id.name, Nil)), Value.Lit(Tree.IntLit(pc)) :: Value.Lit(Tree.UnitLit(true)) :: Nil))
        .assignField(Value.Ref(tmp), Tree.Ident("pc$0"), Value.Lit(Tree.IntLit(pc)))
        .assignField(Value.Ref(tmp), Tree.Ident("__isCont"), Value.Lit(Tree.BoolLit(true)))
      val resultSavedLocals = toSave.head.foldLeft(resultHead)((res, loc) =>
        res.assignField(Value.Ref(tmp), symbolResolver(contClasses.head, loc).id, Value.Ref(loc))
      )
      resultSavedLocals
        .assignField(Value.Ref(tmp), Tree.Ident("next"), Select(Select(res, Tree.Ident("tail")), Tree.Ident("next")))
        .assignField(Select(res, Tree.Ident("tail")), Tree.Ident("next"), Value.Ref(tmp))
        .assignField(res, Tree.Ident("tail"), Value.Ref(tmp))
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
import InstrLowering.*

class InstrLowering(using TL, Raise, Elaborator.State) extends Lowering:
  
  private val optimize: Bool = true

/*
  private val effectSigIdent: Tree.Ident = Tree.Ident("EffectSig$")
  private val effectSigTree: Tree.TypeDef = Tree.TypeDef(syntax.Cls, Tree.Error(), N, N)
  private val effectSigSym: ClassSymbol = ClassSymbol(effectSigTree, effectSigIdent)
  private val effectSigDef = ClassDef(
    N,
    syntax.Cls,
    effectSigSym,
    Nil,
    S(("handler" :: "handlerFun" :: "args" :: "cont" :: Nil).map(name =>
      Param(FldFlags.empty, TermSymbol(ParamBind, S(effectSigSym), Tree.Ident(name)), None)
    )),
    ObjBody(st.Blk(Nil, st.Lit(Tree.UnitLit(true)))))
  private val effectSigTrm = Select(Select(Value.Ref(Elaborator.Ctx.globalThisSymbol), effectSigIdent), Tree.Ident("class"))
  effectSigSym.defn = S(effectSigDef)
*/
  
  private val contIdent: Tree.Ident = Tree.Ident("Cont$")
  private val contTree: Tree.TypeDef = Tree.TypeDef(syntax.Cls, Tree.Error(), N, N)
  private val contSym: ClassSymbol = ClassSymbol(contTree, contIdent)
  private val contDef = ClassDef(
    S(globalThisSymbol),
    syntax.Cls,
    contSym,
    Nil,
    // FIXME: __isCont hack
    S(("resume" :: "resumed" :: "next" :: "__isCont" :: Nil).map(name =>
      Param(FldFlags.empty, TermSymbol(ParamBind, S(contSym), Tree.Ident(name)), None)
    )),
    ObjBody(st.Blk(Nil, st.Lit(Tree.UnitLit(true)))))
  private val contTrm = Select(Select(Value.Ref(Elaborator.Ctx.globalThisSymbol), contIdent), Tree.Ident("class"))
  // private val contTrm = Select(Value.Ref(contSym), Tree.Ident("class"))
  contSym.defn = S(contDef)
  
  private val resumeSym: BlockMemberSymbol = BlockMemberSymbol("resume$", Nil)
  
  private def instCont(resume: Path): Result =
    Instantiate(contTrm, resume :: Value.Lit(Tree.BoolLit(false)) :: Value.Lit(Tree.UnitLit(true)) :: Value.Lit(Tree.BoolLit(true)) :: Nil)
  
  
  private val handlerCtx = HandlerCtx()

  private def freshTmp(dbgNme: Str = "tmp") = new TempSymbol(summon[Elaborator.State].nextUid, N, dbgNme)
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

  // Note: can construct StateTransition and pattern match on it as if it were a case class
  object StateTransition:
    def apply(uid: StateId) = Return(Call(Value.Ref(transitionSymbol), List(Value.Lit(Tree.IntLit(uid)))), false)
    def unapply(blk: Block) = blk match
      case Return(Call(Value.Ref(`transitionSymbol`), List(Value.Lit(Tree.IntLit(uid)))), false) if uid >= 0 =>
        S(uid)
      case _ => N 

  object Separation:
    def apply(res: Local, uid: StateId, rest: Block) =
      Assign(res, Call(Value.Ref(separationSymbol), List(Value.Lit(Tree.IntLit(uid)))), rest)
    def unapply(blk: Block) = blk match
      case Assign(res, Call(Value.Ref(`separationSymbol`), List(Value.Lit(Tree.IntLit(uid)))), rest) => 
        Some(res, uid, rest)
      case _ => None
  
  object ReturnCont:
    private val returnContSymbol = freshTmp("returnCont")
    def apply(res: Local, uid: StateId, rest: Block) =
      Assign(res, Call(Value.Ref(returnContSymbol), List(Value.Lit(Tree.IntLit(uid)))), rest)
    def unapply(blk: Block) = blk match
      case Assign(res, Call(Value.Ref(`returnContSymbol`), List(Value.Lit(Tree.IntLit(uid)))), rest) => 
        Some(res, uid, rest)
      case _ => None
  
  extension (k: Block => Block)
    def separation(res: Local, uid: StateId): Block => Block = b => k(Separation(res, uid, b))
    def returnCont(res: Local, uid: StateId): Block => Block = b => k(ReturnCont(res, uid, b))
  private def blockBuilder: Block => Block = identity

  object FnEnd:
    def apply() = Return(Call(Value.Ref(transitionSymbol), List(Value.Lit(Tree.IntLit(-1)))), false)
    def unapply(blk: Block) = blk match
      case Return(Call(Value.Ref(`transitionSymbol`), List(Value.Lit(Tree.IntLit(uid)))), false) if  uid == -1 =>
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
      def apply(uid: StateId) = Return(Call(Value.Ref(transitionSymbol), List(Value.Lit(Tree.IntLit(uid)))), false)
      def unapply(blk: Block) = blk match
        case Return(Call(Value.Ref(`transitionSymbol`), List(Value.Lit(Tree.IntLit(uid)))), false) =>
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
      case Break(label, toBeginning) => false
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

      case Break(label, toBeginning) =>
        val (start, end) = labelIds.get(label) match
          case N => raise(ErrorReport(
            msg"Could not find label '${label.nme}'" ->
            label.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
            return PartRet(blk, Nil)
          case S(value) => value
        
        if toBeginning then
          PartRet(StateTransition(start), Nil)
        else
          PartRet(StateTransition(end), Nil)
        
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
      case AssignField(lhs, nme, rhs, rest) =>
        val PartRet(head, parts) = go(rest)
        PartRet(AssignField(lhs, nme, rhs, head), parts)
      case Return(_, _) => PartRet(blk, Nil)
      // ignored cases
      case TryBlock(sub, finallyDo, rest) => ??? // ignore
      case Throw(_) => PartRet(blk, Nil)

    val headId = freshId()

    val result = go(blk)(using labelIds, N)
    BlockState(headId, result.head, N) :: result.states
  
  val localsMap: MutMap[Local, TermSymbol] = MutMap()
  private val freshFieldId = freshId()
  // NOTE: Should only be used for function parameters or variables/values strictly defined in the function body!
  // TODO: for class methods, map `this.whatever` to `this.this$.whatever` ($this is the current class)
  def getContLocalSymbol(cls: ClassSymbol, sym: Local): TermSymbol =
    localsMap.get(sym) match
      case Some(value) => value
      case None => 
        val ret = TermSymbol(ParamBind, S(cls), Tree.Ident(s"${sym.nme}$$${freshFieldId}"))
        localsMap.addOne(sym -> ret)
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

    val pcSymbol = TermSymbol(ParamBind, S(cls), Tree.Ident(s"pc$$${freshFieldId}"))
    

    // NOTE: Symbols already replaced
    // TODO: set program counter when returning continuation
    def transformPart(blk: Block): Block = 
      def f(blk: Block): Block = blk match
        case ReturnCont(res, uid, rest) =>
          blockBuilder
            .assignField(Select(Value.Ref(res), Tree.Ident("tail")), Tree.Ident("next"), Value.Ref(cls))
            .assign(pcSymbol, Value.Lit(Tree.IntLit(uid)))
            .ret(Value.Ref(res))
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
      Value.Ref(pcSymbol),
      mainMatchCases,
      N,
      End()
    ))

    val lbl = blockBuilder.label(loopLbl, mainMatchBlk).rest(End())
    
    val resumedVal = VarSymbol(Tree.Ident("value$"), summon[Elaborator.State].nextUid)

    def createAssignment(sym: Local) = Assign(sym, Value.Ref(resumedVal), End())
    
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
          Value.Ref(pcSymbol),
          assignedResumedCases,
          S(End()),
          lbl
        ))
    
    val sym = BlockMemberSymbol("resume", List())
    val resumeFnDef = FunDefn(
      BlockMemberSymbol("resume", List()),
      List(ParamList(ParamListFlags.empty, List(Param(FldFlags.empty, resumedVal, N)))),
      resumeBody
    )

    // HACK: see JSBuilder:154
    val clsDef = ClassDef(
      None,
      syntax.Cls,
      cls,
      List(),
      S(List(Param(FldFlags.empty, resumedVal, N))),
      ObjBody(st.Blk(Nil, st.Lit(Tree.UnitLit(true))))
    )
    sym.defn = S(clsDef)
    
    ClsLikeDefn(
      cls,
      syntax.Cls,
      List(resumeFnDef),
      List(),
      End()
    )
    

  // Create the symbol for the continuation
  // This should only be called once because symbols contain a uid internally
  def getContClassSymbol(sym: Opt[BlockMemberSymbol]): ClassSymbol =
    ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
      Tree.Ident("Cont$" + summon[Elaborator.State].nextUid + "$" + sym.map((sym: BlockMemberSymbol) => sym.nme).getOrElse(""))
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
    if !containMarker && optimize then return body
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
      case td @ TermDefinition(_, syntax.Fun, _, _, _, S(bod), _) =>
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
        val (flds, rest2) = rest1.partitionMap:
          case LetDecl(sym: TermSymbol) => L(sym)
          case s => R(s)
        Define(ClsLikeDefn(cls.sym, syntax.Cls,
            mtds.flatMap: td =>
              td.body.map: bod =>
                val contClassSymbol = getContClassSymbol(S(td.sym))
                val (locals, bodRaw) = handlerCtx.handleFun(contClassSymbol) { returnedTerm(bod) }
                val bodTrm = instrumentBlock(contClassSymbol, bodRaw, locals, N)
                FunDefn(td.sym, td.params, bodTrm)
            ,
            flds, term(Blk(rest2, bodBlk.res))(ImplctRet).mapTail:
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
        case TermDefinition(_, _, sym, params, _, _, _) =>
          val realParams = params.head.params.dropRight(1)
          val idFuncX = VarSymbol(Tree.Ident("x"), -1)
          val idFunc = Value.Lam(Param(FldFlags.empty, idFuncX, N) :: Nil, Return(Value.Ref(idFuncX), false))
          val cont = freshTmp("cont")
          
          val mkHandler: Path => Value.Lam = (sym: Path) => Value.Lam(realParams,
            blockBuilder
              .assign(cont, instCont(Value.Lit(Tree.UnitLit(true))))
              .assignField(Value.Ref(cont), Tree.Ident("tail"), Value.Ref(cont))
              .assignField(Value.Ref(cont), Tree.Ident("handler"), Value.Ref(lhs))
              .assignField(Value.Ref(cont), Tree.Ident("handlerFun"), sym)
              .assignField(Value.Ref(cont), Tree.Ident("params"), Value.Arr(realParams.map(p => Value.Ref(p.sym))))
              .ret(Value.Ref(cont))
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
            Assign(cur, r, Break(lblBdy, false))
          ) { Assign(lhs, Instantiate(cls, handlerFuns), handlerCtx.addSavedVar(lhs){ term(st.Blk(stats, res))(r => Assign(cur, r, Break(lblBdy, false))) }) }
          
          def transformBodyBreaks(blk: Block): Block = blk match
            case Break(`lblBdy`, false) => Return(Value.Ref(cur), false)
            case _ => blk.mapChildBlocks(transformBodyBreaks)
          
          val bod = instrumentBlock(contClassSymbol, bodRaw, locals, S(transformBodyBreaks))
          
          val equalToCurVal = Call(Value.Ref(BuiltinSymbol("===", true, false, false)), Select(Value.Ref(cur), Tree.Ident("handler")) :: Value.Ref(lhs) :: Nil)
          val notEqualToSavedNext = Call(Value.Ref(BuiltinSymbol("!==", true, false, false)), Select(Value.Ref(handlerTailList), Tree.Ident("next")) :: Value.Ref(savedNext) :: Nil)
          val tailNotEmpty = Call(Value.Ref(BuiltinSymbol("!==", true, false, false)), Select(Value.Ref(handlerTailList), Tree.Ident("next")) :: Value.Lit(Tree.UnitLit(true)) :: Nil)
          handlerCtx.addSavedVars(handlerTailList :: cur :: Nil) {
            blockBuilder
              .label(lblBdy, bod)
              .separation(cur, uid)
              .assign(handlerTailList, instCont(Value.Lit(Tree.UnitLit(true)))) // just a dummy link list head
              .label(lblH, Match(
                // Value.Ref(cur),
                // Case.Cls(contSym, contTrm) ->
                // FIXME: __isCont hack
                Value.Ref(cur),
                Case.Lit(Tree.BoolLit(true)) -> Match(
                  Select(Value.Ref(cur), Tree.Ident("__isCont")),
                  Case.Lit(Tree.BoolLit(true)) ->
                    Match(
                      Select(Value.Ref(cur), Tree.Ident("handler")),
                      Case.Lit(Tree.BoolLit(true)) -> blockBuilder // BAD! we should check equality to undefined, just being lazy (and wrong) for now
                        .assign(tmp, equalToCurVal)
                        .rest(Match(
                          Value.Ref(tmp),
                          Case.Lit(Tree.BoolLit(true)) -> blockBuilder
                            // tmp2 = __resume(cur.next, tail)
                            .assign(tmp, Call(Value.Ref(resumeSym), Select(Value.Ref(cur), Tree.Ident("next")) :: Value.Ref(handlerTailList) :: Nil))
                            // .assign(resumeLocal, Call(Value.Ref(resumeSym), Select(Value.Ref(cur), Tree.Ident("next")) :: Select(Value.Ref(cur), Tree.Ident("tail")) :: Nil))
                            // _ = cur.params.push(resume)
                            .assign(tmp, Call(Select(Select(Value.Ref(cur), Tree.Ident("params")), Tree.Ident("push")), Value.Ref(tmp) :: Nil))
                            // cur = cur.handlerFun.apply(cur, cur.params)
                            .assign(savedNext, Select(Value.Ref(handlerTailList), Tree.Ident("next")))
                            .assign(cur, Call(
                              Select(Select(Value.Ref(cur), Tree.Ident("handlerFun")), Tree.Ident("apply")),
                              Value.Ref(cur) :: Select(Value.Ref(cur), Tree.Ident("params")) :: Nil
                            ))
                            // when handlerFun ends, it could be either
                            // 1. handled all effects
                            // 2. new effect raised
                            // In case 2, the handler may (if not tail call) be appended to the list wrongly, we fix it here
                            .assign(tmp, notEqualToSavedNext)
                            .chain(Match(
                              Value.Ref(tmp),
                              Case.Lit(Tree.BoolLit(true)) -> AssignField(
                                Select(Value.Ref(handlerTailList), Tree.Ident("next")),
                                Tree.Ident("next"),
                                Value.Ref(savedNext),
                                End()
                              ) :: Nil,
                              N,
                              _
                            ))
                            .continue(lblH) :: Nil, 
                          N,
                          End()
                        )) :: Nil,
                      S(handlerCtx.linkAndHandle(uid, Value.Ref(cur), tmp, getContLocalSymbol)),
                      End()
                    ) :: Nil,
                  N,
                  End()
                ) :: Nil,
                N,
                blockBuilder
                  .assign(tmp, tailNotEmpty)
                  .rest(
                    Match(
                      Value.Ref(tmp),
                      Case.Lit(Tree.BoolLit(true)) -> blockBuilder
                        // cur = __resume(handlerTail.next, handlerTail)(cur)
                        .assign(tmp, Select(Value.Ref(handlerTailList), Tree.Ident("next")))
                        .assignField(Value.Ref(handlerTailList), Tree.Ident("next"), Value.Lit(Tree.UnitLit(true)))
                        .assign(tmp, Call(Value.Ref(resumeSym), Value.Ref(tmp) :: Value.Ref(handlerTailList) :: Nil))
                        .assign(cur, Call(Value.Ref(tmp), Value.Ref(cur) :: Nil))
                        .continue(lblH)
                        :: Nil,
                      N,
                      End()
                    )
                  )
              ))
              .rest(k(Value.Ref(cur)))
          }
    case st.App(Ref(_: BuiltinSymbol), args) if optimize =>
      // Optimization: Assuming builtin symbols cannot have effect
      super.term(t)(k)
    case st.Ret(t: st.App) if handlerCtx.canPreserveTailCall() && optimize =>
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
            // Value.Ref(res),
            // Case.Cls(contSym, contTrm) -> handlerCtx.linkAndHandle(uid, Value.Ref(res)) :: Nil,
            // N,
            // Separation(res, uid, k(Value.Ref(res)))
            Value.Ref(res), // here, res is either undefined or continuation so actually only need to check against undefined
            Case.Lit(Tree.BoolLit(true)) -> Match(
              Select(Value.Ref(res), Tree.Ident("__isCont")), // TODO: __isCont hack
              Case.Lit(Tree.BoolLit(true)) -> ReturnCont(res, uid, handlerCtx.linkAndHandle(uid, Value.Ref(res), tmp, getContLocalSymbol)) :: Nil,
              N,
              End()
            ) :: Nil,
            N,
            Separation(res, uid, k(Value.Ref(res)))
          )
        )
    case st.Lam(params, body) =>
      val contClassSymbol = getContClassSymbol(N)
      val (locals, bodRaw) = handlerCtx.handleFun(contClassSymbol) { returnedTerm(body) }
      k(Value.Lam(params, instrumentBlock(contClassSymbol, bodRaw, locals, N)))
    case _ => super.term(t)(k)

  override def topLevel(t: st): Block =
    val contParamSym = VarSymbol(Tree.Ident("cont"), -1)
    val tailParamSym = VarSymbol(Tree.Ident("tail"), -1)
    val valueParamSym = VarSymbol(Tree.Ident("value"), -1)
    val contSym = freshTmp("cont")
    val valueSym = freshTmp("value")
    val lblChain = freshTmp("chainLoop")
    blockBuilder
      .define(FunDefn(resumeSym,
        ParamList(ParamListFlags.empty, Param(FldFlags.empty, contParamSym, N) :: Param(FldFlags.empty, tailParamSym, N) :: Nil) ::
          ParamList(ParamListFlags.empty, Param(FldFlags.empty, valueParamSym, N) :: Nil) :: Nil,
        blockBuilder
          .assign(contSym, Value.Ref(contParamSym))
          .assign(valueSym, Value.Ref(valueParamSym))
          .label(lblChain, blockBuilder
          .chain(Match(
              // Value.Ref(contSym),
              // Case.Cls(contSym) ->
              // FIXME: __isCont hack, here bc of undefined we omitted it
              Value.Ref(contSym),
              Case.Lit(Tree.BoolLit(true)) -> blockBuilder
                .assign(valueSym, Call(Select(Value.Ref(contSym), Tree.Ident("resume")), Value.Ref(valueSym) :: Nil))
                .chain(Match(
                  Value.Ref(valueSym),
                  Case.Lit(Tree.BoolLit(true)) -> Match(
                    Select(Value.Ref(valueSym), Tree.Ident("__isCont")),
                    Case.Lit(Tree.BoolLit(true)) -> blockBuilder
                      // An effect, __resume is called inside of handler so we need to make sure we produce what a function normally expects
                      // It should be resumed after the handler block but before all existing handler "tails"
                      .assignField(Value.Ref(valueSym), Tree.Ident("tail"), Value.Ref(tailParamSym))
                      .ret(Value.Ref(valueSym)) :: Nil,
                    N,
                    End()
                  ) :: Nil,
                  N,
                  _
                ))
                .assign(contSym, Select(Value.Ref(contSym), Tree.Ident("next")))
                .continue(lblChain) :: Nil,
              N,
              _
            ))
            .ret(Value.Ref(valueSym))
          )
          .end()
      ))
      .rest(
        removeMarkers(super.topLevel(Blk(/*effectSigDef :: */contDef :: t :: Nil, st.Lit(Tree.UnitLit(true)))))._2
      )
    