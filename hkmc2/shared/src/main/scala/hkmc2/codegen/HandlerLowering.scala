package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import semantics.Elaborator.State

import syntax.{Literal, Tree, ParamBind}
import semantics.*
import scala.annotation.tailrec

object HandlerLowering:

  private val pcIdent: Tree.Ident = Tree.Ident("pc")
  private val nextIdent: Tree.Ident = Tree.Ident("next")
  private val tailIdent: Tree.Ident = Tree.Ident("tail")
  private val nextHandlerIdent: Tree.Ident = Tree.Ident("nextHandler")
  private val tailHandlerIdent: Tree.Ident = Tree.Ident("tailHandler")
  private val handlerIdent: Tree.Ident = Tree.Ident("handler")
  private val handlerFunIdent: Tree.Ident = Tree.Ident("handlerFun")

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
    def next = p.selN(nextIdent)
    def tail = p.selN(tailIdent)
    def nextHandler = p.selN(nextHandlerIdent)
    def tailHandler = p.selN(tailHandlerIdent)
    def value = p.selN(Tree.Ident("value"))
    def asArg = Arg(false, p)
  
  extension (l: Local)
    def asPath: Path = Value.Ref(l)
  
  private case class LinkState(res: Path, cls: Path, uid: StateId)
  
  private case class HandlerCtx(isHandleFree: Bool, isTopLevel: Bool, linkAndHandle: LinkState => Block)
  
  type StateId = BigInt

import HandlerLowering.*

class HandlerLowering(using TL, Raise, Elaborator.State):

  private val functionHandlerCtx = HandlerCtx(true, false, state =>
    val tmp = freshTmp()
    blockBuilder
    .assignFieldN(state.res.tail, nextIdent, Instantiate(state.cls.selN(Tree.Ident("class")), Value.Lit(Tree.IntLit(state.uid)) :: Nil))
    .assignFieldN(state.res, tailIdent, state.res.tail.next)
    .ret(state.res)
  )
  private def handlerCtx(using HandlerCtx): HandlerCtx = summon
  private val contClsPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(Tree.Ident("__Cont")).selN(Tree.Ident("class"))
  private val retClsPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(Tree.Ident("__Return")).selN(Tree.Ident("class"))
  private val handleEffectFun: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(Tree.Ident("__handleEffect"))
  private val mkEffectPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(Tree.Ident("__mkEffect"))
  private val handleBlockImplPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(Tree.Ident("__handleBlockImpl"))
  private val mapPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Map"))
  private val dummyClsSym = ClassSymbol(
    Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
    Tree.Ident("Dummy")
  )
  
  private def freshTmp(dbgNme: Str = "tmp") = new TempSymbol(N, dbgNme)
  
  private def rtThrowMsg(msg: Str) = Throw(
    Instantiate(State.globalThisSymbol.asPath.selN(Tree.Ident("Error")),
    Value.Lit(Tree.StrLit(msg)) :: Nil)
  )
  
  object SimpleCall:
    def apply(fun: Path, args: List[Path]) = Call(fun, args.map(Arg(false, _)))(true)
    def unapply(res: Result) = res match
      case Call(fun, args) => args.foldRight[Opt[List[Path]]](S(Nil))((arg, acc) => acc.flatMap(acc => arg match
        case Arg(false, p) => S(p :: acc)
        case _ => N
      )).map((fun, _))
      case _ => N
  
  object ResumptionPoint:
    private val resumptionSymbol = freshTmp("resumptionPoint")
    def apply(res: Local, uid: StateId, rest: Block) =
      Assign(res, SimpleCall(Value.Ref(resumptionSymbol), List(Value.Lit(Tree.IntLit(uid)))), rest)
    def unapply(blk: Block) = blk match
      case Assign(res, SimpleCall(Value.Ref(`resumptionSymbol`), List(Value.Lit(Tree.IntLit(uid)))), rest) =>
        Some(res, uid, rest)
      case _ => None
  
  object ReturnCont:
    private val returnContSymbol = freshTmp("returnCont")
    def apply(res: Local, uid: StateId) =
      Assign(res, SimpleCall(Value.Ref(returnContSymbol), List(Value.Lit(Tree.IntLit(uid)))), End(""))
    def unapply(blk: Block) = blk match
      case Assign(res, SimpleCall(Value.Ref(`returnContSymbol`), List(Value.Lit(Tree.IntLit(uid)))), _) => 
        Some(res, uid)
      case _ => None
  
  object CallPlaceholder:
    private val callSymbol = freshTmp("callPlaceholder")
    def apply(res: Local, uid: StateId, canRet: Bool, c: Call, rest: Block) =
      Assign(res, SimpleCall(Value.Ref(callSymbol), List(Value.Lit(Tree.IntLit(uid)), Value.Lit(Tree.BoolLit(canRet)))), Assign(res, c, rest))
    def unapply(blk: Block) = blk match
      case Assign(res, SimpleCall(Value.Ref(`callSymbol`), List(Value.Lit(Tree.IntLit(uid)), Value.Lit(Tree.BoolLit(canRet)))), Assign(_, c: Call, rest)) =>
        Some(res, uid, canRet, c, rest)
      case _ => None
  
  object StateTransition:
    private val transitionSymbol = freshTmp("transition")
    def apply(uid: StateId) = Return(SimpleCall(Value.Ref(transitionSymbol), List(Value.Lit(Tree.IntLit(uid)))), false)
    def unapply(blk: Block) = blk match
      case Return(SimpleCall(Value.Ref(`transitionSymbol`), List(Value.Lit(Tree.IntLit(uid)))), false) =>
        S(uid)
      case _ => N
  
  object FnEnd:
    private val fnEndSymbol = freshTmp("fnEnd")
    def apply() = Return(SimpleCall(Value.Ref(fnEndSymbol), Nil), false)
    def unapply(blk: Block) = blk match
      case Return(SimpleCall(Value.Ref(`fnEndSymbol`), Nil), false) => true
      case _ => false
  
  private class FreshId:
    var id: Int = 0
    def apply() =
      val tmp = id
      id += 1
      tmp
  private val freshId = FreshId()
  
  // id: the id of the current state
  // blk: the block of code within this state
  // sym: the variable to which the resumed value should set
  class BlockState(val id: StateId, val blk: Block, val sym: Opt[Local])
  
  def partitionBlock(blk: Block, labelIds: Map[Symbol, (StateId, StateId)] = Map.empty): Ls[BlockState] = 
    // for readability :)
    case class PartRet(head: Block, states: Ls[BlockState])

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
      case _: HandleBlock | _: HandleBlockReturn => die // already translated at this point
    
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
      case ResumptionPoint(result, uid, rest) =>
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
        PartRet(blk.map(_ => head), parts)
      case Return(_, _) => PartRet(blk, Nil)
      // ignored cases
      case TryBlock(sub, finallyDo, rest) => ??? // ignore
      case Throw(_) => PartRet(blk, Nil)
      case _: HandleBlock | _: HandleBlockReturn => die // already translated at this point

    val headId = freshId()

    val result = go(blk)(using labelIds, N)
    BlockState(headId, result.head, N) :: result.states
  
  /**
   * The actual translation:
   * 1. add call markers, transform class, function, lambda and sub handler blocks
   * 2.
   * a) generate continuation class
   * b) generate normal function body
   */
  
  private def translateBlock(b: Block, h: HandlerCtx): Block =
    given HandlerCtx = h
    val stage1 = firstPass(b)
    secondPass(stage1)
  
  private def firstPass(b: Block)(using HandlerCtx): Block =
    b.map(firstPass) match
      case b: HandleBlock => translateHandleBlock(b)
      case b => b.mapValue {
        case Value.Lam(params, body) => Value.Lam(params, translateBlock(body, functionHandlerCtx))
        case v => v
      } match {
        case Return(c: Call, implct) if handlerCtx.isHandleFree => Return(c, implct)
        case b => b.mapResult {
          case r @ Call(Value.Ref(_: BuiltinSymbol), _) => N
          case c: Call =>
            val res = freshTmp("res")
            S(k => CallPlaceholder(res, freshId(), false, c, k(Value.Ref(res))))
          case r => N
        }
      } match
        case Define(f: FunDefn, rst) => Define(translateFun(f), rst)
        case Define(c: ClsLikeDefn, rst) => Define(translateCls(c), rst)
        case b => b
  
  private def secondPass(b: Block)(using HandlerCtx): Block =
    val cls = if handlerCtx.isTopLevel then N else genContClass(b)
    cls match
      case None => genNormalBody(b, BlockMemberSymbol("", Nil))
      case Some(cls) => Define(cls, genNormalBody(b, BlockMemberSymbol(cls.sym.nme, Nil)))
  
  private def translateFun(f: FunDefn): FunDefn =
    FunDefn(f.sym, f.params, translateBlock(f.body, functionHandlerCtx))
  
  private def translateCls(cls: ClsLikeDefn): ClsLikeDefn =
    cls.copy(methods = cls.methods.map(translateFun), ctor = translateBlock(cls.ctor, functionHandlerCtx))
  
  // Handle block becomes a FunDefn and CallPlaceholder
  private def translateHandleBlock(h: HandleBlock): Block =
    val sym = BlockMemberSymbol(s"handleBlock$$${freshId()}", Nil)
    val lbl = freshTmp("handlerBody")
    val lblLoop = freshTmp("handlerLoop")
    val tmp = freshTmp("retCont")
    def prepareBody(b: Block): Block =
      def go(b: Block): Block =
        b.map(go) match
        case Return(res, implct) =>
          // In the case of res is effectful, it will be handled in translateBlock
          Assign(tmp, res, Return(Instantiate(retClsPath, tmp.asPath :: Nil), implct))
        case HandleBlockReturn(res) =>
          Return(res, false)
        case b => b
      go(b)
    val handlerBody = translateBlock(prepareBody(h.body), HandlerCtx(false, false, state => blockBuilder
      .assignFieldN(state.res.tail, nextIdent, Instantiate(state.cls, Value.Lit(Tree.IntLit(state.uid)) :: Nil))
      .assignFieldN(state.res, tailIdent, state.res.tail.next)
      .ret(SimpleCall(handleBlockImplPath, state.res :: h.lhs.asPath :: Nil))))
    
    val cur: Block => Block = h.handlers.foldLeft(blockBuilder)((builder, handler) =>
      val lam = Value.Lam(PlainParamList(Param(FldFlags.empty, handler.resumeSym, N) :: Nil), translateBlock(handler.body, functionHandlerCtx))
      val tmp = freshTmp()
      builder.define(FunDefn(handler.sym, handler.params, Return(SimpleCall(mkEffectPath, h.lhs.asPath :: lam :: Nil), false)))).assign(h.lhs, Instantiate(h.cls, Nil))
    val body = h.handlers.foldLeft(cur)((builder, handler) => builder.assignFieldN(h.lhs.asPath, Tree.Ident(handler.sym.nme), handler.sym.asPath)).rest(handlerBody)
    val defn = FunDefn(sym, PlainParamList(Nil) :: Nil, body)
    val result = Define(defn, CallPlaceholder(h.res, freshId(), true, Call(sym.asPath, Nil)(true), h.rest))
    result
  
  private def genContClass(b: Block)(using HandlerCtx): Opt[ClsLikeDefn] =
    val sym = ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
      Tree.Ident("Cont$" + State.suid.nextUid)
    )
    val pcVar = VarSymbol(Tree.Ident("pc"))
    sym.defn = S(ClassDef(N, syntax.Cls, sym, Nil, S(PlainParamList(Param(FldFlags.empty, pcVar, N) :: Nil)), ObjBody(Term.Blk(Nil, Term.Lit(Tree.UnitLit(true))))))
    
    var trivial = true
    def prepareBlock(b: Block): Block =
      b.map(prepareBlock) match
      case Define(_: (ClsLikeDefn | FunDefn), rst) => rst
      case CallPlaceholder(res, uid, canRet, c, rest) =>
        trivial = false
        blockBuilder
        .assign(res, c)
        .ifthen(
          res.asPath,
          Case.Cls(dummyClsSym, contClsPath),
          ReturnCont(res, uid)
        )
        .staticif(canRet, _.ifthen(
          res.asPath,
          Case.Cls(dummyClsSym, retClsPath),
          blockBuilder.ret(if handlerCtx.isHandleFree then res.asPath.value else res.asPath)
        ))
        .rest(ResumptionPoint(res, uid, rest))
      case b => b
    val actualBlock = prepareBlock(b)
    if trivial then return N
    
    val parts = partitionBlock(actualBlock)
    val loopLbl = freshTmp("contLoop")
    val pcSymbol = TermSymbol(ParamBind, S(sym), pcIdent)
    
    def transformPart(blk: Block): Block = 
      def f(blk: Block): Block = blk match
        case ReturnCont(res, uid) =>
          blockBuilder
            .assignFieldN(res.asPath.tail, nextIdent, sym.asPath)
            .assign(pcSymbol, Value.Lit(Tree.IntLit(uid)))
            .ret(res.asPath)
        case StateTransition(uid) =>
          blockBuilder
            .assign(pcSymbol, Value.Lit(Tree.IntLit(uid)))
            .continue(loopLbl)
        case FnEnd() =>
          blockBuilder.break(loopLbl)
        case c => c.map(f)
      f(blk)

    // match block representing the function body
    val mainMatchCases = parts.toList.map(b => (Case.Lit(Tree.IntLit(b.id)), transformPart(b.blk)))
    val mainMatchBlk = Match(
      pcSymbol.asPath,
      mainMatchCases,
      N,
      End()
    )

    val lbl = blockBuilder.label(loopLbl, mainMatchBlk).rest(End())
    
    val resumedVal = VarSymbol(Tree.Ident("value$"))

    def createAssignment(sym: Local) = Assign(sym, resumedVal.asPath, End())
    
    val assignedResumedCases = for 
      b   <- parts
      sym <- b.sym
    yield Case.Lit(Tree.IntLit(b.id)) -> createAssignment(sym) // NOTE: assume sym is in localsMap

    // assigns the resumed value
    val resumeBody = 
      if assignedResumedCases.isEmpty then
        lbl
      else
        Match(
          pcSymbol.asPath,
          assignedResumedCases,
          N,
          lbl
        )
    
    val resumeSym = BlockMemberSymbol("resume", List())
    val resumeFnDef = FunDefn(
      resumeSym,
      List(PlainParamList(List(Param(FldFlags.empty, resumedVal, N)))),
      resumeBody
    )
    
    S(ClsLikeDefn(sym, syntax.Cls, S(contClsPath), resumeFnDef :: Nil, Nil, Nil,
      Assign(freshTmp(), SimpleCall(Value.Ref(State.builtinOpsMap("super")), Value.Lit(Tree.UnitLit(true)) :: Value.Lit(Tree.UnitLit(true)) :: Nil), End()), End()))
  
  private def genNormalBody(b: Block, clsSym: BlockMemberSymbol)(using HandlerCtx): Block =
    val tmp = freshTmp("cont")
    b.map(genNormalBody(_, clsSym)) match
    case CallPlaceholder(res, uid, canRet, c, rest) =>
      blockBuilder
      .assign(res, c)
      .ifthen(
        res.asPath,
        Case.Cls(dummyClsSym, contClsPath),
        handlerCtx.linkAndHandle(LinkState(res.asPath, clsSym.asPath, uid))
      )
      .staticif(canRet && !handlerCtx.isTopLevel, _.ifthen(
        res.asPath,
        Case.Cls(dummyClsSym, retClsPath),
        blockBuilder.ret(if handlerCtx.isHandleFree then res.asPath.value else res.asPath)
      ))
      .rest(rest)
    case b => b

  def translateTopLevel(b: Block): Block =
    translateBlock(b, HandlerCtx(true, true, _ => rtThrowMsg("Unhandled effects")))
    
