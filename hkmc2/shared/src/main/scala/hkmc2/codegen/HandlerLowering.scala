package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import semantics.Elaborator.State

import syntax.{Literal, Tree}
import semantics.*

object HandlerLowering:

  private val pcIdent: Tree.Ident = Tree.Ident("pc")
  private val nextIdent: Tree.Ident = Tree.Ident("next")
  private val tailIdent: Tree.Ident = Tree.Ident("tail")
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
    .assignFieldN(state.res.tail, nextIdent, Instantiate(state.cls, Value.Lit(Tree.IntLit(state.uid)) :: Nil))
    .assignFieldN(state.res, tailIdent, state.res.tail.next)
    .ret(state.res)
  )
  private def handlerCtx(using HandlerCtx): HandlerCtx = summon
  private val contClsPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(Tree.Ident("__Cont")).selN(Tree.Ident("class"))
  private val retClsPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(Tree.Ident("__Return")).selN(Tree.Ident("class"))
  private val handleEffectFun: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(Tree.Ident("__handleEffect"))
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
  
  object CallPlaceholder:
    private val callSymbol = freshTmp("callPlaceholder")
    def apply(res: Local, uid: StateId, canRet: Bool, c: Call, rest: Block) =
      Assign(res, SimpleCall(Value.Ref(callSymbol), List(Value.Lit(Tree.IntLit(uid)), Value.Lit(Tree.BoolLit(canRet)))), Assign(res, c, rest))
    def unapply(blk: Block) = blk match
      case Assign(res, SimpleCall(Value.Ref(`callSymbol`), List(Value.Lit(Tree.IntLit(uid)), Value.Lit(Tree.BoolLit(canRet)))), Assign(_, c: Call, rest)) =>
        Some(res, uid, canRet, c, rest)
      case _ => None
  
  private class FreshId:
    var id: Int = 0
    def apply() =
      val tmp = id
      id += 1
      tmp
  private val freshId = FreshId()
  
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
    val cls = genContClass(b)
    Define(cls, genNormalBody(b, BlockMemberSymbol(cls.sym.nme, Nil)))
  
  private def translateFun(f: FunDefn): FunDefn =
    FunDefn(f.sym, f.params, translateBlock(f.body, functionHandlerCtx))
  
  private def translateCls(cls: ClsLikeDefn): ClsLikeDefn =
    cls.copy(methods = cls.methods.map(translateFun), ctor = translateBlock(cls.ctor, functionHandlerCtx))
  
  // Handle block becomes a FunDefn and CallPlaceholder
  private def translateHandleBlock(h: HandleBlock): Block =
    val sym = BlockMemberSymbol(s"handleBlock$$${freshId()}", Nil)
    val lbl = freshTmp("handlerBody")
    val lblLoop = freshTmp("handlerLoop")
    def replaceRet(b: Block): Block = b.map(replaceRet) match
      case Return(res, implct) =>
        // In the case of res is effectful, it will be handled in translateBlock
        Assign(h.resIn, res, Return(Instantiate(retClsPath, h.resIn.asPath :: Nil), implct))
      case b => b
    val handlerBody = translateBlock(replaceRet(h.body), HandlerCtx(false, false, state => blockBuilder
      .assignFieldN(state.res.tail, nextIdent, Instantiate(state.cls, Value.Lit(Tree.IntLit(state.uid)) :: Nil))
      .assignFieldN(state.res, tailIdent, state.res.tail.next)
      .assign(h.resIn, state.res)
      .break(lbl)))
    
    def getBinaryBuiltin(nme: Str) = BuiltinSymbol(nme, true, false, false)
    val equalBuiltin = getBinaryBuiltin("===").asPath
    
    val tmp = freshTmp()
    val handlerTailList = freshTmp("handlerTailList")
    val unchanged = SimpleCall(equalBuiltin, tmp.asPath :: h.resIn.asPath :: Nil)
    val handlerLoop = blockBuilder
      .ifthen(h.resIn.asPath, Case.Cls(dummyClsSym, retClsPath), Return(h.resIn.asPath, false))
      // TODO: this should be EffectSig
      .ifthen(h.resIn.asPath, Case.Cls(dummyClsSym, contClsPath), blockBuilder
        .assign(tmp, h.resIn.asPath)
        .assign(h.resIn, SimpleCall(handleEffectFun, h.resIn.asPath :: h.lhs.asPath :: handlerTailList.asPath :: Nil))
        .assign(tmp, unchanged)
        .ifthen(tmp.asPath, Case.Lit(Tree.BoolLit(true)), rtThrowMsg("Nested effects not implemented"))
        .continue(lblLoop)
      )
      .break(lblLoop)
    val cur: Block => Block = h.handlers.foldLeft(blockBuilder)((builder, handler) =>
      val lam = Value.Lam(PlainParamList(Param(FldFlags.empty, handler.resumeSym, N) :: Nil), translateBlock(handler.body, functionHandlerCtx))
      val tmp = freshTmp()
      builder.define(FunDefn(handler.sym, handler.params, blockBuilder
        .assign(tmp, Instantiate(contClsPath, Nil))
        .assignFieldN(tmp.asPath, tailIdent, tmp.asPath)
        .assignFieldN(tmp.asPath, handlerIdent, h.lhs.asPath)
        .assignFieldN(tmp.asPath, handlerFunIdent, lam)
        .ret(tmp.asPath))))
    val body = h.handlers.foldLeft(cur)((builder, handler) => builder.assignFieldN(h.lhs.asPath, Tree.Ident(handler.sym.nme), handler.sym.asPath))
      .label(lbl, handlerBody)
      .assign(handlerTailList, Instantiate(contClsPath, Nil))
      .label(lblLoop, handlerLoop)
      .ret(h.resIn.asPath)
    // TODO: fix handler loop, resume handlerTailList in __handleEffect
    // TODO: implement special continuation class for nested effects
    val defn = FunDefn(sym, PlainParamList(Nil) :: Nil, body)
    val result = Define(defn, CallPlaceholder(h.resOut, freshId(), true, Call(sym.asPath, Nil)(true), h.rest))
    result
  
  private def genContClass(b: Block): ClsLikeDefn =
    val sym = ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
      Tree.Ident("Cont$" + State.suid.nextUid)
    )
    sym.defn = S(ClassDef(N, syntax.Cls, sym, Nil, N, ObjBody(Term.Blk(Nil, Term.Lit(Tree.UnitLit(true))))))
    def removeDefn(b: Block): Block =
      b.map(removeDefn) match
      case Define(_: (ClsLikeDefn | FunDefn), rst) => rst
      case b => b
    val actualBlock = removeDefn(b)
    // TODO: generate resume function using actualBlock
    ClsLikeDefn(sym, syntax.Cls, S(contClsPath), FunDefn(BlockMemberSymbol("resume", Nil),
      PlainParamList(Param(FldFlags.empty, VarSymbol(Tree.Ident("value$")), N) :: Nil) :: Nil, rtThrowMsg("Resume not implemented")) :: Nil, Nil, Nil, End())
  
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
    // TODO: we should skip continuation class on top level
    translateBlock(b, HandlerCtx(true, true, _ => rtThrowMsg("Unhandled effects")))
    
