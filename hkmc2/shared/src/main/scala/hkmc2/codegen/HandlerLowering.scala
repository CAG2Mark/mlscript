package hkmc2
package codegen

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.boundary
import sourcecode.{ Line, FileName, Name }

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.utils.SymbolSubst
import hkmc2.Message.MessageContext

import syntax.{Literal, Tree}
import semantics.*
import semantics.Elaborator.ctx
import semantics.Elaborator.State
import hkmc2.Config.EffectHandlers
import hkmc2.Diagnostic.Source


object HandlerLowering:

  private val pcIdent: Tree.Ident = Tree.Ident("pc")
  private val nextIdent: Tree.Ident = Tree.Ident("next")
  private val lastIdent: Tree.Ident = Tree.Ident("last")
  private val contTraceIdent: Tree.Ident = Tree.Ident("contTrace")
  private def unit = Value.Lit(Tree.UnitLit(true))
  private def intLit(i: BigInt) = Value.Lit(Tree.IntLit(i))

  private def locToStr(loc: Loc) =
    val (line, _, col) = loc.origin.fph.getLineColAt(loc.spanStart)
    Value.Lit(Tree.StrLit(s"${loc.origin.fileName.last}:${line + loc.origin.startLineNum - 1}:$col"))
  
  extension (p: Path)
    def pc = p.selN(pcIdent)
    def value = p.selN(Tree.Ident("value"))
    def next = p.selN(nextIdent)
    def last = p.selN(lastIdent)
    def contTrace = p.selN(contTraceIdent)
  
  // private case class LinkState(res: Local, cls: Path, uid: Path)
  
  type FnOrCls = Either[BlockMemberSymbol, DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol]

  private enum HandlerCtx:
    case FunctionLike(ctx: FunctionCtx)
    case Ctor
    case ModCtor(trulyNested: Bool)
    case TopLevel

    def inCtor = this === Ctor || this.isInstanceOf[ModCtor]
    def inTopLevel = this === TopLevel
    def allowDefn = inTopLevel || this.isInstanceOf[ModCtor]
    def innerDefIsTrulyNested = this match
      case FunctionLike(_) => true
      case Ctor => true
      case ModCtor(trulyNested) => trulyNested
      case TopLevel => false
    
  
  // currentFun: path to the current function for resumption
  // thisPath: path to `this` binding if the function is a method, `this` will be rebinded on resumption
  private case class FunctionCtx(currentFun: Path, thisPath: Option[Path], resumeInfo: ResumeInfo, debugInfo: DebugInfo, inGetter: Bool):
    def doUnwind(loc: Value, stateId: BigInt, restoreList: List[LocalVarSymbol])(using paths: HandlerPaths) =
      Return(Call(paths.unwindPath, (
        currentFun ::
        intLit(stateId) ::
        loc ::
        debugInfo.debugInfoPath ::
        thisPath.getOrElse(unit) ::
        resumeInfo.argLists ++:
        (intLit(restoreList.length) ::
        restoreList.map(_.asPath))
      ).map(_.asArg) ne_:: Nil)(true, true, false))
  
  // argLists: length-encoded argument list used for resumption.
  // currentLocals: All locals to be saved and reloaded, this cannot include any variables in outer scopes
  // currentStackSafetySym: The symbol to be used for stack safety
  private case class ResumeInfo(
    argLists: List[Path],
    currentLocals: List[LocalVarSymbol],
    currentStackSafetySym: FnOrCls,
  )
  
  private case class DebugInfo(
    debugNme: Str,
    debugInfoPath: Path,
  )

  object EffectfulResult:
    def unapply(r: Result)(using Config): Bool = r match
      case c: Call if c.mayRaiseEffects => true
      case _: Instantiate if config.checkInstantiateEffect => true
      case _ => false
  
  type StateId = BigInt

import HandlerLowering.*

class HandlerPaths(using Elaborator.State):
  val runtimePath: Path = State.runtimeSymbol.asPath
  val contClsPath: Path = runtimePath.selSN("FunctionContFrame").selSN("class")
  val mkEffectPath: Path = runtimePath.selSN("mkEffect")
  val handleBlockImplPath: Path = runtimePath.selSN("handleBlockImpl")
  val stackDelayClsPath: Path = runtimePath.selSN("StackDelay")
  val topLevelEffectPath: Path = runtimePath.selSN("topLevelEffect")
  val illegalEffectPath: Path = runtimePath.selSN("illegalEffect")
  val enterHandleBlockPath: Path = runtimePath.selSN("enterHandleBlock")
  val stackDepthIdent = new Tree.Ident("stackDepth")
  val stackDepthPath: Path = runtimePath.selN(stackDepthIdent)
  val fnLocalsPath: Path = runtimePath.selSN("FnLocalsInfo").selSN("class")
  val localVarInfoPath: Path = runtimePath.selSN("LocalVarInfo").selSN("class")
  val curEffect: Path = runtimePath.selSN("curEffect")
  val unwindPath: Path = runtimePath.selSN("unwind")
  val resetEffects: Path = runtimePath.selSN("resetEffects")
  val resumePc: Path = runtimePath.selSN("resumePc")
  val resumeIdx: Path = runtimePath.selSN("resumeIdx")
  val resumeValueIdent = new Tree.Ident("resumeValue")
  val resumeValue: Path = runtimePath.selN(resumeValueIdent)

type StackSafetyMap = collection.Map[FnOrCls, (Int, Block)]

class HandlerLowering(paths: HandlerPaths, opt: EffectHandlers)(using TL, Raise, Elaborator.State, Elaborator.Ctx, Config):
  
  var cpsId = 0
  
  def mapTail(b: Block)(f: BlockTail => Block): Block = b match
    case b: BlockTail => f(b)
    case Match(scrut, arms, dflt, rest) => Match(scrut, arms, dflt, mapTail(rest)(f))
    case Label(label, loop, body, rest) => Label(label, loop, body, mapTail(rest)(f))
    case Scoped(syms, body) => Scoped(syms, mapTail(body)(f))
    case Begin(sub, rest) => Begin(sub, mapTail(rest)(f))
    case TryBlock(sub, finallyDo, rest) => TryBlock(sub, finallyDo, mapTail(rest)(f))
    case Assign(lhs, rhs, rest) => Assign(lhs, rhs, mapTail(rest)(f))
    case a @ AssignField(lhs, field, res, rest) => AssignField(lhs, field, res, mapTail(rest)(f))(a.symbol)
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) => AssignDynField(lhs, fld, arrayIdx, rhs, mapTail(rest)(f))
    case Define(defn, rest) => Define(defn, mapTail(rest)(f))
  
  
  def blockNormalizer = new BlockTransformer(SymbolSubst()):
    val thunks: mutable.Map[LabelSymbol, () => FunDefn] = mutable.Map.empty
    override def applyBlock(b: Block): Block = b match
      case m @ Match(scrut, arms, dflt, rest) =>
        var used = false
        val (dfn, blk) = createNestedFn("rest", PlainParamList(Nil), applyBlock(rest), true)
        def rewriteTail(arm: Block) = mapTail(arm):
          case End(_) =>
            used = true
            Return(Call(dfn.asPath, Nil ne_:: Nil)(true, false, false))
          case arm => arm
        val newArms = arms.mapConserve:
          case (c, b_) => (c, applyBlock(rewriteTail(b_)))
        val newDflt = dflt.mapConserve(b_ => applyBlock(rewriteTail(b_)))
        // Match(scrut, arms, dflt, rest)
        val ret = Match(scrut, newArms, newDflt, End())
        if used then
          blk(ret)
        else ret
      
      case b @ Begin(sub, rest) =>
        if sub.isAbortive || rest.isEmpty then applyBlock(sub)
        var good = false
        val mapped = mapTail(sub):
          case End(_) =>
            good = true
            rest
          case b => b
        
        if good then applyBlock(mapped)
        else
          val (dfn, blk) = createNestedFn("rest", PlainParamList(Nil), applyBlock(rest), true)
          def rewriteTail(arm: Block) = mapTail(arm):
            case End(_) => Return(Call(dfn.asPath, Nil ne_:: Nil)(true, false, false))
            case arm => arm
          Begin(blk(applyBlock(rewriteTail(sub))), End())
      
      case Label(label, loop, body, rest) =>
        if !loop then
          var used = false
          val (dfn, blk) = createNestedFn("rest", PlainParamList(Nil), applyBlock(rest), true)
          def rewriteTail(arm: Block) = mapTail(arm):
            case End(_) => Return(Call(dfn.asPath, Nil ne_:: Nil)(true, false, false))
            case arm => arm
          thunks.addOne(label, () =>
            used = true
            dfn
          )
          val res = applyBlock(body)
          if used then blk(res) else res
        else
          ???
      case Break(label) =>
        Return(Call(thunks(label)().asPath, Nil ne_:: Nil)(true, false, false))
      case Continue(label) => ???
      
      
      case _ => super.applyBlock(b)
  
  val cpsTransformer = new BlockTransformer(SymbolSubst()):
    
    var curContPath: Path = State.runtimeSymbol.asPath.selN(Tree.Ident("cpsId"))
    var isTopLevel = true
    
    def applyCpsOnFun(b: Block, contPath: Path): Block =
      val saved = curContPath
      val savedTopLevel = isTopLevel
      curContPath = contPath
      isTopLevel = false
      val ret = applyScopedBlock(b)
      curContPath = saved
      isTopLevel = savedTopLevel
      ret
    
    override def applyFunDefn(fun: FunDefn): FunDefn =
      if fun.params.size != 1 then
        raise(WarningReport(
          msg"This function is not CPS-transformed because it has more than one parameter list." -> fun.dSym.toLoc :: Nil,
          source = Source.Compilation))
        super.applyFunDefn(fun)
      else
        val contSym = VarSymbol(Tree.Ident("k"))
        val ogParams = fun.params.head
        fun.copy(
          params = ogParams.copy(params = Param.simple(contSym) :: ogParams.params) :: Nil,
          body = applyCpsOnFun(fun.body, contSym.asPath)
        )(fun.configOverride, fun.annotations)
    
    def checkCall(c: Call) =
      println(c.fun)
      if c.argss.size != 1 then
        raise(WarningReport(
          msg"This call is not CPS-transformed because it has more than one argument list." -> c.toLoc :: Nil,
          source = Source.Compilation))
        false
      else
        c.fun match
          case Select(Value.MemberRef(bms, disamb), _) if bms.nme === "Predef" => false
          case Select(Value.This(inner), _) if inner.nme == "globalThis" => false
          case _ => true
        
    
    override def applyPath(p: Path)(k: Path => Block): Block = p match
      case Value.RefLike(Elaborator.ctx.builtins.runtime.handle_suspension) =>
        k(State.runtimeSymbol.asPath.selN(Tree.Ident("cpsHandlerImpl")))
      case _ => super.applyPath(p)(k)
    
    override def applyResult(r: Result)(k: Result => Block): Block = r match
      case c @ Call(Value.RefLike(Elaborator.ctx.builtins.runtime.suspend), (tag :: handlerFun :: Nil) :: Nil) =>
        val paramSym = VarSymbol(Tree.Ident("retVal"))
        val pList = PlainParamList.simple(paramSym :: Nil)
        val bod = k(paramSym.asPath)
        val (cpsCont, rest) = createNestedFn("cpsCont$" + cpsId, pList, bod)
        cpsId += 1
        val call = Instantiate(
          true,
          State.runtimeSymbol.asPath.selN(Tree.Ident("Suspend")),
          (cpsCont.asPath.asArg :: tag :: handlerFun :: Nil) ne_:: Nil)
        rest(Return(call))
      // case c @ Call(Value.RefLike(Elaborator.ctx.builtins.runtime.handle_suspension), (tag :: bodyFun :: Nil) :: Nil) =>
      case c @ Call(path, args) if c.mayRaiseEffects =>
        if !checkCall(c) then
          super.applyResult(r)(k)
        else
          val paramSym = VarSymbol(Tree.Ident("retVal"))
          val pList = PlainParamList.simple(paramSym :: Nil)
          val bod = k(paramSym.asPath)
          val (cpsCont, rest) = createNestedFn("cpsCont$" + cpsId, pList, bod)
          cpsId += 1
          applyPath(path): path =>
            val call = Call(path, (cpsCont.asPath.asArg :: args.head) ne_:: Nil)(true, false, false)
            rest(Return(call))
      case _ => super.applyResult(r)(k)
    
    def retResult(r: Result) =
      val (pth, rst) = r match
        case p: Path => (p, id)
        case _ =>
          val tmp = TempSymbol(N)
          (tmp.asPath, blockBuilder.assignScoped(tmp, r))
      rst.ret(Call(curContPath, (pth.asArg :: Nil) ne_:: Nil)(true, false, false))
    
    override def applyBlock(b: Block): Block = b match
      case Return(Call(Value.RefLike(Elaborator.ctx.builtins.runtime.suspend), args :: Nil)) =>
        Return(Instantiate(
          true,
          State.runtimeSymbol.asPath.selN(Tree.Ident("Suspend")),
          (curContPath.asArg :: args) ne_:: Nil))
      case Return(c: Call) if c.mayRaiseEffects =>
        if !checkCall(c) then
          retResult(c)
        else
          Return(Call(c.fun, (curContPath.asArg :: c.argss.head) ne_:: Nil)(true, false, false))
      case Return(r: Result) => retResult(r)
      case _: Label => lastWords("undesugared label")
      case b: Begin =>
        if !b.rest.isEmpty then
          lastWords("non-empty begin rest")
        super.applyBlock(b)
      case t: TryBlock => lastWords("unsupported")
      case m: Match =>
        if !m.rest.isEmpty then
          lastWords("non-empty match rest")
        super.applyBlock(b)
      case _ => super.applyBlock(b)
  
  def translateTopLevel(b: Block): (Block, StackSafetyMap) =
    (cpsTransformer.applyBlock(blockNormalizer.applyBlock(b)), Map.empty)
    // (blockNormalizer.applyBlock(b), Map.empty)
