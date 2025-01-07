package hkmc2

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.Elaborator.State
import hkmc2.semantics.*
import hkmc2.syntax.Tree


class StackSafeTransform(depthLimit: Int)(using State):
  extension (l: Local)
    def asPath: Path = Value.Ref(l)
  extension (p: Path)
    def selN(id: Tree.Ident) = Select(p, id)(N)
    def asArg = Arg(false, p)

  private val STACK_DEPTH_IDENT: Tree.Ident = Tree.Ident("__stackDepth")
  private val STACK_HANDLER_IDENT: Tree.Ident = Tree.Ident("__stackHandler")

  private val stackDelayClsPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(Tree.Ident("__StackDelay")).selN(Tree.Ident("class"))
  private val stackDepthPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(STACK_DEPTH_IDENT)
  private val stackHandlerPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef")).selN(STACK_HANDLER_IDENT)
  private val predefPath: Path = State.globalThisSymbol.asPath.selN(Tree.Ident("Predef"))

  private def intLit(n: BigInt) = Value.Lit(Tree.IntLit(n))
  
  private def op(op: String, a: Path, b: Path) =
    Call(State.builtinOpsMap(op).asPath, List(a.asArg, b.asArg))(true)

  // TODO: this code is copied from HandlerLowering and is quite useful. Maybe refactor it into a utils file
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

  // Increases the stack depth, assigns the call to a value, then decreases the stack depth
  // then binds that value to a desired block
  def extractRes(res: Result, f: Result => Block) =
    res match
      case c: Call if c.isMlsFun => 
        val tmp = TempSymbol(None, "tmp")
        val depthPositive = TempSymbol(None, "depthPositive")
        blockBuilder
          .assignFieldN(predefPath, STACK_DEPTH_IDENT, op("+", stackDepthPath, intLit(1)))
          .assign(tmp, res)
          .assign(depthPositive, op(">", stackDepthPath, intLit(0)))
          .ifthen( // only reduce stack depth if it's positive, since the stack depth is reset after the stack is unwound
            depthPositive.asPath, Case.Lit(Tree.BoolLit(true)),
            blockBuilder
              .assignFieldN(predefPath, STACK_DEPTH_IDENT, op("-", stackDepthPath, intLit(1)))
              .end()
            )
          .rest(f(tmp.asPath))
      case _ => f(res)

  // Rewrites anything that can contain a Call to increase the stack depth
  def transform(b: Block): Block = b match
    case Return(res, implct) => extractRes(res, Return(_, false))
    case Assign(lhs, rhs, rest) => extractRes(rhs, Assign(lhs, _, transform(rest)))
    case b @ AssignField(lhs, nme, rhs, rest) => extractRes(rhs, AssignField(lhs, nme, _, transform(rest))(b.symbol))
    case Define(defn, rest) => Define(rewriteDefn(defn), transform(rest))
    case HandleBlock(lhs, res, par, cls, handlers, body, rest) =>
      HandleBlock(
        lhs, res, par, cls, handlers.map(h => Handler(h.sym, h.resumeSym, h.params, transform(h.body))),
        transform(body), transform(rest)
      )
    case HandleBlockReturn(res) => extractRes(res, HandleBlockReturn(_))
    case _ => b.map(transform)
  
  // TODO: this will just some simple analysis. some more in-depth analysis could be done at some other point
  def isTrivial(b: Block): Boolean = b match
    case Match(scrut, arms, dflt, rest) => 
      arms.foldLeft(dflt.map(isTrivial).getOrElse(true))((acc, bl) => acc && isTrivial(bl._2)) && isTrivial(rest)
    case Return(res, implct) => true
    case Throw(exc) => ???
    case Label(label, body, rest) => ???
    case Break(label) => ???
    case Continue(label) => ???
    case Begin(sub, rest) => ???
    case TryBlock(sub, finallyDo, rest) => ???
    case Assign(lhs, rhs, rest) => ???
    case AssignField(lhs, nme, rhs, rest) => ???
    case Define(defn, rest) => ???
    case HandleBlock(lhs, res, par, cls, handlers, body, rest) => ???
    case HandleBlockReturn(res) => ???
    case End(msg) => ???

  def rewriteDefn(defn: Defn) = defn match
    case d: FunDefn => rewriteFn(d)
    case _: ValDefn => defn
    case ClsLikeDefn(sym, k, parentPath, methods, privateFields, publicFields, preCtor, ctor) =>
      ClsLikeDefn(
        sym, k, parentPath, methods.map(rewriteFn), privateFields, publicFields,
        rewriteBlk(preCtor), rewriteBlk(ctor) // TODO: do we need to rewrite the preCtor?
      )

  def rewriteBlk(blk: Block) =
    val scrut1Sym = TempSymbol(None, "scrut1")
    val scrut2Sym = TempSymbol(None, "scrut2")
    val scrutSym = TempSymbol(None, "scrut")
    val scrut1 = op(">=", stackDepthPath, intLit(depthLimit))
    val scrut2 = op("!==", stackHandlerPath, Value.Lit(Tree.UnitLit(false)))
    val scrutVal = op("&&", scrut1Sym.asPath, scrut2Sym.asPath)

    val newBody = transform(blk)

    blockBuilder
      .assign(scrut1Sym, scrut1) // stackDepth >= depthLimit
      .assign(scrut2Sym, scrut2) // stackHandler !== null
      .assign(scrutSym, scrutVal) // stackDepth >= depthLimit && stackHandler !== null
      .ifthen(
        scrutSym.asPath, Case.Lit(Tree.BoolLit(true)), 
        blockBuilder.assign( // tmp = perform(undefined)
          TempSymbol(None, "tmp"), 
          Call(Select(stackHandlerPath, Tree.Ident("perform"))(N), Nil)(true)).end())
      .rest(newBody)
     
  def rewriteFn(defn: FunDefn) = FunDefn(defn.sym, defn.params, rewriteBlk(defn.body))

  def transformTopLevel(b: Block) =
    def replaceReturns(b: Block): Block = b match
      case Return(res, false) => HandleBlockReturn(res)
      case _ => b.map(replaceReturns)
    
    // symbols
    val resumeSym = VarSymbol(Tree.Ident("resume"))
    val handlerSym = TempSymbol(None, "stackHandler");
    val resSym = TempSymbol(None, "res");
    val clsSym = ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
      Tree.Ident("StackDelay$")
    )
    clsSym.defn = S(ClassDef(N, syntax.Cls, clsSym, Nil, N, ObjBody(Term.Blk(Nil, Term.Lit(Tree.UnitLit(true))))))

    val (blk, defns) = b.floatOutDefns(true)

    // the global stack handler is created here
    val handle = HandleBlock(
      handlerSym, resSym,
      stackDelayClsPath, clsSym,
      List(Handler(
        BlockMemberSymbol("perform", Nil), resumeSym, List(ParamList(ParamListFlags.empty, Nil, N)),
        blockBuilder
          .assignFieldN(predefPath, STACK_DEPTH_IDENT, intLit(0)) // Q: should this be 0 or 1 to account for some overhead?
          .ret(Call(Value.Ref(resumeSym), List())(true))
      )), // create a "unit" handler, i.e. fun perform(k) = k(())
      blockBuilder
        .assignFieldN(predefPath, STACK_DEPTH_IDENT, intLit(0)) // set stackDepth = 0
        .assignFieldN(predefPath, STACK_HANDLER_IDENT, handlerSym.asPath) // assign stack handler
        .rest(replaceReturns(transform(blk))), // transform the rest of the body
      blockBuilder // reset the stack safety values
        .assignFieldN(predefPath, STACK_DEPTH_IDENT, intLit(0)) // set stackDepth = 0
        .assignFieldN(predefPath, STACK_HANDLER_IDENT, Value.Lit(Tree.UnitLit(false))) // set stackHandler = null
        .rest(Return(Value.Ref(resSym), true))
    )

    defns.foldLeft[Block](handle)((blk, defn) => Define(rewriteDefn(defn), blk))