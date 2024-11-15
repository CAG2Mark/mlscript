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

object InstrLowering:
  private class HandlerCtx:
    var handlers: List[Path => Block] = Nil
    var toSave: List[Set[Local]] = Set.empty :: Nil
    // The callee should pass the appended continuation as the handler has no way of knowing what should be saved
    def jumpToHandler(res: Path): Block =
      handlers match
        case Nil => Throw(
          Instantiate(Select(Value.Ref(Elaborator.Ctx.globalThisSymbol), Tree.Ident("Error")),
          Value.Lit(Tree.StrLit("Unhandled effects")) :: Nil)
        )
        case h :: _ => h(res)
    def addVar(l: Local) =
      toSave = toSave.head + l :: toSave.tail
    def handleScoped(handler: Path => Block)(scope: => Block): (Set[Local], Block) =
      handlers ::= handler
      toSave ::= Set.empty
      val result = scope
      val locals = toSave.head
      toSave = toSave.tail
      handlers = handlers.tail
      (locals, result)
    def handleFun(scope: => Block): (Set[Local], Block) =
      handleScoped(Return(_, false))(scope)
import InstrLowering.*

class InstrLowering(using TL, Raise, Elaborator.State) extends Lowering:

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
    N,
    syntax.Cls,
    contSym,
    Nil,
    S(("resume" :: "resumed" :: "next" :: Nil).map(name =>
      Param(FldFlags.empty, TermSymbol(ParamBind, S(contSym), Tree.Ident(name)), None)
    )),
    ObjBody(st.Blk(Nil, st.Lit(Tree.UnitLit(true)))))
  private val contTrm = Select(Select(Value.Ref(Elaborator.Ctx.globalThisSymbol), contIdent), Tree.Ident("class"))
  contSym.defn = S(contDef)
  
  private def instCont(resume: Path): Result =
    Instantiate(contTrm, resume :: Value.Lit(Tree.BoolLit(false)) :: Value.Lit(Tree.UnitLit(true)) :: Nil)
  
  extension (k: Block => Block)
    def assign(l: Local, r: Result): Block => Block = b => k(Assign(l, r, b))
    def assignField(lhs: Path, nme: Tree.Ident, rhs: Result): Block => Block = b => k(AssignField(lhs, nme, rhs, b))
    def break(l: Local): Block = k(Break(l, false))
    def continue(l: Local): Block = k(Break(l, true))
    def label(label: Local, body: Block): Block => Block = b => k(Label(label, body, b))
    def ret(r: Result, implct: Bool): Block = k(Return(r, implct))
    def rest(b: Block): Block = k(b)
  private def blockBuilder: Block => Block = identity
  
  private val handlerCtx = HandlerCtx()

  private def freshTmp(dbgNme: Str = "tmp") = new TempSymbol(summon[Elaborator.State].nextUid, N, dbgNme)
  // special function denoting state transitions, transitionFn should never appear in the real output
  private val transitionSymbol = freshTmp()
  private val separationSymbol = freshTmp("separator")
  private class FreshId:
    var id: BigInt = 0
    def apply() =
      val tmp = id
      id += 1
      tmp
  private val freshId = FreshId()

  // id: the id of the current state
  // blk: the block of code within this state
  class BlockState(id: BigInt, blk: Block)

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
  def partitionBlock(blk: Block): Ls[BlockState] = 
    // for readability :)
    case class PartRet(head: Block, states: Ls[BlockState])

    // Note: can construct StateTransition and pattern match on it as if it were a case class
    object StateTransition:
      def apply(uid: BigInt) = Return(Call(Value.Ref(transitionSymbol), List(Value.Lit(Tree.IntLit(uid)))), false)
      def unapply(blk: Block) = blk match
        case Return(Call(Value.Ref(sym), List(Value.Lit(Tree.IntLit(uid)))), false) if sym == transitionSymbol =>
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
    // TODO: replace Call pattern with special EffectfulCall pattern when Anson adds that
    // TODO: don't split within Labels when not needed, ideally keep it intact. Need careful analysis for this
    // blk: The block to transform
    // labelIds: maps label IDs to the state at the start of the label and the state after the label
    // jumpTo: what state End should jump to, if at all 
    // freshState: uid generator
    def go(blk: Block)(implicit labelIds: Map[Symbol, (BigInt, BigInt)], afterEnd: Option[BigInt]): PartRet = blk match
      case Match(scrut, arms, dflt, rest) => 
        val restParts = go(rest)
        // TODO: If restParts is a StateTransition, we can avoid creating a new state here
        val restId = freshId()
        
        val armsParts = arms.map((cse, blkk) => (cse, go(blkk)(afterEnd = S(restId))))
        val dfltParts = dflt.map(blkk => go(blkk)(afterEnd = S(restId)))
        

        val states_ = restParts.states ::: armsParts.flatMap(_._2.states)
        val states = dfltParts match
          case N => states_
          case S(value) => value.states ::: states_

        val newArms = armsParts.map((cse, partRet) => (cse, partRet.head))
        
        PartRet(
          Match(scrut, newArms, dfltParts.map(_.head), StateTransition(restId)),
          BlockState(restId, restParts.head) :: states
        )
        
      case Return(c: Call, implct) => 
        // note: this is a tail-call, this case should eventually become impossible when there is a tail call optimizer
        val t = freshTmp()
        val nextState = freshId()
        val blk = Assign(t, c, StateTransition(nextState))

        val retBlk = Return(Value.Ref(t), false)

        PartRet(blk, BlockState(nextState, retBlk) :: Nil)
      case l @ Label(label, body, rest) =>
        val startId = freshId() // start of body
        val endId = freshId() // start of rest

        val PartRet(bodyNew, parts) = go(body)(using labelIds + (label -> (startId, endId)), S(endId))
        val PartRet(restNew, restParts) = go(rest)
        PartRet(
          StateTransition(startId), 
          BlockState(startId, bodyNew) :: BlockState(endId, restNew) :: parts ::: restParts
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
        // TODO: Same comment as in Match
        val restId = freshId()
        val PartRet(subNew, subParts) = go(sub)(afterEnd = S(restId))
        val PartRet(restNew, restParts) = go(rest)
        
        PartRet(subNew, BlockState(restId, restNew) :: subParts ::: restParts)
      case Assign(lhs, rhs: Call, rest) => ??? // TODO: awaiting changes
      case AssignField(lhs, nme, rhs: Call, rest) => ???
      case Define(defn, rest) => 
        val PartRet(head, parts) = go(rest)
        PartRet(Define(defn, head), parts)
      case End(_) | Return(Value.Lit(Tree.UnitLit(true)), true) => afterEnd match
        case None => PartRet(blk, Nil)
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
      case Throw(_) => ??? // ignore

    val headId = freshId()

    val ret = go(blk)(using Map.empty, N)
    BlockState(headId, ret.head) :: ret.states
  

  def createContClass(fun: FunDefn): ClsLikeDefn =
    val clsSymbol = ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N), 
      Tree.Ident("Cont$" + fun.sym.nme)
    )
    val kind = syntax.Cls
    
    ???

  // Create the symbol for the continuation
  // This should only be called once because symbols contain a uid internally
  def getContClassSymbol(sym: Opt[BlockMemberSymbol]): ClassSymbol =
    ClassSymbol(
      Tree.TypeDef(syntax.Cls, Tree.Error(), N, N),
      Tree.Ident("Cont$" + summon[Elaborator.State].nextUid + "$" + sym.getOrElse(""))
    )

  def instrumentBlock(sym: ClassSymbol, blk: Block, locals: Set[Symbol]): Block =
    // TODO: create a continuation class and return a transformed block to be used in a function or a lambda or a handler block
    // CHANGES:
    // 1. symbol in locals should be transformed to be accessed and modified using the class itself in this function
    // 2. calls to separation symbol should disappear and the block should read this.pc and jump to the correct symbol
    blk

  override def term(t: st)(k: Result => Block)(using Subst): Block =
    t match
    case st.Blk((td: TermDefinition) :: stats, res) =>
      td match
      case TermDefinition(_, syntax.Fun, _, _, _, S(bod), _) =>
        val contClassSymbol = getContClassSymbol(S(td.sym))
        // TODO: add current symbol to handlerCtx
        val (locals, bodRaw) = handlerCtx.handleFun { returnedTerm(bod) }
        val bodTrm = instrumentBlock(contClassSymbol, bodRaw, locals)
        Define(FunDefn(td.sym, td.params, bodTrm),
          term(st.Blk(stats, res))(k))
      case _ => super.term(t)(k)
    case st.Blk(st.Handle(lhs, rhs, defs) :: stats, res) =>
      tl.log(s"Lowering.term ${t.showDbg.truncate(30, "[...]")}")
      val uid = freshId()
      // FIXME: Assumed defs are in the correct order, which is not checked currently
      val termHandlerFuns = (k: Ls[Value.Lam] => Block) => (defs.foldRight[Ls[Value.Lam] => Block](k)((df, acc) =>
        df match
        case TermDefinition(_, _, sym, params, _, _, _) =>
          val realParams = params.head.params.dropRight(1)
          val idFuncX = VarSymbol(Tree.Ident("x"), -1)
          val idFunc = Value.Lam(Param(FldFlags.empty, idFuncX, N) :: Nil, Return(Value.Ref(idFuncX), false))
          val cont = freshTmp("cont")
          
          val mkHandler: Path => Value.Lam = (sym: Path) => Value.Lam(realParams,
            blockBuilder
              .assign(cont, instCont(idFunc))
              .assignField(Value.Ref(cont), Tree.Ident("last"), Value.Ref(cont))
              .assignField(Value.Ref(cont), Tree.Ident("handler"), Value.Ref(lhs))
              .assignField(Value.Ref(cont), Tree.Ident("handlerFun"), sym)
              .assignField(Value.Ref(cont), Tree.Ident("params"), Value.Arr(realParams.map(p => Value.Ref(p.sym))))
              .ret(Value.Ref(cont), false)
          )
          // FIXME: do the dummy identifier do any harm?
          // This automatically instrument df as desired
          (args: Ls[Value.Lam]) => subTerm(st.Blk(df :: Nil, st.Ref(sym)(Tree.Ident("dummy"), -1)))(r => acc(mkHandler(r) :: args))
        case _ => _ => End("error") // only term definitions should appear
      ))(Nil)
      termHandlerFuns: handlerFuns =>
        subTerm(rhs): cls =>
          val cur = freshTmp("cur")
          val lblBdy = freshTmp("lblBdy")
          val lblH = freshTmp("lblH")
          val tmp = freshTmp()
          
          val contClassSymbol = getContClassSymbol(N)
          // TODO: add to ctx
          val (locals, bodRaw) = handlerCtx.handleScoped(r =>
            Assign(cur, r, Break(lblBdy, false))
          ) { Assign(lhs, Instantiate(cls, handlerFuns), term(st.Blk(stats, res))(r => Assign(cur, r, End()))) }
          
          val bod = instrumentBlock(contClassSymbol, bodRaw, locals)
          
          val equalToCurVal = Call(Value.Ref(BuiltinSymbol("===", true, false, false)), Select(Value.Ref(cur), Tree.Ident("handler")) :: Value.Ref(lhs) :: Nil)
          
          blockBuilder
            .label(lblBdy, bod)
            .assign(cur, Call(Value.Ref(separationSymbol), Value.Lit(Tree.IntLit(uid)) :: Nil)) // TODO: use new syntax
            .label(lblH, Match(
              Value.Ref(cur),
              Case.Cls(contSym, contTrm) ->
                Match(
                  Select(Value.Ref(cur), Tree.Ident("handler")),
                  Case.Lit(Tree.UnitLit(true)) -> blockBuilder // BAD! we should check equality to undefined, just being lazy (and wrong) for now
                    .assign(tmp, equalToCurVal)
                    .rest(Match(
                      Value.Ref(tmp),
                      Case.Lit(Tree.UnitLit(true)) -> blockBuilder
                        // TODO: pass correct arguments
                        // TODO: we need to access array elem
                        // TODO: we can use methods for now
                        // TODO: oops, we need resume afterall
                        // resume should be returning the resumption of current until effect not of current handler is raised
                        .assign(cur, Call(
                          Select(Select(Value.Ref(cur), Tree.Ident("handlerFun")), Tree.Ident("apply")),
                          Value.Lit(Tree.UnitLit(false)) :: Select(Value.Ref(cur), Tree.Ident("args")) :: Nil // We need to append resume to the arg list
                        ))
                        .continue(lblH) :: Nil, 
                      N,
                      End()
                    )) :: Nil,
                  S(blockBuilder // TODO: append continuation
                    .rest(handlerCtx.jumpToHandler(Value.Ref(cur)))),
                  End()
                ) :: Nil,
              N,
              End()
            ))
            .rest(k(Value.Ref(cur)))
    case st.App(f, args) =>
      tl.log(s"Lowering.term ${t.showDbg.truncate(30, "[...]")}")
      val uid = freshId()
      val res = freshTmp("res")
      super.term(t): r =>
        Assign(res, r,
          Match(
            Value.Ref(res),
            // TODO: append continuation before jumpToHandler
            // TODO: get the resumption symbol from handlerCtx
            Case.Cls(contSym, contTrm) -> handlerCtx.jumpToHandler(Value.Ref(res)) :: Nil,
            N,
            Assign(res, Call(Value.Ref(separationSymbol), List(Value.Lit(Tree.IntLit(uid)))), k(Value.Ref(res)))
          )
        )
    case st.Lam(params, body) =>
      val contClassSymbol = getContClassSymbol(N)
      // TODO: add symbol to ctx
      val (locals, bodRaw) = handlerCtx.handleFun { returnedTerm(body) }
      k(Value.Lam(params, instrumentBlock(contClassSymbol, bodRaw, locals)))
    case _ => super.term(t)(k)

  override def topLevel(t: st): Block =
    // TODO: A hack to make it show some JS, should be removed later
    Assign(separationSymbol, Value.Lit(Tree.UnitLit(true)),
      super.topLevel(Blk(/*effectSigDef :: */contDef :: t :: Nil, st.Lit(Tree.UnitLit(true))))
    )
    