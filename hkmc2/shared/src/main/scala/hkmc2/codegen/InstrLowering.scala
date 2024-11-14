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
  case class HandlerCtx(handlers: List[Path => Block], defaultHandler: Path => Block):
    def jumpToHandler(res: Path): Block =
      handlers match
        case Nil => defaultHandler(res)
        case h :: _ => h(res)
  object HandlerCtx:
    def empty: HandlerCtx = HandlerCtx(Nil, _ => Throw(
      Instantiate(Select(Value.Ref(Elaborator.Ctx.globalThisSymbol), Tree.Ident("Error")),
      Value.Lit(Tree.StrLit("Unhandled effects")) :: Nil)
    ))
    val default: HandlerCtx = HandlerCtx(Nil, Return(_, false))
import InstrLowering.*

class InstrLowering(using TL, Raise, Elaborator.State) extends Lowering:

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
    ObjBody(st.Blk(Nil, Term.Lit(Tree.UnitLit(true)))))
  private val effectSigTrm = Select(Select(Value.Ref(Elaborator.Ctx.globalThisSymbol), effectSigIdent), Tree.Ident("class"))
  effectSigSym.defn = S(effectSigDef)
  
  private val contIdent: Tree.Ident = Tree.Ident("Cont$")
  private val contTree: Tree.TypeDef = Tree.TypeDef(syntax.Cls, Tree.Error(), N, N)
  private val contSym: ClassSymbol = ClassSymbol(contTree, contIdent)
  private val contDef = ClassDef(
    N,
    syntax.Cls,
    contSym,
    Nil,
    S(("resume" :: "resumed" :: "next" :: "last" :: Nil).map(name =>
      Param(FldFlags.empty, TermSymbol(ParamBind, S(contSym), Tree.Ident(name)), None)
    )),
    ObjBody(st.Blk(Nil, Term.Lit(Tree.UnitLit(true)))))
  private val contTrm = Select(Select(Value.Ref(Elaborator.Ctx.globalThisSymbol), contIdent), Tree.Ident("class"))
  contSym.defn = S(contDef)
  
  def handlerCtx(using HandlerCtx): HandlerCtx = summon[HandlerCtx]

  // special function denoting state transitions, transitionFn should never appear in the real output
  private def freshTmp(dbgNme: Str = "tmp") = new TempSymbol(summon[Elaborator.State].nextUid, N, dbgNme)
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

  override def term(t: st)(k: Result => Block)(using Subst, HandlerCtx): Block =
    t match
    case st.Blk((td: TermDefinition) :: stats, res) =>
      td match
      case TermDefinition(_, syntax.Fun, _, _, _, S(bod), _) =>
        val bodTrm = HandlerCtx.default.givenIn:
          returnedTerm(bod)
        Define(FunDefn(td.sym, td.params, bodTrm),
          term(st.Blk(stats, res))(k))
      case _ => super.term(t)(k)
    case st.Blk(st.Handle(lhs, rhs, defs) :: stats, res) =>
      tl.log(s"Lowering.term ${t.showDbg.truncate(30, "[...]")}")
      // TODO: save handler context and states for uid
      val uid = freshId()
      // FIXME: Assumed defs are in the correct order, which is not checked currently
      val termHandlerFuns = (k: Ls[Value.Lam] => Block) => (defs.foldRight[Ls[Value.Lam] => Block](k)((a, acc) =>
        a match
        case TermDefinition(_, _, sym, params, _, _, _) =>
          val realParams = params.head.params.dropRight(1)
          // st.Lam(Param(FldFlags.empty, sym, N) :: Nil, st.Ret(st.Ref()))
          // val sym = VarSymbol(Tree.Ident("tmp"), 666)
          // FIXME: This should generate x => x
          val idFunc = Value.Lam(Nil, Return(Value.Lit(Tree.UnitLit(true)), false))
          val dummyContSym = new TempSymbol(summon[Elaborator.State].nextUid, N, "cont")
          val dummyCont = Instantiate(contTrm, idFunc :: Value.Lit(Tree.BoolLit(false)) :: Value.Lit(Tree.UnitLit(true)) :: Value.Lit(Tree.UnitLit(true)) :: Nil)
          
          val mkHandler: Path => Value.Lam = (sym: Path) => Value.Lam(realParams,
            Assign(dummyContSym, dummyCont,
              AssignField(Value.Ref(dummyContSym), Tree.Ident("last"), Value.Ref(dummyContSym),
                Return(
                  Instantiate(effectSigTrm, Value.Ref(lhs) :: sym :: Value.Arr(realParams.map(p => Value.Ref(p.sym))) :: Value.Ref(dummyContSym) :: Nil),
                  false
                )
              )
            )
          )
          // TODO: dummy Ref
          (args: Ls[Value.Lam]) => subTerm(st.Blk(a :: Nil, st.Ref(sym)(Tree.Ident("dummy"), 0)))(r => acc(mkHandler(r) :: args))
        case _ => _ => End("error") // only term definitions should appear
      ))(Nil)
      termHandlerFuns: handlerFuns =>
        subTerm(rhs): cls =>
          val cur = new TempSymbol(summon[Elaborator.State].nextUid, N, "cur")
          val nxt = new TempSymbol(summon[Elaborator.State].nextUid, N, "nxt")
          val lblBdy = new TempSymbol(summon[Elaborator.State].nextUid, N, "handlerBody")
          val lblH = new TempSymbol(summon[Elaborator.State].nextUid, N, "handler")
          val tmp = new TempSymbol(summon[Elaborator.State].nextUid, N)
          /*
            // let's pretend effect signature is a continuation, the impl is wrong now
            // cur is either a value, a continuation
            // nxt is either undefined or a continuation
            nxt = undefined;
            while (true) {
              if (cur is continuation) {
                append nxt to cur (amortized cost, set last properly on searched elem)
                if (cur is effect and handled by current handler) {
                  nxt = cur.nxt
                  cur = handle(cur)
                  continue
                }
                nxt = undefined;
                do jumpToHandler with appended cur
                (there should be a resume entry that assign result to cur and resume the loop)
              } else if (nxt is undefined) {
                break
              } else {
                cur = nxt.resume(cur);
                nxt = undefined;
              }
              continue
            }
          */
          val bdy = handlerCtx.copy(handlers = (r =>
            Assign(cur, r, Break(lblBdy, false)) // FIXME: this should append automata of the current handler block
          ) :: handlerCtx.handlers).givenIn:
            Assign(lhs, Instantiate(cls, handlerFuns), term(st.Blk(stats, res))(r => Assign(cur, r, End())))
          Label(
            lblBdy,
            bdy,
            Assign(nxt, Value.Lit(Tree.UnitLit(true)),
              Label(
                lblH,
                Match(
                  Value.Ref(cur),
                  (Case.Cls(contSym, contTrm) ->
                    // FIXME: this is wrong, a loop is needed to get the real last, and last should be updated for amortized efficient lookup later.
                    // Easier to implement: write in js directly and use a function call here
                    AssignField(Select(Value.Ref(cur), Tree.Ident("last")), Tree.Ident("next"), Value.Ref(nxt),
                      Match(
                        Value.Ref(cur),
                        (Case.Cls(effectSigSym, effectSigTrm) ->
                          Assign(
                            tmp,
                            Call(Value.Ref(BuiltinSymbol("===", true, false, false)), Select(Value.Ref(cur), Tree.Ident("handler")) :: Value.Ref(lhs) :: Nil),
                            Match(
                              Value.Ref(tmp),
                              (Case.Lit(Tree.BoolLit(true)) ->
                                Assign(nxt, Select(Value.Ref(cur), Tree.Ident("next")), Assign(cur, Call(
                                  Select(Value.Ref(cur), Tree.Ident("handlerFun")),
                                  Nil // TODO: argument is from handler itself!
                                ), Break(lblH, true)))
                              ) :: Nil,
                              N,
                              End()
                            )
                          )
                        ) :: Nil,
                        N,
                        Assign(cur, Call(Value.Ref(separationSymbol), List(Value.Lit(Tree.IntLit(uid)))), End())
                      )
                    )
                  ) :: Nil,
                  // cur is not continuation
                  S(Match(
                    Value.Ref(nxt),
                    (Case.Lit(Tree.UnitLit(true)) ->
                      Break(lblH, false)
                    ) :: Nil,
                    S(Assign(cur, Call(Select(Value.Ref(nxt), Tree.Ident("resume")), Value.Ref(cur) :: Nil), Assign(nxt, Value.Lit(Tree.UnitLit(true)), End()))),
                    Break(lblH, true),
                  )),
                  End()
                ),
                k(Value.Ref(cur))
              )
            )
          )
    case st.App(f, args) =>
      tl.log(s"Lowering.term ${t.showDbg.truncate(30, "[...]")}")
      // TODO: save handler context and states for uid
      val uid = freshId()
      // TODO: we don't need termAsLocalSuper, just use another local
      val res = freshTmp("res")
      super.term(t): r =>
        Assign(res, r,
          Match(
            Value.Ref(res),
            (Case.Cls(effectSigSym, effectSigTrm) -> Assign(res, Call(Value.Ref(separationSymbol), List(Value.Lit(Tree.IntLit(uid)))), End())) :: Nil,
            N,
            k(Value.Ref(res))
          )
        )
    case st.Lam(params, body) =>
      HandlerCtx.default.givenIn:
        k(Value.Lam(params, returnedTerm(body)))
    case _ => super.term(t)(k)
  override def topLevel(t: st): Block =
    // TODO: A hack to make it show some JS, should be removed later
    Assign(separationSymbol, Value.Lit(Tree.UnitLit(true)),
      super.topLevel(Blk(effectSigDef :: contDef :: t :: Nil, Term.Lit(Tree.UnitLit(true))))
    )
    