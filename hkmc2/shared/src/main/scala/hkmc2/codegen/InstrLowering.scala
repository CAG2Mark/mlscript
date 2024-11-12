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
          val params = handlerFuns.map(hFun => Lam)
          val discard = new TempSymbol(summon[Elaborator.State].nextUid, N)
          val cur = new TempSymbol(summon[Elaborator.State].nextUid, N, "cur")
          val nxt = new TempSymbol(summon[Elaborator.State].nextUid, N, "nxt")
          val lblBdy = new TempSymbol(summon[Elaborator.State].nextUid, N, "handlerBody")
          val lblH = new TempSymbol(summon[Elaborator.State].nextUid, N, "handler")
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
                do jumpToHandler with cur
              } else if (nxt is undefined) {
                break
              } else {
                cur = resume nxt with cur;
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
                          Match(
                            // FIXME: this should be equality with lhs
                            Select(Value.Ref(cur), Tree.Ident("handler")),
                            (Case.Lit(Tree.BoolLit(true)) ->
                              Assign(nxt, Select(Value.Ref(cur), Tree.Ident("next")), Assign(cur, Call(
                                Select(Value.Ref(cur), Tree.Ident("handlerFun")),
                                Nil // TODO: argument is from handler itself!
                              ), Break(lblH, true)))
                            ) :: Nil,
                            N,
                            End()
                          )
                        ) :: Nil,
                        N,
                        handlerCtx.jumpToHandler(Value.Ref(cur))
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
            /*
            Label(
              lblBdy,
              Assign(lhs, Instantiate(cls, handlerFuns), term(st.Blk(stats, res))(r => Assign(cur, r, End()))),
              Label(
                lblH,
                Match(
                  Value.Ref(cur),
                  (Case.Cls(effectSigSym, effectSigTrm) -> Match(
                    Select(Value.Ref(cur), Tree.Ident("handler")), // FIXME: should be equality with lhs
                    (Case.Lit(Tree.BoolLit(true)) ->
                      Assign(nxt, Select(Select(Value.Ref(cur), Tree.Ident("cont")), Tree.Ident("next")),
                          Assign(cur,
                            Call(
                              Select(Value.Ref(cur), Tree.Ident("handlerFun")),
                              Nil // FIXME: pass correct params from cur
                            ),
                            Match(
                              Value.Ref(cur),
                              (Case.Cls(effectSigSym, effectSigTrm) -> Match(
                                Select(Value.Ref(cur), Tree.Ident("handler")), // FIXME: should be equality with lhs
                                (Case.Lit(Tree.BoolLit(true)) ->
                                  // FIXME: this is wrong, a loop is needed to get the real last, and last should be updated for amortized efficient lookup later.
                                  AssignField(Select(Select(Value.Ref(cur), Tree.Ident("cont")), Tree.Ident("last")), Tree.Ident("next"), Value.Ref(nxt),
                                    Break(lblH, true)
                                  )
                                ) :: Nil,
                                End(),
                                End()
                              )) :: Nil,
                              End(),
                              End()
                            )
                          ),
                          End()
                        )
                      )
                    ) :: Nil,
                    End(),
                    End()
                  )
                ),
                Some(k(Value.Ref(cur)))
              )
            )
            */
    case st.App(f, args) =>
      tl.log(s"Lowering.term ${t.showDbg.truncate(30, "[...]")}")
      subtermSuper(t): res =>
        Match(
          res,
          (Case.Cls(effectSigSym, effectSigTrm), summon[HandlerCtx].jumpToHandler(res)) :: Nil,
          Some(k(res)), // FIXME: This should chain with the current context's automata
          End()
        )
    case st.Lam(params, body) =>
      HandlerCtx.default.givenIn:
        k(Value.Lam(params, returnedTerm(body)))
    case _ => super.term(t)(k)
  
  private def subtermSuper(t: st)(k: Path => Block)(using Subst, HandlerCtx): Block =
    super.term(t)(asSubTerm(_)(k))

  override def topLevel(t: st): Block =
    super.topLevel(Blk(effectSigDef :: contDef :: t :: Nil, Term.Lit(Tree.UnitLit(true))))
    