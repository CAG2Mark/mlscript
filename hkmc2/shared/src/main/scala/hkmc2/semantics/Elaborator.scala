package hkmc2
package semantics

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import syntax.*
import Tree.*
import hkmc2.Message.MessageContext
import scala.annotation.tailrec


object Elaborator:
  case class Ctx(parent: Opt[Ctx], members: Map[Str, Symbol], locals: Map[Str, VarSymbol])
  object Ctx:
    val empty: Ctx = Ctx(N, Map.empty, Map.empty)
  type Ctxl[A] = Ctx ?=> A
  def ctx: Ctxl[Ctx] = summon
import Elaborator.*

class Elaborator(raise: Raise):
  
  private var curUi = 0
  def nextUid: Int = { curUi += 1; curUi }
  
  def term(tree: Tree): Ctxl[Term] = tree match
    case Block(s :: Nil) =>
      term(s)
    case Block(sts) =>
      block(sts)._1
    case lit: Literal =>
      Term.Lit(lit)
    case Let(lhs, rhs, bodo) =>
      val (pat, syms) = pattern(lhs)
      val r = term(rhs)
      val b = bodo.map(term(_)(using ctx.copy(locals = ctx.locals ++ syms))).getOrElse(unit)
      Term.Blk(List(LetBinding(pat, r)), b)
    case Ident(name) =>
      ctx.locals.get(name) match
        case S(sym) => sym.ref
        case N =>
          ctx.members.get(name) match
            case S(sym) => sym.ref
            case N =>
              raise(ErrorReport(msg"Name not found: $name" -> tree.toLoc :: Nil))
              Term.Error
    case TyApp(lhs, targs) =>
      Term.TyApp(term(lhs), targs.map(term(_)))
    case App(Ident("->"), Tup(l :: r :: Nil)) => // TODO also forbit other refs/definitions of ->
      Term.FunTy(term(Tup(l :: Nil)), term(r)) // FIXME handle multi params properly in parser
    case App(lhs, rhs) =>
      Term.App(term(lhs), term(rhs))
    case Sel(pre, nme) =>
      Term.Sel(term(pre), nme)
    case Tup(fields) =>
      Term.Tup(fields.map(fld(_)))
    case Empty() =>
      raise(ErrorReport(msg"A term was expected in this position, but no term was found." -> tree.toLoc :: Nil))
      Term.Error
    case Error() =>
      Term.Error
    case TermDef(k, sym, nme, rhs) =>
      raise(ErrorReport(msg"Illegal definition in term position." -> tree.toLoc :: Nil))
      Term.Error
    case TypeDef(k, head, extension, body) =>
      raise(ErrorReport(msg"Illegal type declaration in term position." -> tree.toLoc :: Nil))
      Term.Error
    // case _ =>
    //   ???
  
  def fld(tree: Tree): Ctxl[Fld] = tree match
    case InfixApp(lhs, Keyword.`:`, rhs) =>
      Fld(FldFlags.empty, term(lhs), S(term(rhs)))
    case _ => Fld(FldFlags.empty, term(tree), N)
  
  def unit: Term.Lit = Term.Lit(UnitLit(true))
  
  def block(sts: Ls[Tree])(using c: Ctx): (Term.Blk, Ctx) =
    val newMembers = mutable.Map.empty[Str, MemberSymbol]
    sts.foreach:
      case td: TermDef =>
        td.name match
          case R(id) =>
            newMembers.get(id.name) match
              case S(sym) =>
                raise(ErrorReport(msg"Duplicate definition of ${id.name}" -> td.toLoc
                  :: msg"aready defined gere" -> sym.toLoc :: Nil))
              case N =>
                newMembers += id.name -> TermSymbol(S(id))
          case L(d) => raise(d)
      case td: TypeDef =>
        td.name match
          case R(id) =>
            newMembers.get(id.name) match
              // TODO pair up companions
              case S(sym) =>
                raise(ErrorReport(msg"Duplicate definition of ${id.name}" -> td.toLoc
                  :: msg"aready defined gere" -> sym.toLoc :: Nil))
              case N =>
                newMembers += id.name -> ClassSymbol(id)
          case L(d) => raise(d)
      case _ =>
    given Ctx = c.copy(members = c.members ++ newMembers)
    @tailrec
    def go(sts: Ls[Tree], acc: Ls[Statement]): Ctxl[(Term.Blk, Ctx)] = sts match
      case Nil =>
        val res = unit
        (Term.Blk(acc.reverse, res), ctx)
      case Let(lhs, rhs, N) :: sts =>
        val (pat, syms) = pattern(lhs)
        val rhsTerm = term(rhs)
        go(sts, LetBinding(pat, rhsTerm) :: acc)(using ctx.copy(locals = ctx.locals ++ syms))
      case TermDef(k, sym, nme, rhs) :: sts =>
        val n = nme match
          case S(id: Ident) => id
          case S(InfixApp(id: Ident, Keyword.`:`, _)) => id
          // case _ => ???
        val s = TermSymbol(S(n))
        val b = rhs.map(term(_))
        val td = TermDefinition(k, s, b)
        s.defn = S(td)
        go(sts, td :: acc)
      case TypeDef(k, head, extension, body) :: sts =>
        assert((k is Cls) || (k is Mod), k)
        def processHead(head: Tree): Ctxl[(Ident, Ls[TyParam], Opt[Ls[Param]], Ctx)] = head match
          case TyApp(base, targs) =>
            
            val (name, tas, as, newCtx) = processHead(base)
            // TODO reject duplicated tas, out of order as
            
            val tparams =
              given Ctx = newCtx
              targs.flatMap:
                case id: Ident =>
                  val vs = VarSymbol(id.name, nextUid)
                  val res = TyParam(FldFlags.empty, vs)
                  vs.decl = S(res)
                  res :: Nil
                case InfixApp(lhs: Ident, Keyword.`:`, rhs) =>
                  val vs = VarSymbol(lhs.name, nextUid)
                  val res = TyParam(FldFlags.empty, vs)
                  vs.decl = S(res)
                  res :: Nil
            (name, tparams, as, newCtx.copy(locals = ctx.locals ++ tparams.map(tp => tp.sym.name -> tp.sym)))
          case App(base, args) =>
            
            val (name, tas, as, newCtx) = processHead(base)
            // TODO reject duplicated as
            
            val ps =
              given Ctx = newCtx
              args match
              case Tup(ps) =>
                ps.flatMap:
                  case InfixApp(lhs: Ident, Keyword.`:`, rhs) =>
                    Param(FldFlags.empty, VarSymbol(lhs.name, nextUid), term(rhs)) :: Nil
                  // case _ =>
            (name, tas, S(ps), newCtx.copy(locals = ctx.locals ++ ps.map(p => p.sym.name -> p.sym)))
          case id: Ident =>
            (id, Nil, N, ctx)
          // case _ => ???
        val (nme, tps, ps, newCtx) = processHead(head)
        val sym = newMembers(nme.name).asInstanceOf[ClassSymbol] // TODO improve
        val cd =
          given Ctx = newCtx
          val (bod, c) = body match
            case S(Tree.Block(sts)) => block(sts)
            case S(t) => block(t :: Nil)
            case N => (new Term.Blk(Nil, Term.Lit(UnitLit(true))), ctx)
          ClassDef(sym, tps, ps, ObjBody(bod))
        sym.defn = S(cd)
        go(sts, cd :: acc)
      case (result: Tree) :: Nil =>
        val res = term(result)
        (Term.Blk(acc.reverse, res), ctx)
    sts match
      case (_: TermDef | _: TypeDef) :: _ => go(sts, Nil)
      // case s :: Nil => (term(s), ctx)
      case _ => go(sts, Nil)
  
  def pattern(t: Tree): Ctxl[(Pattern, Ls[Str -> VarSymbol])] =
    val boundVars = mutable.HashMap.empty[Str, VarSymbol]
    def go(t: Tree): Pattern = t match
      case Ident(name) =>
        val sym = boundVars.getOrElseUpdate(name, VarSymbol(name, nextUid))
        Pattern.Var(sym)
      case Tup(fields) =>
        // val pats = fields.map(pattern)
        // Pattern.Tup(pats)
        ???
      case _ =>
        ???
    (go(t), boundVars.toList)
  
  def importFrom(sts: Ls[Tree])(using c: Ctx): Ctx =
    val (_, newCtx) = block(sts)
    // TODO handle name clashes
    c.copy(members = c.members ++ newCtx.members)
  
  
  def topLevel(sts: Ls[Tree])(using c: Ctx): (Term, Ctx) =
    val (res, ctx) = block(sts)
    computeVariances(res)
    (res, ctx)
  
  def computeVariances(s: Statement): Unit =
    val trav = VarianceTraverser()
    def go(s: Statement): Unit = s match
      case TermDefinition(_, sym, body) =>
        body match
          case S(b) =>
            go(b)
          case N =>
      case ClassDef(sym, tps, pso, body) =>
        pso.foreach: ps =>
          ps.foreach: p =>
            trav.traverseType(S(true))(p.sign)
        body.blk.stats.foreach(go)
        // s.subStatements.foreach(go)
      case _ =>
        s.subStatements.foreach(go)
    while trav.changed do
      trav.changed = false
      go(s)
    
  class VarianceTraverser(var changed: Bool = true) extends Traverser:
    override def traverseType(pol: Pol)(trm: Term): Unit = trm match
      case Term.TyApp(lhs, targs) =>
        lhs.resolveSymbol match
          case S(sym: ClassSymbol) =>
            sym.defn match
              case S(td: ClassDef) =>
                if td.tparams.sizeCompare(targs) =/= 0 then
                  raise(ErrorReport(msg"Wrong number of type arguments" -> trm.toLoc :: Nil)) // TODO BE
                td.tparams.zip(targs).foreach:
                  case (tp, targ) =>
                    if !tp.isContravariant then traverseType(pol)(targ)
                    if !tp.isCovariant then traverseType(pol.!)(targ)
              case N =>
                TODO(sym->sym.uid)
          case S(sym) => ???
          case N => ???
      case Term.Ref(sym: VarSymbol) =>
        sym.decl match
          case S(ty: TyParam) =>
            if pol =/= S(true) && ty.isCovariant then
              changed = true
              ty.isCovariant = false
            if pol =/= S(false) && ty.isContravariant then
              changed = true
              ty.isContravariant = false
          case _ => ???
      case _ => super.traverseType(pol)(trm)
  abstract class Traverser:
    def traverseType(pol: Pol)(trm: Term): Unit = trm match
      case Term.TyApp(lhs, targs) =>
        // lhs.resolveSymbol
        // targs.foreach(traverseType(pol))
        ???
      case r: Term.Ref =>
      case Term.FunTy(l, r) =>
        traverseType(pol.!)(l)
        traverseType(pol)(r)
      case Term.Tup(fields) =>
        // fields.foreach(f => traverseType(pol)(f.value))
        fields.foreach(traverseType(pol))
      // case _ => ???
    def traverseType(pol: Pol)(f: Fld): Unit =
      traverseType(pol)(f.value)
      f.asc.foreach(traverseType(pol))
end Elaborator

type Pol = Opt[Bool]
extension (p: Pol) def ! : Pol = p.map(!_)
