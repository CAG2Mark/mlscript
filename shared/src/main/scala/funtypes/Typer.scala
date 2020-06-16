package funtypes

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import funtypes.utils._, shorthands._
import funtypes.Message._

/** A class encapsulating type inference state.
 *  It uses its own internal representation of types and type variables, using mutable data structures.
 *  Inferred SimpleType values are then turned into CompactType values for simplification.
 *  In order to turn the resulting CompactType into a funtypes.Type, we use `expandCompactType`.
 */
class Typer(var dbg: Boolean, var verbose: Bool, var explainErrors: Bool) extends ConstraintSolver with TypeSimplifier {
  
  type Ctx = Map[String, TypeScheme]
  type Raise = Diagnostic => Unit
  
  val primProv: TypeProvenance = TypeProvenance(N, "expression")
  
  val UnitType: PrimType = PrimType(Var("unit"), primProv)
  val BoolType: PrimType = PrimType(Var("bool"), primProv)
  val IntType: PrimType = PrimType(Var("int"), primProv)
  val DecType: PrimType = PrimType(Var("number"), primProv)
  val StrType: PrimType = PrimType(Var("string"), primProv)
  
  val builtins: Ctx = {
    val tv = freshVar(primProv)(1) // Q: level?
    import FunctionType.{ apply => fun }
    Map(
      "true" -> BoolType,
      "false" -> BoolType,
      "not" -> fun(BoolType, BoolType, primProv),
      "succ" -> fun(IntType, IntType, primProv),
      "log" -> PolymorphicType(0, fun(tv, UnitType, primProv)),
      "discard" -> PolymorphicType(0, fun(tv, UnitType, primProv)),
      "add" -> fun(IntType, fun(IntType, IntType, primProv), primProv),
      "+" -> fun(IntType, fun(IntType, IntType, primProv), primProv),
      "<" -> fun(IntType, fun(IntType, BoolType, primProv), primProv),
      "id" -> {
        val v = freshVar(primProv)(1)
        PolymorphicType(0, fun(v, v, primProv))
      },
      "if" -> {
        val v = freshVar(primProv)(1)
        PolymorphicType(0, fun(BoolType, fun(v, fun(v, v, primProv), primProv), primProv))
      },
    )
  }
  
  /** The main type inference function */
  def inferTypes(pgrm: Pgrm, ctx: Ctx = builtins): List[Either[TypeError, PolymorphicType]] =
    pgrm.defs match {
      case (isrec, nme, rhs) :: defs =>
        val ty_sch = try Right(typeLetRhs(isrec, nme, rhs)(ctx, 0, throw _)) catch {
          case err: TypeError => Left(err) }
        val errProv = TypeProvenance(rhs.toLoc, "let-bound value")
        ty_sch :: inferTypes(Pgrm(defs), ctx + (nme -> ty_sch.getOrElse(freshVar(errProv)(0))))
      case Nil => Nil
    }
  
  // Saldy, the version above does not work in JavaScript as it raises a
  //    "RangeError: Maximum call stack size exceeded"
  // So we have to go with this uglier one:
  def inferTypesJS(
    pgrm: Pgrm,
    ctx: Ctx = builtins,
    stopAtFirstError: Boolean = true,
  ): List[Either[TypeError, PolymorphicType]] = {
    var defs = pgrm.defs
    var curCtx = ctx
    var res = collection.mutable.ListBuffer.empty[Either[TypeError, PolymorphicType]]
    while (defs.nonEmpty) {
      val (isrec, nme, rhs) = defs.head
      defs = defs.tail
      val ty_sch = try Right(typeLetRhs(isrec, nme, rhs)(curCtx, 0, throw _)) catch {
        case err: TypeError =>
          if (stopAtFirstError) defs = Nil
          Left(err)
      }
      res += ty_sch
      val errProv = TypeProvenance(rhs.toLoc, "let-bound value")
      curCtx += (nme -> ty_sch.getOrElse(freshVar(errProv)(0)))
    }
    res.toList
  }
  
  def typeBlk(blk: Blk, ctx: Ctx = builtins, allowPure: Bool = false)
        : List[List[Diagnostic] -> PolymorphicType]
        = blk.stmts match {
    case s :: stmts =>
      val diags = mutable.ListBuffer.empty[Diagnostic]
      val (newCtx, ty) = typeStatement(s, allowPure)(ctx, 0, diags += _)
      diags.toList -> ty :: typeBlk(Blk(stmts), newCtx, allowPure)
    case Nil => Nil
  }
  def typeStatement(s: Statement, allowPure: Bool = false)
        (implicit ctx: Ctx, lvl: Int, raise: Raise): Ctx -> PolymorphicType = s match {
    case LetS(isrec, Var(nme), rhs) =>
      val ty_sch = typeLetRhs(isrec, nme, rhs)
      (ctx + (nme -> ty_sch)) -> ty_sch
    case LetS(isrec, pat, rhs) => lastWords("Not yet supported: pattern " + pat)
    case t @ Tup(fs) if !allowPure => // Note: not sure this is still used!
      val thing = fs match {
        case (S(_), _) :: Nil => "field"
        case Nil => "empty tuple"
        case _ => "tuple"
      }
      warn(s"Useless $thing in statement position.", t.toLoc)
      ctx -> PolymorphicType(0, typeTerm(t))
    case t: Term =>
      val ty = typeTerm(t)
      if (!allowPure) {
        if (t.isInstanceOf[Var] || t.isInstanceOf[Lit])
          warn("Pure expression does nothing in statement position.", t.toLoc)
        else
          constrain(mkProxy(ty, TypeProvenance(t.toCoveringLoc, "expression in statement position")),
            UnitType)(raise = raise, prov = TypeProvenance(t.toLoc, t.describe)) // TODO add explanation message
      }
      ctx -> PolymorphicType(0, ty)
  }
  
  def inferType(term: Term, ctx: Ctx = builtins, lvl: Int = 0): SimpleType =
    typeTerm(term)(ctx, lvl, throw _)
  
  /** Infer the type of a let binding right-hand side. */
  def typeLetRhs(isrec: Boolean, nme: String, rhs: Term)
        (implicit ctx: Ctx, lvl: Int, raise: Raise): PolymorphicType = {
    val res = if (isrec) {
      val e_ty = freshVar(TypeProvenance(rhs.toLoc, "let-bound value"))(lvl + 1)
      val ty = typeTerm(rhs)(ctx + (nme -> e_ty), lvl + 1, raise)
      constrain(ty, e_ty)(raise, TypeProvenance(rhs.toLoc, "binding of " + rhs.describe))
      e_ty
    } else typeTerm(rhs)(ctx, lvl + 1, raise)
    PolymorphicType(lvl, res)
  }
  
  def mkProxy(ty: SimpleType, prov: TypeProvenance): SimpleType = {
    ProxyType(ty)(prov)
    // TODO switch to return this in perf mode:
    // ty
  }
  
  /** Infer the type of a term. */
  def typeTerm(term: Term)
        (implicit ctx: Ctx, lvl: Int, raise: Raise): SimpleType
        = trace(s"$lvl. Typing $term") {
    import TypeProvenance.{apply => tp}
    implicit val prov: TypeProvenance = TypeProvenance(term.toLoc, term.describe)
    term match {
      case Var(name) =>
        val ty = ctx.getOrElse(name, {
          // TODO: delay type expansion to message display and show the expected type here!
          err("identifier not found: " + name, term.toLoc)
          freshVar(tp(term.toLoc, "unknown variable"))
        }).instantiate
        mkProxy(ty, tp(term.toLoc, term.describe))
        // ^ TODO maybe use a description passed in param?
        // currently we get things like "flows into variable reference"
        // but we used to get the better "flows into object receiver" or "flows into applied expression"...
      case Lam(v @ Var(name), body) =>
        val param = freshVar(tp(if (verboseConstraintProvenanceHints) v.toLoc else N, "parameter"))
        val body_ty = typeTerm(body)(ctx + (name -> param), lvl, raise)
        FunctionType(param, body_ty, tp(term.toLoc, "function"))
      case Lam(lhs, rhs) => ???
      case App(f, a) =>
        val f_ty = typeTerm(f)
        val a_ty = typeTerm(a)
        val res = freshVar(prov)
        val arg_ty = mkProxy(a_ty, tp(a.toCoveringLoc, "argument"))
        val fun_ty = mkProxy(f_ty, tp(f.toCoveringLoc, "applied expression"))
        constrain(fun_ty, FunctionType(arg_ty, res, prov))
        res
      case lit: Lit => PrimType(lit, tp(term.toLoc, "constant literal"))
      case Sel(obj, name) =>
        val o_ty = typeTerm(obj)
        val res = freshVar(prov)
        val obj_ty_ = mkProxy(o_ty, tp(obj.toCoveringLoc, "receiver"))
        constrain(obj_ty_, RecordType((name, res) :: Nil, prov))
        res
      case Rcd(fs) => // TODO rm: no longer used?
        RecordType(fs.map { case (n, t) => (n, typeTerm(t)) }, tp(term.toLoc, "record literal"))
      case Let(isrec, nme, rhs, bod) =>
        val n_ty = typeLetRhs(isrec, nme, rhs)
        typeTerm(bod)(ctx + (nme -> n_ty), lvl, raise)
      case tup: Tup =>
        typeTerms(tup :: Nil, false, Nil)
      case Bra(false, trm: Blk) => typeTerm(trm)
      case Bra(rcd, trm @ (_: Tup | _: Blk)) => typeTerms(trm :: Nil, rcd, Nil)
      case Bra(_, trm) => typeTerm(trm)
      case Blk((s: Term) :: Nil) => typeTerm(s)
      case Blk(Nil) => UnitType
      // case Blk(s :: stmts) =>
      //   val (newCtx, ty) = typeStatement(s)
      //   typeTerm(Blk(stmts))(newCtx, lvl, raise)
      case Blk(stmts) => typeTerms(stmts, false, Nil)
    }
  }(r => s"$lvl. : ${r}")
  
  def typeTerms(term: Ls[Statement], rcd: Bool, fields: List[Opt[Str] -> SimpleType])
        (implicit ctx: Ctx, lvl: Int, raise: Raise, prov: TypeProvenance): SimpleType
      = term match {
    case (trm @ Var(nme)) :: sts if rcd => // field punning
      typeTerms(Tup(S(nme) -> trm :: Nil) :: sts, rcd, fields)
    case Blk(sts0) :: sts1 => typeTerms(sts0 ::: sts1, rcd, fields)
    case Tup(Nil) :: sts => typeTerms(sts, rcd, fields)
    case Tup((no, trm) :: ofs) :: sts =>
      val ty = if (ofs.isEmpty) typeTerm(Bra(rcd, trm)) else typeTerm(trm)
      val newCtx = no.fold(ctx)(n => ctx + (n -> ty))
      typeTerms(Tup(ofs) :: sts, rcd, (no, ty) :: fields)(newCtx, lvl, raise, prov)
    case (trm: Term) :: Nil =>
      if (fields.nonEmpty)
        warn("Previous field definitions are discarded by this returned expression.", trm.toLoc)
      typeTerm(trm)
    // case (trm: Term) :: Nil =>
    //   assert(!rcd)
    //   val ty = typeTerm(trm)
    //   typeBra(Nil, rcd, (N, ty) :: fields)
    case s :: sts =>
      val (newCtx, ty) = typeStatement(s)
      typeTerms(sts, rcd, fields)(newCtx, lvl, raise, prov)
    case Nil =>
      // TODO actually use a tuple type if !rcd
      val fs = fields.reverseIterator.zipWithIndex.map {
        case ((N, t), i) => ("_" + (i + 1), t); case ((S(n), t), _) => (n, t)
      }.toList
      RecordType(fs, prov)
  }
  
  /** Convert an inferred SimpleType into the immutable Type representation. */
  def expandType(st: SimpleType, polarity: Bool = true): Type = {
    val recursive = mutable.Map.empty[PolarVariable, TypeVar]
    def go(st: SimpleType, polarity: Boolean)(inProcess: Set[PolarVariable]): Type = st match {
      case tv: TypeVariable =>
        val tv_pol = tv -> polarity
        if (inProcess.contains(tv_pol))
          recursive.getOrElseUpdate(tv_pol, freshVar(tv.prov)(0).asTypeVar)
        else {
          val bounds = if (polarity) tv.lowerBounds else tv.upperBounds
          val boundTypes = bounds.map(go(_, polarity)(inProcess + tv_pol))
          val mrg = if (polarity) Union else Inter
          val res = boundTypes.foldLeft[Type](tv.asTypeVar)(mrg)
          recursive.get(tv_pol).fold(res)(Recursive(_, res))
        }
      case FunctionType(l, r, _) => Function(go(l, !polarity)(inProcess), go(r, polarity)(inProcess))
      case RecordType(fs, _) => Record(fs.map(nt => nt._1 -> go(nt._2, polarity)(inProcess)))
      case ProxyType(und) => go(und, polarity)(inProcess)
      case PrimType(n, _) => Primitive(n.idStr)
    }
    go(st, polarity)(Set.empty)
  }
  
}
