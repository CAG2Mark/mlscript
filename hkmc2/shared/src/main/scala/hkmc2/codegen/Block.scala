package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import hkmc2.{semantics => sem}
import hkmc2.semantics.{Term => st}

import syntax.{Literal, Tree}
import semantics.*
import semantics.Term.*


case class Program(
  imports: Ls[Local -> Str],
  main: Block,
)


sealed abstract class Block extends Product with AutoLocated:
  
  protected def children: Ls[Located] = ??? // Maybe extending AutoLocated is unnecessary
  
  lazy val definedVars: Set[Local] = this match
    case _: Return | _: Throw => Set.empty
    case Begin(sub, rst) => sub.definedVars ++ rst.definedVars
    case Assign(l: TermSymbol, r, rst) => rst.definedVars
    case Assign(l, r, rst) => rst.definedVars + l
    case AssignField(l, n, r, rst) => rst.definedVars
    case Match(scrut, arms, dflt, rst) =>
      arms.flatMap(_._2.definedVars).toSet ++ dflt.toList.flatMap(_.definedVars) ++ rst.definedVars
    case End(_) => Set.empty
    case Break(_, _) => Set.empty
    case Define(defn, rst) => rst.definedVars
    case TryBlock(sub, fin, rst) => sub.definedVars ++ fin.definedVars ++ rst.definedVars
    case Label(lbl, bod, rst) => bod.definedVars ++ rst.definedVars

  lazy val definedLocals: Set[Local] = this match
    case _: Return | _: Throw => Set.empty
    case Begin(sub, rst) => sub.definedVars ++ rst.definedVars
    case Assign(l: TermSymbol, r, rst) => rst.definedVars
    case Assign(l, r, rst) => rst.definedVars + l
    case AssignField(l, n, r, rst) => rst.definedVars
    case Match(scrut, arms, dflt, rst) =>
      arms.flatMap(_._2.definedVars).toSet ++ dflt.toList.flatMap(_.definedVars) ++ rst.definedVars
    case End(_) => Set.empty
    case Break(_, _) => Set.empty
    case Define(ValDefn(N, k, sym, rhs), rest) => rest.definedLocals + sym
    case Define(defn, rst) => rst.definedVars
    case TryBlock(sub, fin, rst) => sub.definedVars ++ fin.definedVars ++ rst.definedVars
    case Label(lbl, bod, rst) => bod.definedVars ++ rst.definedVars
  
  def mapChildBlocks(f: Block => Block): Block = this match
    case Match(scrut, arms, dflt, rest) => Match(scrut, arms.map{case cse -> blk => cse -> f(blk)}, dflt.map(f), f(rest))
    case Return(res, implct) => this
    case Throw(exc) => this
    case Label(label, body, rest) => Label(label, f(body), f(rest))
    case Break(label, toBeginning) => this
    case Begin(sub, rest) => Begin(f(sub), f(rest))
    case TryBlock(sub, finallyDo, rest) => TryBlock(f(sub), f(finallyDo), f(rest))
    case Assign(lhs, rhs, rest) => Assign(lhs, rhs, f(rest))
    case AssignField(lhs, nme, rhs, rest) => AssignField(lhs, nme, rhs, f(rest))
    case Define(defn, rest) => Define(defn, f(rest))
    case End(msg) => this
  
  
  // TODO conserve if no changes
  def mapTail(f: BlockTail => BlockTail): Block = this match
    case b: BlockTail => f(b)
    case Begin(sub, rst) => Begin(sub, rst.mapTail(f))
    case Assign(lhs, rhs, rst) => Assign(lhs, rhs, rst.mapTail(f))
    case Define(defn, rst) => Define(defn, rst.mapTail(f))
    case Match(scrut, arms, dflt, rst) =>
      Match(scrut, arms.map(_ -> _.mapTail(f)), dflt.map(_.mapTail(f)), rst.mapTail(f))

  def mapLocals(f: Local => Local): Block = this match
    case Match(scrut, arms, dflt, rest) => 
      val newScrut = scrut match
        case Value.Ref(l) => Value.Ref(f(l))
        case _ => scrut
      val newArms = arms.map((c, b) => (c, b.mapLocals(f)))
      Match(newScrut, newArms, dflt.map(_.mapLocals(f)), rest.mapLocals(f))
    case Return(res, implct) => Return(res.mapLocals(f), implct)
    case Throw(exc) => Throw(exc.mapLocals(f))
    case Label(label, body, rest) => Label(label, body.mapLocals(f), rest.mapLocals(f))
    case Break(label, toBeginning) => this
    case Begin(sub, rest) => Begin(sub.mapLocals(f), rest.mapLocals(f))
    case TryBlock(sub, finallyDo, rest) => TryBlock(sub.mapLocals(f), finallyDo.mapLocals(f), rest.mapLocals(f))
    case Assign(lhs, rhs, rest) => Assign(f(lhs), rhs.mapLocals(f), rest.mapLocals(f))
    case AssignField(lhs, nme, rhs, rest) => AssignField(lhs.mapLocals(f), nme, rhs.mapLocals(f), rest.mapLocals(f))
    case Define(defn, rest) => 
      Define(defn.mapLocals(f), rest.mapLocals(f))
    case End(msg) => this
  
  
end Block

sealed abstract class BlockTail extends Block

case class Match(
  scrut: Path,
  arms: Ls[Case -> Block],
  dflt: Opt[Block],
  rest: Block,
) extends Block with ProductWithTail

// * `implct`: whether it's a JS implicit return, without the `return` keyword
case class Return(res: Result, implct: Bool) extends BlockTail

case class Throw(exc: Result) extends BlockTail

case class Label(label: Local, body: Block, rest: Block) extends BlockTail

case class Break(label: Local, toBeginning: Bool) extends BlockTail

// TODO: remove this form?
case class Begin(sub: Block, rest: Block) extends Block with ProductWithTail

case class TryBlock(sub: Block, finallyDo: Block, rest: Block) extends Block with ProductWithTail

case class Assign(lhs: Local, rhs: Result, rest: Block) extends Block with ProductWithTail
// case class Assign(lhs: Path, rhs: Result, rest: Block) extends Block with ProductWithTail

case class AssignField(lhs: Path, nme: Tree.Ident, rhs: Result, rest: Block) extends Block with ProductWithTail

case class Define(defn: Defn, rest: Block) extends Block with ProductWithTail

sealed abstract class Defn:
  val sym: MemberSymbol[?]
  def mapLocals(f: Local => Local): Defn

// final case class TermDefn(
//     k: syntax.TermDefKind,
//     // sym: TermSymbol,
//     sym: BlockMemberSymbol,
//     params: Ls[ParamList],
//     body: Block,
// ) extends Defn
final case class FunDefn(
    // k: syntax.TermDefKind,
    // sym: TermSymbol,
    sym: BlockMemberSymbol,
    params: Ls[ParamList],
    body: Block,
) extends Defn:
  override def mapLocals(f: Local => Local): FunDefn =
    FunDefn(sym, params, body.mapLocals(f))

final case class ValDefn(
    owner: Opt[InnerSymbol],
    k: syntax.Val,
    sym: BlockMemberSymbol,
    // params: Ls[ParamList],
    rhs: Path,
) extends Defn:
  override def mapLocals(f: Local => Local): ValDefn =
    ValDefn(owner, k, sym, rhs.mapLocals(f))

final case class ClsLikeDefn(
  // sym: ClassSymbol,
  // sym: MemberSymbol[ClassLikeDef],
  sym: MemberSymbol[? <: ClassLikeDef],
  k: syntax.ClsLikeKind,
  methods: Ls[FunDefn],
  fields: Ls[TermSymbol],
  ctor: Block,
) extends Defn:
  override def mapLocals(f: Local => Local): ClsLikeDefn =
    ClsLikeDefn(sym, k, methods.map(_.mapLocals(f)), fields, ctor.mapLocals(f))

/* Represents either unreachable code (for functions that must return a result)
 * or the end of a non-returning function or a REPL block */
case class End(msg: Str = "") extends BlockTail with ProductWithTail

enum Case:
  case Lit(lit: Literal)
  case Cls(cls: ClassSymbol | ModuleSymbol, path: Path)
  case Tup(len: Int, inf: Bool)

sealed abstract class Result:
  def mapLocals(f: Local => Local): Result
  
// type Local = LocalSymbol
type Local = Symbol

case class Call(fun: Path, args: Ls[Path]) extends Result:
  override def mapLocals(f: Local => Local) = Call(fun.mapLocals(f), args.map(_.mapLocals(f)))

case class Instantiate(cls: Path, args: Ls[Path]) extends Result:
  def mapLocals(f: Local => Local): Instantiate = Instantiate(cls, args.map(_.mapLocals(f)))

abstract class Path extends Result:
  override def mapLocals(f: Local => Local): Path

case class Select(qual: Path, name: Tree.Ident) extends Path:
  override def mapLocals(f: Local => Local) = Select(qual.mapLocals(f), name)

enum Value extends Path:
  case Ref(l: Local)
  case This(sym: InnerSymbol) // TODO rm – just use Ref
  case Lit(lit: Literal)
  case Lam(params: Ls[Param], body: Block)
  case Arr(elems: Ls[Path])

  override def mapLocals(f: Local => Local): Value = this match
    case Ref(l) => Ref(f(l))
    case This(sym) => Ref(f(sym))
    case Lit(lit) => this
    case Lam(params, body) => Lam(params, body.mapLocals(f))
    case Arr(elems) => Arr(elems.map(_.mapLocals(f)))
