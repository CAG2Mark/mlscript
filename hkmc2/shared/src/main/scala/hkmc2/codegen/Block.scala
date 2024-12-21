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
    case Break(_) => Set.empty
    case Continue(_) => Set.empty
    case Define(defn, rst) => rst.definedVars
    case HandleBlock(lhs, res, cls, hdr, bod, rst) => bod.definedVars ++ rst.definedVars + lhs
    case HandleBlockReturn(_) => Set.empty
    case TryBlock(sub, fin, rst) => sub.definedVars ++ fin.definedVars ++ rst.definedVars
    case Label(lbl, bod, rst) => bod.definedVars ++ rst.definedVars
  
  lazy val size: Int = this match
    case _: Return | _: Throw | _: End | _: Break | _: Continue => 1
    case Begin(sub, rst) => sub.size + rst.size
    case Assign(_, _, rst) => 1 + rst.size
    case AssignField(_, _, _, rst) => 1 + rst.size
    case Match(_, arms, dflt, rst) =>
      1 + arms.map(_._2.size).sum + dflt.map(_.size).getOrElse(0) + rst.size
    case Define(_, rst) => 1 + rst.size
    case TryBlock(sub, fin, rst) => 1 + sub.size + fin.size + rst.size
    case Label(_, bod, rst) => 1 + bod.size + rst.size
  
  // ignoring blocks inside functions and handle block
  def map(f: Block => Block): Block = this match
    case _: Return | _: Throw | _: End | _: Break | _: Continue | _: HandleBlockReturn => this
    case Match(scrut, arms, dflt, rst) => Match(scrut, arms.map(_ -> f(_)), dflt.map(f), f(rst))
    case Label(lbl, bod, rst) => Label(lbl, f(bod), f(rst))
    case Begin(sub, rst) => Begin(f(sub), f(rst))
    case TryBlock(sub, fin, rst) => TryBlock(f(sub), f(fin), f(rst))
    case Assign(l, r, rst) => Assign(l, r, f(rst))
    case b @ AssignField(l, n, r, rst) => AssignField(l, n, r, f(rst))(b.symbol)
    case Define(defn, rst) => Define(defn, f(rst))
    case HandleBlock(l, res, cls, hdr, bod, rst) => HandleBlock(l, res, cls, hdr, bod, f(rst))
  
  def mapResult(f: Result => Opt[(Result => Block) => Block]): Block = this match
    case Return(res, implct) => f(res).map(_(Return(_, implct))).getOrElse(this)
    case Throw(exc) => f(exc).map(_(Throw(_))).getOrElse(this)
    case Assign(l, r, rst) => f(r).map(_(Assign(l, _, rst))).getOrElse(this)
    case b @ AssignField(l, n, r, rst) => f(r).map(_(AssignField(l, n, _, rst)(b.symbol))).getOrElse(this)
    case HandleBlockReturn(res) => f(res).map(_(HandleBlockReturn(_))).getOrElse(this)
    case _: End | _: Break | _: Continue | _: Match | _: Label | _: Begin | _: TryBlock | _: Define | _: HandleBlock | _: HandleBlockReturn => this
  
  def mapPath(f: Path => Path): Block = this match
    case Return(res: Path, implct) => Return(f(res), implct)
    case Throw(exc: Path) => Throw(f(exc))
    case Assign(l, r: Path, rst) => Assign(l, f(r), rst)
    case b @ AssignField(l, n, r: Path, rst) => AssignField(l, n, f(r), rst)(b.symbol)
    case Match(scrut: Path, arms, dflt, rst) => Match(f(scrut), arms, dflt, rst)
    case Define(ValDefn(owner, k, sym, rhs: Path), rst) => Define(ValDefn(owner, k, sym, f(rhs)), rst)
    case HandleBlockReturn(res: Path) => HandleBlockReturn(f(res))
    case _: Return | _: Throw | _: Assign | _: AssignField | _: End | _: Break | _: Continue | _: Match | _: Label | _: Begin | _: TryBlock | _: Define | _: HandleBlock | _: HandleBlockReturn => this.mapResult {
      case r @ Call(fun, args) => S(_(Call(f(fun), args.map(arg => Arg(arg.spread, f(arg.value))))(r.isMlsFun)))
      case r @ Instantiate(cls, args) => S(_(Instantiate(f(cls), args.map(f))))
      case r => N
    }
  
  def mapValue(f: Value => Value): Block =
    def go(p: Path): Path = p match
      case sel: Select => Select(go(sel.qual), sel.name)(sel.symbol)
      case v: Value => f(v)
    this.mapPath(go)
  
  // TODO conserve if no changes
  def mapTail(f: BlockTail => BlockTail): Block = this match
    case b: BlockTail => f(b)
    case Begin(sub, rst) => Begin(sub, rst.mapTail(f))
    case Assign(lhs, rhs, rst) => Assign(lhs, rhs, rst.mapTail(f))
    case Define(defn, rst) => Define(defn, rst.mapTail(f))
    case HandleBlock(lhs, res, cls, handlers, body, rest) =>
      HandleBlock(lhs, res, cls, handlers.map(h => Handler(h.sym, h.resumeSym, h.params, h.body.mapTail(f))), body.mapTail(f), rest.mapTail(f))
    case Match(scrut, arms, dflt, rst) =>
      Match(scrut, arms.map(_ -> _.mapTail(f)), dflt.map(_.mapTail(f)), rst.mapTail(f))
  
end Block

sealed abstract class BlockTail extends Block

case class Match(
  scrut: Path,
  arms: Ls[Case -> Block],
  dflt: Opt[Block],
  rest: Block,
) extends Block with ProductWithTail

// * `implct`: whether it's a JS implicit return, without the `return` keyword
// * TODO could just remove this flag and add a flag in Scope instead
case class Return(res: Result, implct: Bool) extends BlockTail

case class Throw(exc: Result) extends BlockTail

case class Label(label: Local, body: Block, rest: Block) extends BlockTail

case class Break(label: Local) extends BlockTail
case class Continue(label: Local) extends BlockTail

// TODO: remove this form?
case class Begin(sub: Block, rest: Block) extends Block with ProductWithTail

case class TryBlock(sub: Block, finallyDo: Block, rest: Block) extends Block with ProductWithTail

case class Assign(lhs: Local, rhs: Result, rest: Block) extends Block with ProductWithTail
// case class Assign(lhs: Path, rhs: Result, rest: Block) extends Block with ProductWithTail

case class AssignField(lhs: Path, nme: Tree.Ident, rhs: Result, rest: Block)(val symbol: Opt[FieldSymbol]) extends Block with ProductWithTail

case class Define(defn: Defn, rest: Block) extends Block with ProductWithTail

case class HandleBlock(lhs: Local, res: Local, cls: Path, handlers: Ls[Handler], body: Block, rest: Block) extends Block with ProductWithTail
case class HandleBlockReturn(res: Result) extends BlockTail

sealed abstract class Defn:
  val sym: MemberSymbol[?]

final case class FunDefn(
    sym: BlockMemberSymbol,
    params: Ls[ParamList],
    body: Block,
) extends Defn

final case class ValDefn(
    owner: Opt[InnerSymbol],
    k: syntax.Val,
    sym: BlockMemberSymbol,
    rhs: Path,
) extends Defn

final case class ClsLikeDefn(
  sym: MemberSymbol[? <: ClassLikeDef],
  k: syntax.ClsLikeKind,
  parentSym: Opt[Path],
  methods: Ls[FunDefn],
  privateFields: Ls[TermSymbol],
  publicFields: Ls[TermDefinition],
  preCtor: Block,
  ctor: Block,
) extends Defn

final case class Handler(
    sym: BlockMemberSymbol,
    resumeSym: LocalSymbol & NamedSymbol,
    params: Ls[ParamList],
    body: Block,
)

/* Represents either unreachable code (for functions that must return a result)
 * or the end of a non-returning function or a REPL block */
case class End(msg: Str = "") extends BlockTail with ProductWithTail

enum Case:
  case Lit(lit: Literal)
  case Cls(cls: ClassSymbol | ModuleSymbol, path: Path)
  case Tup(len: Int, inf: Bool)

sealed abstract class Result

// type Local = LocalSymbol
type Local = Symbol

case class Call(fun: Path, args: Ls[Arg])(val isMlsFun: Bool) extends Result

case class Instantiate(cls: Path, args: Ls[Path]) extends Result

sealed abstract class Path extends Result

case class Select(qual: Path, name: Tree.Ident)(val symbol: Opt[FieldSymbol]) extends Path with ProductWithExtraInfo:
  def extraInfo: Str = symbol.mkString

enum Value extends Path:
  case Ref(l: Local)
  case This(sym: InnerSymbol) // TODO rm – just use Ref
  case Lit(lit: Literal)
  case Lam(params: ParamList, body: Block)
  case Arr(elems: Ls[Arg])

case class Arg(spread: Bool, value: Path)

