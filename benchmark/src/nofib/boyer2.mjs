import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let boyer21;
boyer21 = class boyer2 {
  static #statement;
  static #rules;
  static #lemmas;
  static {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75, tmp76, tmp77, tmp78, tmp79, tmp80, tmp81, tmp82, tmp83, tmp84, tmp85, tmp86, tmp87, tmp88, tmp89, tmp90, tmp91, tmp92, tmp93, tmp94, tmp95, tmp96, tmp97, tmp98, tmp99, tmp100, tmp101, tmp102, tmp103, tmp104, tmp105, tmp106, tmp107, tmp108, tmp109, tmp110, tmp111, tmp112, tmp113, tmp114, tmp115, tmp116, tmp117, tmp118, tmp119, tmp120, tmp121, tmp122, tmp123, tmp124, tmp125, tmp126, tmp127, tmp128, tmp129, tmp130, tmp131, tmp132, tmp133, tmp134, tmp135, tmp136, tmp137, tmp138, tmp139, tmp140, tmp141, tmp142, tmp143, tmp144, tmp145, tmp146, tmp147, tmp148, tmp149, tmp150, tmp151, tmp152, tmp153, tmp154, tmp155, tmp156, tmp157, tmp158, tmp159, tmp160, tmp161, tmp162, tmp163, tmp164, tmp165, tmp166, tmp167, tmp168, tmp169, tmp170, tmp171, tmp172, tmp173, tmp174, tmp175, tmp176, tmp177, tmp178, tmp179, tmp180, tmp181, tmp182, tmp183, tmp184, tmp185, tmp186, tmp187, tmp188, tmp189, tmp190, tmp191, tmp192, tmp193, tmp194, tmp195, tmp196, tmp197, tmp198, tmp199, tmp200, tmp201, tmp202, tmp203, tmp204, tmp205, tmp206, tmp207, tmp208, tmp209, tmp210, tmp211, tmp212, tmp213, tmp214, tmp215, tmp216, lambda;
    this.Lisplist = class Lisplist {
      constructor() {}
      toString() { return "Lisplist"; }
    };
    const Nill$class = class Nill extends boyer2.Lisplist {
      constructor() {
        super();
      }
      toString() { return "Nill"; }
    };
    this.Nill = new Nill$class;
    this.Nill.class = Nill$class;
    this.Atom = function Atom(a1) {
      return new Atom.class(a1);
    };
    this.Atom.class = class Atom extends boyer2.Lisplist {
      constructor(a) {
        super();
        this.a = a;
      }
      toString() { return "Atom(" + globalThis.Predef.render(this.a) + ")"; }
    };
    this.Conss = function Conss(a1) {
      return new Conss.class(a1);
    };
    this.Conss.class = class Conss extends boyer2.Lisplist {
      constructor(a) {
        super();
        this.a = a;
      }
      toString() { return "Conss(" + globalThis.Predef.render(this.a) + ")"; }
    };
    this.LUT = class LUT {
      constructor() {}
      toString() { return "LUT"; }
    };
    const Empty$class = class Empty extends boyer2.LUT {
      constructor() {
        super();
      }
      toString() { return "Empty"; }
    };
    this.Empty = new Empty$class;
    this.Empty.class = Empty$class;
    this.Node = function Node(x1) {
      return new Node.class(x1);
    };
    this.Node.class = class Node extends boyer2.LUT {
      constructor(x) {
        super();
        this.x = x;
      }
      toString() { return "Node(" + globalThis.Predef.render(this.x) + ")"; }
    };
    tmp = NofibPrelude.nofibStringToList("( implies ( and ( implies x y )( and ( implies y z )( and ( implies z u )( implies u w ) ) ) )( implies x w ) )");
    tmp1 = boyer2.strToToken(tmp);
    tmp2 = boyer2.mkLispList(tmp1);
    boyer2.#statement = tmp2;
    tmp3 = NofibPrelude.nofibStringToList("(equal (compile form)(reverse (codegen (optimize form) (Nill) ) ) )");
    tmp4 = NofibPrelude.nofibStringToList("(equal (eqp x y)(equal (fix x)(fix y) ) )");
    tmp5 = NofibPrelude.nofibStringToList("(equal (greaterp x y)(lessp y x) )");
    tmp6 = NofibPrelude.nofibStringToList("(equal (lesseqp x y)(not (lessp y x) ) )");
    tmp7 = NofibPrelude.nofibStringToList("(equal (greatereqp x y)(not (lessp y x) ) )");
    tmp8 = NofibPrelude.nofibStringToList("(equal (boolean x)(or (equal x (t) )(equal x (f) ) )");
    tmp9 = NofibPrelude.nofibStringToList("(equal (iff x y)(and (implies x y)(implies y x) ) )");
    tmp10 = NofibPrelude.nofibStringToList("(equal (even1 x)(if (zerop x)(t)(odd (1- x) ) ) )");
    tmp11 = NofibPrelude.nofibStringToList("(equal (countps- l pred)(countps-loop l pred (zero) ) )");
    tmp12 = NofibPrelude.nofibStringToList("(equal (fact- i)(fact-loop i 1) )");
    tmp13 = NofibPrelude.nofibStringToList("(equal (reverse- x)(reverse-loop x (Nill) ) )");
    tmp14 = NofibPrelude.nofibStringToList("(equal (divides x y)(zerop (remainder y x) ) )");
    tmp15 = NofibPrelude.nofibStringToList("(equal (assume-true var alist)(Conss (Conss var (t) )alist) )");
    tmp16 = NofibPrelude.nofibStringToList("(equal (assume-false var alist)(Conss (Conss var (f) )alist) )");
    tmp17 = NofibPrelude.nofibStringToList("(equal (tautology-checker x)(tautologyp (normalize x)(Nill) ) )");
    tmp18 = NofibPrelude.nofibStringToList("(equal (falsify x)(falsify1 (normalize x)(Nill) ) )");
    tmp19 = NofibPrelude.nofibStringToList("(equal (prime x)(and (not (zerop x))(not (equal x (add1 (zero) ) ) )(prime1 x (1- x) ) ) )");
    tmp20 = NofibPrelude.nofibStringToList("(equal (and p q)(if p (if q (t) (f) ) (f) ) )");
    tmp21 = NofibPrelude.nofibStringToList("(equal (or p q)(if p (t) (if q (t) (f) ) ) )");
    tmp22 = NofibPrelude.nofibStringToList("(equal (not p)(if p (f) (t) ) )");
    tmp23 = NofibPrelude.nofibStringToList("(equal (implies p q)(if p (if q (t) (f) ) (t) ) )");
    tmp24 = NofibPrelude.nofibStringToList("(equal (fix x)(if (numberp x) x (zero) ) )");
    tmp25 = NofibPrelude.nofibStringToList("(equal (if (if a b c) d e)(if a (if b d e) (if c d e) ) )");
    tmp26 = NofibPrelude.nofibStringToList("(equal (zerop x)(or (equal x (zero) )(not (numberp x) ) ) )");
    tmp27 = NofibPrelude.nofibStringToList("(equal (plus (plus x y) z )(plus x (plus y z) ) )");
    tmp28 = NofibPrelude.nofibStringToList("(equal (equal (plus a b) (zero ) )(and (zerop a) (zerop b) ) )");
    tmp29 = NofibPrelude.nofibStringToList("(equal (difference x x)(zero) )");
    tmp30 = NofibPrelude.nofibStringToList("(equal (equal (plus a b) (plus a c) )(equal (fix b) (fix c) ) )");
    tmp31 = NofibPrelude.nofibStringToList("(equal (equal (zero) (difference x y) )(not (lessp y x) ) )");
    tmp32 = NofibPrelude.nofibStringToList("(equal (equal x (difference x y) )(and (numberp x)(or (equal x (zero) )(zerop y) ) ) )");
    tmp33 = NofibPrelude.nofibStringToList("(equal (meaning (plus-tree (append x y) ) a)(plus (meaning (plus-tree x) a)(meaning (plus-tree y) a) ) )");
    tmp34 = NofibPrelude.nofibStringToList("(equal (meaning (plus-tree (plus-fringe x) ) a)(fix (meaning x a) ) )");
    tmp35 = NofibPrelude.nofibStringToList("(equal (append (append x y) z)(append x (append y z) ) )");
    tmp36 = NofibPrelude.nofibStringToList("(equal (reverse (append a b) )(append (reverse b) (reverse a) ) )");
    tmp37 = NofibPrelude.nofibStringToList("(equal (times x (plus y z) )(plus (times x y)(times x z) ) )");
    tmp38 = NofibPrelude.nofibStringToList("(equal (times (times x y) z)(times x (times y z) ) )");
    tmp39 = NofibPrelude.nofibStringToList("(equal (equal (times x y) (zero) )(or (zerop x)(zerop y) ) )");
    tmp40 = NofibPrelude.nofibStringToList("(equal (exec (append x y)pds envrn)(exec y (exec x pds envrn)envrn) )");
    tmp41 = NofibPrelude.nofibStringToList("(equal (mc-flatten x y)(append (flatten x)y) )");
    tmp42 = NofibPrelude.nofibStringToList("(equal (member x (append a b) )(or (member x a)(member x b) ) )");
    tmp43 = NofibPrelude.nofibStringToList("(equal (member x (reverse y) )(member x y) )");
    tmp44 = NofibPrelude.nofibStringToList("(equal (length (reverse x) )(length x) )");
    tmp45 = NofibPrelude.nofibStringToList("(equal (member a (intersect b c) )(and (member a b)(member a c) ) )");
    tmp46 = NofibPrelude.nofibStringToList("(equal (nth (zero)i)(zero) )");
    tmp47 = NofibPrelude.nofibStringToList("(equal (exp i (plus j k) )(times (exp i j)(exp i k) ) )");
    tmp48 = NofibPrelude.nofibStringToList("(equal (exp i (times j k) )(exp (exp i j)k) )");
    tmp49 = NofibPrelude.nofibStringToList("(equal (reverse-loop x y)(append (reverse x)y) )");
    tmp50 = NofibPrelude.nofibStringToList("(equal (reverse-loop x (Nill) )(reverse x) )");
    tmp51 = NofibPrelude.nofibStringToList("(equal (count-list z (sort-lp x y) )(plus (count-list z x)(count-list z y) ) )");
    tmp52 = NofibPrelude.nofibStringToList("(equal (equal (append a b)(append a c) )(equal b c) )");
    tmp53 = NofibPrelude.nofibStringToList("(equal (plus (remainder x y)(times y (quotient x y) ) )(fix x) )");
    tmp54 = NofibPrelude.nofibStringToList("(equal (power-eval (big-plus1 l i base)base)(plus (power-eval l base)i) )");
    tmp55 = NofibPrelude.nofibStringToList("(equal (power-eval (big-plus x y i base)base)(plus i (plus (power-eval x base)(power-eval y base) ) ) )");
    tmp56 = NofibPrelude.nofibStringToList("(equal (remainder y 1)(zero) )");
    tmp57 = NofibPrelude.nofibStringToList("(equal (lessp (remainder x y)y)(not (zerop y) ) )");
    tmp58 = NofibPrelude.nofibStringToList("(equal (remainder x x)(zero) )");
    tmp59 = NofibPrelude.nofibStringToList("(equal (lessp (quotient i j)i)(and (not (zerop i) )(or (zerop j)(not (equal j 1) ) ) ) )");
    tmp60 = NofibPrelude.nofibStringToList("(equal (lessp (remainder x y)x)(and (not (zerop y) )(not (zerop x) )(not (lessp x y) ) ) )");
    tmp61 = NofibPrelude.nofibStringToList("(equal (power-eval (power-rep i base)base)(fix i) )");
    tmp62 = NofibPrelude.nofibStringToList("(equal (power-eval (big-plus (power-rep i base)(power-rep j base)(zero)base)base)(plus i j) )");
    tmp63 = NofibPrelude.nofibStringToList("(equal (gcd x y)(gcd y x) )");
    tmp64 = NofibPrelude.nofibStringToList("(equal (nth (append a b)i)(append (nth a i)(nth b (difference i (length a) ) ) ) )");
    tmp65 = NofibPrelude.nofibStringToList("(equal (difference (plus x y)x)(fix y) )");
    tmp66 = NofibPrelude.nofibStringToList("(equal (difference (plus y x)x)(fix y) )");
    tmp67 = NofibPrelude.nofibStringToList("(equal (difference (plus x y)(plus x z) )(difference y z) )");
    tmp68 = NofibPrelude.nofibStringToList("(equal (times x (difference c w) )(difference (times c x)(times w x) ) )");
    tmp69 = NofibPrelude.nofibStringToList("(equal (remainder (times x z)z)(zero) )");
    tmp70 = NofibPrelude.nofibStringToList("(equal (difference (plus b (plus a c) )a)(plus b c) )");
    tmp71 = NofibPrelude.nofibStringToList("(equal (difference (add1 (plus y z)z)(add1 y) )");
    tmp72 = NofibPrelude.nofibStringToList("(equal (lessp (plus x y)(plus x z ) )(lessp y z) )");
    tmp73 = NofibPrelude.nofibStringToList("(equal (lessp (times x z)(times y z) )(and (not (zerop z) )(lessp x y) ) )");
    tmp74 = NofibPrelude.nofibStringToList("(equal (lessp y (plus x y) )(not (zerop x) ) )");
    tmp75 = NofibPrelude.nofibStringToList("(equal (gcd (times x z)(times y z) )(times z (gcd x y) ) )");
    tmp76 = NofibPrelude.nofibStringToList("(equal (value (normalize x)a)(value x a) )");
    tmp77 = NofibPrelude.nofibStringToList("(equal (equal (flatten x)(Conss y (Nill) ) )(and (nlistp x)(equal x y) ) )");
    tmp78 = NofibPrelude.nofibStringToList("(equal (listp (gopher x) )(listp x) )");
    tmp79 = NofibPrelude.nofibStringToList("(equal (samefringe x y)(equal (flatten x)(flatten y) ) )");
    tmp80 = NofibPrelude.nofibStringToList("(equal (equal (greatest-factor x y)(zero) )(and (or (zerop y)(equal y 1) )(equal x (zero) ) ) )");
    tmp81 = NofibPrelude.nofibStringToList("(equal (equal (greatest-factor x y)1)(equal x 1) )");
    tmp82 = NofibPrelude.nofibStringToList("(equal (numberp (greatest-factor x y) )(not (and (or (zerop y)(equal y 1) )(not (numberp x) ) ) ) )");
    tmp83 = NofibPrelude.nofibStringToList("(equal (times-list (append x y) )(times (times-list x)(times-list y) ) )");
    tmp84 = NofibPrelude.nofibStringToList("(equal (prime-list (append x y) )(and (prime-list x)(prime-list y) ) )");
    tmp85 = NofibPrelude.nofibStringToList("(equal (equal z (times w z) )(and (numberp z)(or (equal z (zero) )(equal w 1) ) ) )");
    tmp86 = NofibPrelude.nofibStringToList("(equal (greatereqpr x y)(not (lessp x y) ) )");
    tmp87 = NofibPrelude.nofibStringToList("(equal (equal x (times x y) )(or (equal x (zero) )(and (numberp x)(equal y 1) ) ) )");
    tmp88 = NofibPrelude.nofibStringToList("(equal (remainder (times y x)y)(zero) )");
    tmp89 = NofibPrelude.nofibStringToList("(equal (equal (times a b)1)(and (not (equal a (zero) ) )(not (equal b (zero) ) )(numberp a)(numberp b)(equal (1- a)(zero) )(equal (1- b)(zero) ) ) )");
    tmp90 = NofibPrelude.nofibStringToList("(equal (lessp (length (delete x l) )(length l) )(member x l) )");
    tmp91 = NofibPrelude.nofibStringToList("(equal (sort2 (delete x l) )(delete x (sort2 l) ) )");
    tmp92 = NofibPrelude.nofibStringToList("(equal (dsort x)(sort2 x) )");
    tmp93 = NofibPrelude.nofibStringToList("(equal (length(Conss x1(Conss x2(Conss x3(Conss x4(Conss x5(Conss x6 x7) ) ) ) ) ) )(plus 6 (length x7) ) )");
    tmp94 = NofibPrelude.nofibStringToList("(equal (difference (add1 (add1 x) )2)(fix x) )");
    tmp95 = NofibPrelude.nofibStringToList("(equal (quotient (plus x (plus x y) )2)(plus x (quotient y 2) ) )");
    tmp96 = NofibPrelude.nofibStringToList("(equal (sigma (zero)i)(quotient (times i (add1 i) )2) )");
    tmp97 = NofibPrelude.nofibStringToList("(equal (plus x (add1 y) )(if (numberp y)(add1 (plus x y) )(add1 x) ) )");
    tmp98 = NofibPrelude.nofibStringToList("(equal (equal (difference x y)(difference z y) )(if (lessp x y)(not (lessp y z) )(if (lessp z y)(not (lessp y x) )(equal (fix x)(fix z) ) ) ) )");
    tmp99 = NofibPrelude.nofibStringToList("(equal (meaning (plus-tree (delete x y) )a)(if (member x y)(difference (meaning (plus-tree y)a)(meaning x a) )(meaning (plus-tree y)a) ) )");
    tmp100 = NofibPrelude.nofibStringToList("(equal (times x (add1 y) )(if (numberp y)(plus x (times x y) )(fix x) ) )");
    tmp101 = NofibPrelude.nofibStringToList("(equal (nth (Nill)i)(if (zerop i)(Nill)(zero) ) )");
    tmp102 = NofibPrelude.nofibStringToList("(equal (last (append a b) )(if (listp b)(last b)(if (listp a)(Conss (car (last a) )b)b) ) )");
    tmp103 = NofibPrelude.nofibStringToList("(equal (equal (lessp x y)z)(if (lessp x y)(equal t z)(equal f z) ) )");
    tmp104 = NofibPrelude.nofibStringToList("(equal (assignment x (append a b) )(if (assignedp x a)(assignment x a)(assignment x b) ) )");
    tmp105 = NofibPrelude.nofibStringToList("(equal (car (gopher x) )(if (listp x)(car (flatten x) )(zero) ) )");
    tmp106 = NofibPrelude.nofibStringToList("(equal (flatten (cdr (gopher x) ) )(if (listp x)(cdr (flatten x) )(Conss (zero)(Nill) ) ) )");
    tmp107 = NofibPrelude.nofibStringToList("(equal (quotient (times y x)y)(if (zerop y)(zero)(fix x) ) )");
    tmp108 = NofibPrelude.nofibStringToList("(equal (get j (set i val mem) )(if (eqp j i)val(get j mem) ) )");
    tmp109 = NofibPrelude.Cons(tmp108, NofibPrelude.Nil);
    tmp110 = NofibPrelude.Cons(tmp107, tmp109);
    tmp111 = NofibPrelude.Cons(tmp106, tmp110);
    tmp112 = NofibPrelude.Cons(tmp105, tmp111);
    tmp113 = NofibPrelude.Cons(tmp104, tmp112);
    tmp114 = NofibPrelude.Cons(tmp103, tmp113);
    tmp115 = NofibPrelude.Cons(tmp102, tmp114);
    tmp116 = NofibPrelude.Cons(tmp101, tmp115);
    tmp117 = NofibPrelude.Cons(tmp100, tmp116);
    tmp118 = NofibPrelude.Cons(tmp99, tmp117);
    tmp119 = NofibPrelude.Cons(tmp98, tmp118);
    tmp120 = NofibPrelude.Cons(tmp97, tmp119);
    tmp121 = NofibPrelude.Cons(tmp96, tmp120);
    tmp122 = NofibPrelude.Cons(tmp95, tmp121);
    tmp123 = NofibPrelude.Cons(tmp94, tmp122);
    tmp124 = NofibPrelude.Cons(tmp93, tmp123);
    tmp125 = NofibPrelude.Cons(tmp92, tmp124);
    tmp126 = NofibPrelude.Cons(tmp91, tmp125);
    tmp127 = NofibPrelude.Cons(tmp90, tmp126);
    tmp128 = NofibPrelude.Cons(tmp89, tmp127);
    tmp129 = NofibPrelude.Cons(tmp88, tmp128);
    tmp130 = NofibPrelude.Cons(tmp87, tmp129);
    tmp131 = NofibPrelude.Cons(tmp86, tmp130);
    tmp132 = NofibPrelude.Cons(tmp85, tmp131);
    tmp133 = NofibPrelude.Cons(tmp84, tmp132);
    tmp134 = NofibPrelude.Cons(tmp83, tmp133);
    tmp135 = NofibPrelude.Cons(tmp82, tmp134);
    tmp136 = NofibPrelude.Cons(tmp81, tmp135);
    tmp137 = NofibPrelude.Cons(tmp80, tmp136);
    tmp138 = NofibPrelude.Cons(tmp79, tmp137);
    tmp139 = NofibPrelude.Cons(tmp78, tmp138);
    tmp140 = NofibPrelude.Cons(tmp77, tmp139);
    tmp141 = NofibPrelude.Cons(tmp76, tmp140);
    tmp142 = NofibPrelude.Cons(tmp75, tmp141);
    tmp143 = NofibPrelude.Cons(tmp74, tmp142);
    tmp144 = NofibPrelude.Cons(tmp73, tmp143);
    tmp145 = NofibPrelude.Cons(tmp72, tmp144);
    tmp146 = NofibPrelude.Cons(tmp71, tmp145);
    tmp147 = NofibPrelude.Cons(tmp70, tmp146);
    tmp148 = NofibPrelude.Cons(tmp69, tmp147);
    tmp149 = NofibPrelude.Cons(tmp68, tmp148);
    tmp150 = NofibPrelude.Cons(tmp67, tmp149);
    tmp151 = NofibPrelude.Cons(tmp66, tmp150);
    tmp152 = NofibPrelude.Cons(tmp65, tmp151);
    tmp153 = NofibPrelude.Cons(tmp64, tmp152);
    tmp154 = NofibPrelude.Cons(tmp63, tmp153);
    tmp155 = NofibPrelude.Cons(tmp62, tmp154);
    tmp156 = NofibPrelude.Cons(tmp61, tmp155);
    tmp157 = NofibPrelude.Cons(tmp60, tmp156);
    tmp158 = NofibPrelude.Cons(tmp59, tmp157);
    tmp159 = NofibPrelude.Cons(tmp58, tmp158);
    tmp160 = NofibPrelude.Cons(tmp57, tmp159);
    tmp161 = NofibPrelude.Cons(tmp56, tmp160);
    tmp162 = NofibPrelude.Cons(tmp55, tmp161);
    tmp163 = NofibPrelude.Cons(tmp54, tmp162);
    tmp164 = NofibPrelude.Cons(tmp53, tmp163);
    tmp165 = NofibPrelude.Cons(tmp52, tmp164);
    tmp166 = NofibPrelude.Cons(tmp51, tmp165);
    tmp167 = NofibPrelude.Cons(tmp50, tmp166);
    tmp168 = NofibPrelude.Cons(tmp49, tmp167);
    tmp169 = NofibPrelude.Cons(tmp48, tmp168);
    tmp170 = NofibPrelude.Cons(tmp47, tmp169);
    tmp171 = NofibPrelude.Cons(tmp46, tmp170);
    tmp172 = NofibPrelude.Cons(tmp45, tmp171);
    tmp173 = NofibPrelude.Cons(tmp44, tmp172);
    tmp174 = NofibPrelude.Cons(tmp43, tmp173);
    tmp175 = NofibPrelude.Cons(tmp42, tmp174);
    tmp176 = NofibPrelude.Cons(tmp41, tmp175);
    tmp177 = NofibPrelude.Cons(tmp40, tmp176);
    tmp178 = NofibPrelude.Cons(tmp39, tmp177);
    tmp179 = NofibPrelude.Cons(tmp38, tmp178);
    tmp180 = NofibPrelude.Cons(tmp37, tmp179);
    tmp181 = NofibPrelude.Cons(tmp36, tmp180);
    tmp182 = NofibPrelude.Cons(tmp35, tmp181);
    tmp183 = NofibPrelude.Cons(tmp34, tmp182);
    tmp184 = NofibPrelude.Cons(tmp33, tmp183);
    tmp185 = NofibPrelude.Cons(tmp32, tmp184);
    tmp186 = NofibPrelude.Cons(tmp31, tmp185);
    tmp187 = NofibPrelude.Cons(tmp30, tmp186);
    tmp188 = NofibPrelude.Cons(tmp29, tmp187);
    tmp189 = NofibPrelude.Cons(tmp28, tmp188);
    tmp190 = NofibPrelude.Cons(tmp27, tmp189);
    tmp191 = NofibPrelude.Cons(tmp26, tmp190);
    tmp192 = NofibPrelude.Cons(tmp25, tmp191);
    tmp193 = NofibPrelude.Cons(tmp24, tmp192);
    tmp194 = NofibPrelude.Cons(tmp23, tmp193);
    tmp195 = NofibPrelude.Cons(tmp22, tmp194);
    tmp196 = NofibPrelude.Cons(tmp21, tmp195);
    tmp197 = NofibPrelude.Cons(tmp20, tmp196);
    tmp198 = NofibPrelude.Cons(tmp19, tmp197);
    tmp199 = NofibPrelude.Cons(tmp18, tmp198);
    tmp200 = NofibPrelude.Cons(tmp17, tmp199);
    tmp201 = NofibPrelude.Cons(tmp16, tmp200);
    tmp202 = NofibPrelude.Cons(tmp15, tmp201);
    tmp203 = NofibPrelude.Cons(tmp14, tmp202);
    tmp204 = NofibPrelude.Cons(tmp13, tmp203);
    tmp205 = NofibPrelude.Cons(tmp12, tmp204);
    tmp206 = NofibPrelude.Cons(tmp11, tmp205);
    tmp207 = NofibPrelude.Cons(tmp10, tmp206);
    tmp208 = NofibPrelude.Cons(tmp9, tmp207);
    tmp209 = NofibPrelude.Cons(tmp8, tmp208);
    tmp210 = NofibPrelude.Cons(tmp7, tmp209);
    tmp211 = NofibPrelude.Cons(tmp6, tmp210);
    tmp212 = NofibPrelude.Cons(tmp5, tmp211);
    tmp213 = NofibPrelude.Cons(tmp4, tmp212);
    tmp214 = NofibPrelude.Cons(tmp3, tmp213);
    boyer2.#rules = tmp214;
    tmp215 = boyer2.makelemmas(boyer2.#rules);
    tmp216 = boyer2.addlemmalst(tmp215, boyer2.Empty);
    boyer2.#lemmas = tmp216;
    lambda = (undefined, function () {
      return boyer2.testBoyer2_nofib(3)
    });
    BenchmarkPrelude.benchmark(lambda)
  }
  static lispListEq(x, y) {
    let param0, first1, first0, a, b, param01, first11, first01, c, d, scrut, param02, a1, param03, b1;
    if (x instanceof boyer2.Nill.class) {
      if (y instanceof boyer2.Nill.class) {
        return true
      } else {
        return false
      }
    } else if (x instanceof boyer2.Atom.class) {
      param02 = x.a;
      a1 = param02;
      if (y instanceof boyer2.Atom.class) {
        param03 = y.a;
        b1 = param03;
        return NofibPrelude.listEq(a1, b1)
      } else {
        return false
      }
    } else if (x instanceof boyer2.Conss.class) {
      param0 = x.a;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        a = first0;
        b = first1;
        if (y instanceof boyer2.Conss.class) {
          param01 = y.a;
          if (globalThis.Array.isArray(param01) && param01.length === 2) {
            first01 = param01[0];
            first11 = param01[1];
            c = first01;
            d = first11;
            scrut = boyer2.lispListEq(a, c);
            if (scrut === true) {
              return boyer2.lispListEq(b, d)
            } else {
              return false
            }
          } else {
            return false
          }
        } else {
          return false
        }
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static lispmember(e_x) {
    let first1, first0, e, param0, first11, first01, x1, xs, scrut;
    if (globalThis.Array.isArray(e_x) && e_x.length === 2) {
      first0 = e_x[0];
      first1 = e_x[1];
      e = first0;
      if (first1 instanceof boyer2.Conss.class) {
        param0 = first1.a;
        if (globalThis.Array.isArray(param0) && param0.length === 2) {
          first01 = param0[0];
          first11 = param0[1];
          x1 = first01;
          xs = first11;
          scrut = boyer2.lispListEq(e, x1);
          if (scrut === true) {
            return true
          } else {
            return boyer2.lispmember([
              e,
              xs
            ])
          }
        } else {
          return false
        }
      } else {
        return false
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static truep(term_l) {
    let first1, first0, term, l, param0, first11, first01, param01, param02, param1;
    if (globalThis.Array.isArray(term_l) && term_l.length === 2) {
      first0 = term_l[0];
      first1 = term_l[1];
      if (first0 instanceof boyer2.Nill.class) {
        return false
      } else if (first0 instanceof boyer2.Conss.class) {
        param0 = first0.a;
        if (globalThis.Array.isArray(param0) && param0.length === 2) {
          first01 = param0[0];
          first11 = param0[1];
          if (first01 instanceof boyer2.Atom.class) {
            param01 = first01.a;
            if (param01 instanceof NofibPrelude.Cons.class) {
              param02 = param01.head;
              param1 = param01.tail;
              if (param02 === "t") {
                if (param1 instanceof NofibPrelude.Nil.class) {
                  if (first11 instanceof boyer2.Nill.class) {
                    return true
                  } else {
                    term = first0;
                    l = first1;
                    return boyer2.lispmember([
                      term,
                      l
                    ])
                  }
                } else {
                  term = first0;
                  l = first1;
                  return boyer2.lispmember([
                    term,
                    l
                  ])
                }
              } else {
                term = first0;
                l = first1;
                return boyer2.lispmember([
                  term,
                  l
                ])
              }
            } else {
              term = first0;
              l = first1;
              return boyer2.lispmember([
                term,
                l
              ])
            }
          } else {
            term = first0;
            l = first1;
            return boyer2.lispmember([
              term,
              l
            ])
          }
        } else {
          term = first0;
          l = first1;
          return boyer2.lispmember([
            term,
            l
          ])
        }
      } else {
        term = first0;
        l = first1;
        return boyer2.lispmember([
          term,
          l
        ])
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static falsep(term_l1) {
    let first1, first0, term, l, param0, first11, first01, param01, param02, param1;
    if (globalThis.Array.isArray(term_l1) && term_l1.length === 2) {
      first0 = term_l1[0];
      first1 = term_l1[1];
      if (first0 instanceof boyer2.Nill.class) {
        return false
      } else if (first0 instanceof boyer2.Conss.class) {
        param0 = first0.a;
        if (globalThis.Array.isArray(param0) && param0.length === 2) {
          first01 = param0[0];
          first11 = param0[1];
          if (first01 instanceof boyer2.Atom.class) {
            param01 = first01.a;
            if (param01 instanceof NofibPrelude.Cons.class) {
              param02 = param01.head;
              param1 = param01.tail;
              if (param02 === "f") {
                if (param1 instanceof NofibPrelude.Nil.class) {
                  if (first11 instanceof boyer2.Nill.class) {
                    return true
                  } else {
                    term = first0;
                    l = first1;
                    return boyer2.lispmember([
                      term,
                      l
                    ])
                  }
                } else {
                  term = first0;
                  l = first1;
                  return boyer2.lispmember([
                    term,
                    l
                  ])
                }
              } else {
                term = first0;
                l = first1;
                return boyer2.lispmember([
                  term,
                  l
                ])
              }
            } else {
              term = first0;
              l = first1;
              return boyer2.lispmember([
                term,
                l
              ])
            }
          } else {
            term = first0;
            l = first1;
            return boyer2.lispmember([
              term,
              l
            ])
          }
        } else {
          term = first0;
          l = first1;
          return boyer2.lispmember([
            term,
            l
          ])
        }
      } else {
        term = first0;
        l = first1;
        return boyer2.lispmember([
          term,
          l
        ])
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static tv(x1) {
    let param0, a;
    if (x1 instanceof boyer2.Atom.class) {
      param0 = x1.a;
      a = param0;
      return a
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static atom(x2) {
    let param0;
    if (x2 instanceof boyer2.Atom.class) {
      param0 = x2.a;
      return true
    } else {
      return false
    }
  } 
  static car(x3) {
    let param0, first1, first0, a;
    if (x3 instanceof boyer2.Conss.class) {
      param0 = x3.a;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        a = first0;
        return a
      } else {
        return boyer2.Nill
      }
    } else {
      return boyer2.Nill
    }
  } 
  static cdr(x4) {
    let param0, first1, first0, b;
    if (x4 instanceof boyer2.Conss.class) {
      param0 = x4.a;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        b = first1;
        return b
      } else {
        return boyer2.Nill
      }
    } else {
      return boyer2.Nill
    }
  } 
  static cadr(x5) {
    let tmp;
    tmp = boyer2.cdr(x5);
    return boyer2.car(tmp)
  } 
  static caddr(x6) {
    let tmp, tmp1;
    tmp = boyer2.cdr(x6);
    tmp1 = boyer2.cdr(tmp);
    return boyer2.car(tmp1)
  } 
  static cadddr(x7) {
    let tmp, tmp1, tmp2;
    tmp = boyer2.cdr(x7);
    tmp1 = boyer2.cdr(tmp);
    tmp2 = boyer2.cdr(tmp1);
    return boyer2.car(tmp2)
  } 
  static tautologyp(f_truelst_falselst) {
    let first2, first1, first0, f, truelst, falselst, param0, first11, first01, x8, y1, param01, param02, param1, param03, param11, scrut, scrut1, scrut2, scrut3, scrut4, scrut5, param04, x9, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12;
    if (globalThis.Array.isArray(f_truelst_falselst) && f_truelst_falselst.length === 3) {
      first0 = f_truelst_falselst[0];
      first1 = f_truelst_falselst[1];
      first2 = f_truelst_falselst[2];
      f = first0;
      truelst = first1;
      falselst = first2;
      if (f instanceof boyer2.Nill.class) {
        return false
      } else if (f instanceof boyer2.Atom.class) {
        param04 = f.a;
        x9 = param04;
        tmp = boyer2.Atom(x9);
        return boyer2.truep([
          tmp,
          truelst
        ])
      } else if (f instanceof boyer2.Conss.class) {
        param0 = f.a;
        if (globalThis.Array.isArray(param0) && param0.length === 2) {
          first01 = param0[0];
          first11 = param0[1];
          x8 = first01;
          y1 = first11;
          tmp1 = boyer2.Conss([
            x8,
            y1
          ]);
          scrut5 = boyer2.truep([
            tmp1,
            truelst
          ]);
          if (scrut5 === true) {
            return true
          } else {
            tmp2 = boyer2.Conss([
              x8,
              y1
            ]);
            scrut4 = boyer2.falsep([
              tmp2,
              falselst
            ]);
            if (scrut4 === true) {
              return false
            } else {
              if (x8 instanceof boyer2.Atom.class) {
                param01 = x8.a;
                if (param01 instanceof NofibPrelude.Cons.class) {
                  param02 = param01.head;
                  param1 = param01.tail;
                  if (param02 === "i") {
                    if (param1 instanceof NofibPrelude.Cons.class) {
                      param03 = param1.head;
                      param11 = param1.tail;
                      if (param03 === "f") {
                        if (param11 instanceof NofibPrelude.Nil.class) {
                          tmp3 = boyer2.car(y1);
                          scrut3 = boyer2.truep([
                            tmp3,
                            truelst
                          ]);
                          if (scrut3 === true) {
                            tmp4 = boyer2.cadr(y1);
                            return boyer2.tautologyp([
                              tmp4,
                              truelst,
                              falselst
                            ])
                          } else {
                            tmp5 = boyer2.car(y1);
                            scrut2 = boyer2.falsep([
                              tmp5,
                              falselst
                            ]);
                            if (scrut2 === true) {
                              tmp6 = boyer2.caddr(y1);
                              return boyer2.tautologyp([
                                tmp6,
                                truelst,
                                falselst
                              ])
                            } else {
                              tmp7 = boyer2.cadr(y1);
                              tmp8 = boyer2.car(y1);
                              tmp9 = boyer2.Conss([
                                tmp8,
                                truelst
                              ]);
                              scrut = boyer2.tautologyp([
                                tmp7,
                                tmp9,
                                falselst
                              ]);
                              if (scrut === true) {
                                tmp10 = boyer2.caddr(y1);
                                tmp11 = boyer2.car(y1);
                                tmp12 = boyer2.Conss([
                                  tmp11,
                                  falselst
                                ]);
                                scrut1 = boyer2.tautologyp([
                                  tmp10,
                                  truelst,
                                  tmp12
                                ]);
                                if (scrut1 === true) {
                                  return true
                                } else {
                                  return false
                                }
                              } else {
                                return false
                              }
                            }
                          }
                        } else {
                          return false
                        }
                      } else {
                        return false
                      }
                    } else {
                      return false
                    }
                  } else {
                    return false
                  }
                } else {
                  return false
                }
              } else {
                return false
              }
            }
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static sublist(t) {
    let param0, param1, h, t1, scrut, first1, first0, r, l, param01, param11, t2, t3, scrut1, first11, first01, r1, l1, scrut2, first12, first02, r2, l2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12;
    if (t instanceof NofibPrelude.Nil.class) {
      return [
        NofibPrelude.Nil,
        boyer2.Nill
      ]
    } else if (t instanceof NofibPrelude.Cons.class) {
      param0 = t.head;
      param1 = t.tail;
      if (param0 instanceof NofibPrelude.Cons.class) {
        param01 = param0.head;
        param11 = param0.tail;
        if (param01 === "(") {
          if (param11 instanceof NofibPrelude.Nil.class) {
            t3 = param1;
            scrut1 = boyer2.sublist(t3);
            if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
              first01 = scrut1[0];
              first11 = scrut1[1];
              r1 = first01;
              l1 = first11;
              scrut2 = boyer2.sublist(r1);
              if (globalThis.Array.isArray(scrut2) && scrut2.length === 2) {
                first02 = scrut2[0];
                first12 = scrut2[1];
                r2 = first02;
                l2 = first12;
                tmp = boyer2.Conss([
                  l1,
                  l2
                ]);
                return [
                  r2,
                  tmp
                ]
              } else {
                h = param0;
                t1 = param1;
                scrut = boyer2.sublist(t1);
                if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
                  first0 = scrut[0];
                  first1 = scrut[1];
                  r = first0;
                  l = first1;
                  tmp1 = boyer2.Atom(h);
                  tmp2 = boyer2.Conss([
                    tmp1,
                    l
                  ]);
                  return [
                    r,
                    tmp2
                  ]
                } else {
                  throw new globalThis.Error("match error");
                }
              }
            } else {
              h = param0;
              t1 = param1;
              scrut = boyer2.sublist(t1);
              if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
                first0 = scrut[0];
                first1 = scrut[1];
                r = first0;
                l = first1;
                tmp3 = boyer2.Atom(h);
                tmp4 = boyer2.Conss([
                  tmp3,
                  l
                ]);
                return [
                  r,
                  tmp4
                ]
              } else {
                throw new globalThis.Error("match error");
              }
            }
          } else {
            h = param0;
            t1 = param1;
            scrut = boyer2.sublist(t1);
            if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
              first0 = scrut[0];
              first1 = scrut[1];
              r = first0;
              l = first1;
              tmp5 = boyer2.Atom(h);
              tmp6 = boyer2.Conss([
                tmp5,
                l
              ]);
              return [
                r,
                tmp6
              ]
            } else {
              throw new globalThis.Error("match error");
            }
          }
        } else if (param01 === ")") {
          if (param11 instanceof NofibPrelude.Nil.class) {
            t2 = param1;
            return [
              t2,
              boyer2.Nill
            ]
          } else {
            h = param0;
            t1 = param1;
            scrut = boyer2.sublist(t1);
            if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
              first0 = scrut[0];
              first1 = scrut[1];
              r = first0;
              l = first1;
              tmp7 = boyer2.Atom(h);
              tmp8 = boyer2.Conss([
                tmp7,
                l
              ]);
              return [
                r,
                tmp8
              ]
            } else {
              throw new globalThis.Error("match error");
            }
          }
        } else {
          h = param0;
          t1 = param1;
          scrut = boyer2.sublist(t1);
          if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
            first0 = scrut[0];
            first1 = scrut[1];
            r = first0;
            l = first1;
            tmp9 = boyer2.Atom(h);
            tmp10 = boyer2.Conss([
              tmp9,
              l
            ]);
            return [
              r,
              tmp10
            ]
          } else {
            throw new globalThis.Error("match error");
          }
        }
      } else {
        h = param0;
        t1 = param1;
        scrut = boyer2.sublist(t1);
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first0 = scrut[0];
          first1 = scrut[1];
          r = first0;
          l = first1;
          tmp11 = boyer2.Atom(h);
          tmp12 = boyer2.Conss([
            tmp11,
            l
          ]);
          return [
            r,
            tmp12
          ]
        } else {
          throw new globalThis.Error("match error");
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static mkLispList(ls) {
    let param0, param1, param01, param11, t1, scrut, first1, first0, r, l;
    if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      if (param0 instanceof NofibPrelude.Cons.class) {
        param01 = param0.head;
        param11 = param0.tail;
        if (param01 === "(") {
          if (param11 instanceof NofibPrelude.Nil.class) {
            t1 = param1;
            scrut = boyer2.sublist(t1);
            if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
              first0 = scrut[0];
              first1 = scrut[1];
              r = first0;
              l = first1;
              if (r instanceof NofibPrelude.Nil.class) {
                return l
              } else {
                return boyer2.Nill
              }
            } else {
              return boyer2.Nill
            }
          } else {
            return boyer2.Nill
          }
        } else {
          return boyer2.Nill
        }
      } else {
        return boyer2.Nill
      }
    } else {
      return boyer2.Nill
    }
  } 
  static restOfToken(s) {
    let param0, param1, h, t1, scrut, first1, first0, a, b, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    if (s instanceof NofibPrelude.Nil.class) {
      return [
        NofibPrelude.Nil,
        NofibPrelude.Nil
      ]
    } else if (s instanceof NofibPrelude.Cons.class) {
      param0 = s.head;
      param1 = s.tail;
      h = param0;
      t1 = param1;
      tmp = h === "(";
      tmp1 = h === ")";
      tmp2 = tmp || tmp1;
      tmp3 = h === " ";
      scrut1 = tmp2 || tmp3;
      if (scrut1 === true) {
        tmp4 = NofibPrelude.Cons(h, t1);
        return [
          NofibPrelude.Nil,
          tmp4
        ]
      } else {
        scrut = boyer2.restOfToken(t1);
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first0 = scrut[0];
          first1 = scrut[1];
          a = first0;
          b = first1;
          tmp5 = NofibPrelude.Cons(h, a);
          return [
            tmp5,
            b
          ]
        } else {
          throw new globalThis.Error("match error");
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static getToken(s1) {
    let param0, param1, h, t1, scrut, first1, first0, a, b, scrut1, scrut2, tmp, tmp1, tmp2, tmp3;
    if (s1 instanceof NofibPrelude.Nil.class) {
      return [
        NofibPrelude.Nil,
        NofibPrelude.Nil
      ]
    } else if (s1 instanceof NofibPrelude.Cons.class) {
      param0 = s1.head;
      param1 = s1.tail;
      h = param0;
      t1 = param1;
      scrut2 = h === " ";
      if (scrut2 === true) {
        return boyer2.getToken(t1)
      } else {
        tmp = h === "(";
        tmp1 = h === ")";
        scrut1 = tmp || tmp1;
        if (scrut1 === true) {
          tmp2 = NofibPrelude.Cons(h, NofibPrelude.Nil);
          return [
            tmp2,
            t1
          ]
        } else {
          scrut = boyer2.restOfToken(t1);
          if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
            first0 = scrut[0];
            first1 = scrut[1];
            a = first0;
            b = first1;
            tmp3 = NofibPrelude.Cons(h, a);
            return [
              tmp3,
              b
            ]
          } else {
            throw new globalThis.Error("match error");
          }
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static strToToken(s2) {
    let scrut, first1, first0, a, b, tmp;
    if (s2 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      scrut = boyer2.getToken(s2);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        a = first0;
        b = first1;
        tmp = boyer2.strToToken(b);
        return NofibPrelude.Cons(a, tmp)
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  static assoc(term_x_y) {
    let first1, first0, term, param0, first11, first01, x8, y1, param01, first12, first02, param02, key, rest, scrut, tmp;
    if (globalThis.Array.isArray(term_x_y) && term_x_y.length === 2) {
      first0 = term_x_y[0];
      first1 = term_x_y[1];
      term = first0;
      if (first1 instanceof boyer2.Conss.class) {
        param0 = first1.a;
        if (globalThis.Array.isArray(param0) && param0.length === 2) {
          first01 = param0[0];
          first11 = param0[1];
          x8 = first01;
          y1 = first11;
          if (x8 instanceof boyer2.Conss.class) {
            param01 = x8.a;
            if (globalThis.Array.isArray(param01) && param01.length === 2) {
              first02 = param01[0];
              first12 = param01[1];
              if (first02 instanceof boyer2.Atom.class) {
                param02 = first02.a;
                key = param02;
                rest = first12;
                tmp = boyer2.Atom(key);
                scrut = boyer2.lispListEq(term, tmp);
                if (scrut === true) {
                  return x8
                } else {
                  return boyer2.assoc([
                    term,
                    y1
                  ])
                }
              } else {
                return boyer2.Nill
              }
            } else {
              return boyer2.Nill
            }
          } else {
            return boyer2.Nill
          }
        } else {
          return boyer2.Nill
        }
      } else {
        return boyer2.Nill
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static addtoLUT(k_l_lut) {
    let first2, first1, first0, k, l, param0, first21, first11, first01, left, first12, first02, k1, kl, right, scrut, scrut1, k2, l1, tmp, tmp1, tmp2, tmp3, lambda, lambda1;
    if (globalThis.Array.isArray(k_l_lut) && k_l_lut.length === 3) {
      first0 = k_l_lut[0];
      first1 = k_l_lut[1];
      first2 = k_l_lut[2];
      k2 = first0;
      l1 = first1;
      k = first0;
      l = first1;
      if (first2 instanceof boyer2.Empty.class) {
        tmp = NofibPrelude.Cons(l1, NofibPrelude.Nil);
        return boyer2.Node([
          boyer2.Empty,
          [
            k2,
            tmp
          ],
          boyer2.Empty
        ])
      } else if (first2 instanceof boyer2.Node.class) {
        param0 = first2.x;
        if (globalThis.Array.isArray(param0) && param0.length === 3) {
          first01 = param0[0];
          first11 = param0[1];
          first21 = param0[2];
          left = first01;
          if (globalThis.Array.isArray(first11) && first11.length === 2) {
            first02 = first11[0];
            first12 = first11[1];
            k1 = first02;
            kl = first12;
            right = first21;
            scrut1 = NofibPrelude.listEq(k, k1);
            if (scrut1 === true) {
              tmp1 = NofibPrelude.Cons(l, kl);
              return boyer2.Node([
                left,
                [
                  k1,
                  tmp1
                ],
                right
              ])
            } else {
              lambda = (undefined, function (x8, y1) {
                return x8 < y1
              });
              lambda1 = (undefined, function (x8, y1) {
                return x8 > y1
              });
              scrut = NofibPrelude.ltList(k, k1, lambda, lambda1);
              if (scrut === true) {
                tmp2 = boyer2.addtoLUT([
                  k,
                  l,
                  left
                ]);
                return boyer2.Node([
                  tmp2,
                  [
                    k1,
                    kl
                  ],
                  right
                ])
              } else {
                tmp3 = boyer2.addtoLUT([
                  k,
                  l,
                  right
                ]);
                return boyer2.Node([
                  left,
                  [
                    k1,
                    kl
                  ],
                  tmp3
                ])
              }
            }
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static getLUT(t_lut) {
    let first1, first0, t1, param0, first2, first11, first01, left, first12, first02, k, kl, right, scrut, scrut1, t2, lambda, lambda1;
    if (globalThis.Array.isArray(t_lut) && t_lut.length === 2) {
      first0 = t_lut[0];
      first1 = t_lut[1];
      t2 = first0;
      t1 = first0;
      if (first1 instanceof boyer2.Empty.class) {
        return NofibPrelude.Nil
      } else if (first1 instanceof boyer2.Node.class) {
        param0 = first1.x;
        if (globalThis.Array.isArray(param0) && param0.length === 3) {
          first01 = param0[0];
          first11 = param0[1];
          first2 = param0[2];
          left = first01;
          if (globalThis.Array.isArray(first11) && first11.length === 2) {
            first02 = first11[0];
            first12 = first11[1];
            k = first02;
            kl = first12;
            right = first2;
            scrut1 = NofibPrelude.listEq(t1, k);
            if (scrut1 === true) {
              return kl
            } else {
              lambda = (undefined, function (x8, y1) {
                return x8 < y1
              });
              lambda1 = (undefined, function (x8, y1) {
                return x8 > y1
              });
              scrut = NofibPrelude.ltList(t1, k, lambda, lambda1);
              if (scrut === true) {
                return boyer2.getLUT([
                  t1,
                  left
                ])
              } else {
                return boyer2.getLUT([
                  t1,
                  right
                ])
              }
            }
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static makelemmas(rules) {
    let param0, param1, h, t1, tmp, tmp1, tmp2;
    if (rules instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (rules instanceof NofibPrelude.Cons.class) {
      param0 = rules.head;
      param1 = rules.tail;
      h = param0;
      t1 = param1;
      tmp = boyer2.strToToken(h);
      tmp1 = boyer2.mkLispList(tmp);
      tmp2 = boyer2.makelemmas(t1);
      return NofibPrelude.Cons(tmp1, tmp2)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static addlemma(lspls, term) {
    let param0, first1, first0, x8, y1, z, scrut, scrut1, param01, x9, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    if (lspls instanceof boyer2.Nill.class) {
      return term
    } else if (lspls instanceof boyer2.Atom.class) {
      param01 = lspls.a;
      x9 = param01;
      throw new globalThis.Error("error");
    } else if (lspls instanceof boyer2.Conss.class) {
      param0 = lspls.a;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        x8 = first0;
        y1 = first1;
        tmp = boyer2.car(y1);
        z = tmp;
        tmp1 = boyer2.tv(x8);
        tmp2 = NofibPrelude.nofibStringToList("equal");
        scrut = NofibPrelude.listEq(tmp1, tmp2);
        if (scrut === true) {
          tmp3 = boyer2.atom(z);
          scrut1 = BenchmarkPrelude.not(tmp3);
          if (scrut1 === true) {
            tmp4 = boyer2.car(z);
            tmp5 = boyer2.tv(tmp4);
            tmp6 = boyer2.Conss([
              x8,
              y1
            ]);
            return boyer2.addtoLUT([
              tmp5,
              tmp6,
              term
            ])
          } else {
            throw new globalThis.Error("error");
          }
        } else {
          throw new globalThis.Error("error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static addlemmalst(lspls1, term1) {
    let param0, param1, h, t1, tmp;
    if (lspls1 instanceof NofibPrelude.Nil.class) {
      return term1
    } else if (lspls1 instanceof NofibPrelude.Cons.class) {
      param0 = lspls1.head;
      param1 = lspls1.tail;
      h = param0;
      t1 = param1;
      tmp = boyer2.addlemma(h, term1);
      return boyer2.addlemmalst(t1, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static applysubstlst(alist, y1) {
    let param0, first1, first0, x8, y2, param01, x9, tmp, tmp1;
    if (y1 instanceof boyer2.Nill.class) {
      return boyer2.Nill
    } else if (y1 instanceof boyer2.Atom.class) {
      param01 = y1.a;
      x9 = param01;
      throw new globalThis.Error("error");
    } else if (y1 instanceof boyer2.Conss.class) {
      param0 = y1.a;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        x8 = first0;
        y2 = first1;
        tmp = boyer2.applysubst(alist, x8);
        tmp1 = boyer2.applysubstlst(alist, y2);
        return boyer2.Conss([
          tmp,
          tmp1
        ])
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static applysubst(alist1, x8) {
    let param0, first1, first0, x9, y2, param01, x10, scrut, param02, first11, first01, y3, tmp, tmp1;
    if (x8 instanceof boyer2.Nill.class) {
      return boyer2.Nill
    } else if (x8 instanceof boyer2.Atom.class) {
      param01 = x8.a;
      x10 = param01;
      tmp = boyer2.Atom(x10);
      scrut = boyer2.assoc([
        tmp,
        alist1
      ]);
      if (scrut instanceof boyer2.Conss.class) {
        param02 = scrut.a;
        if (globalThis.Array.isArray(param02) && param02.length === 2) {
          first01 = param02[0];
          first11 = param02[1];
          y3 = first11;
          return y3
        } else {
          return boyer2.Atom(x10)
        }
      } else {
        return boyer2.Atom(x10)
      }
    } else if (x8 instanceof boyer2.Conss.class) {
      param0 = x8.a;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        x9 = first0;
        y2 = first1;
        tmp1 = boyer2.applysubstlst(alist1, y2);
        return boyer2.Conss([
          x9,
          tmp1
        ])
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static onewayunify1lst(l1, l2, u) {
    let scrut, first1, first0, b, u1, tmp, tmp1, tmp2, tmp3;
    if (l1 instanceof boyer2.Nill.class) {
      return [
        true,
        u
      ]
    } else {
      tmp = boyer2.car(l1);
      tmp1 = boyer2.car(l2);
      scrut = boyer2.onewayunify1(tmp, tmp1, u);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        b = first0;
        u1 = first1;
        if (b === true) {
          tmp2 = boyer2.cdr(l1);
          tmp3 = boyer2.cdr(l2);
          return boyer2.onewayunify1lst(tmp2, tmp3, u1)
        } else {
          return [
            false,
            u1
          ]
        }
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  static onewayunify1(t1, t2, u1) {
    let scrut, scrut1, scrut2, scrut3, param0, first1, first0, y2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    scrut2 = boyer2.atom(t2);
    if (scrut2 === true) {
      scrut3 = boyer2.assoc([
        t2,
        u1
      ]);
      if (scrut3 instanceof boyer2.Conss.class) {
        param0 = scrut3.a;
        if (globalThis.Array.isArray(param0) && param0.length === 2) {
          first0 = param0[0];
          first1 = param0[1];
          y2 = first1;
          tmp = boyer2.lispListEq(t1, y2);
          return [
            tmp,
            u1
          ]
        } else {
          tmp1 = boyer2.Conss([
            t2,
            t1
          ]);
          tmp2 = boyer2.Conss([
            tmp1,
            u1
          ]);
          return [
            true,
            tmp2
          ]
        }
      } else {
        tmp3 = boyer2.Conss([
          t2,
          t1
        ]);
        tmp4 = boyer2.Conss([
          tmp3,
          u1
        ]);
        return [
          true,
          tmp4
        ]
      }
    } else {
      scrut1 = boyer2.atom(t1);
      if (scrut1 === true) {
        return [
          false,
          u1
        ]
      } else {
        tmp5 = boyer2.car(t1);
        tmp6 = boyer2.car(t2);
        scrut = boyer2.lispListEq(tmp5, tmp6);
        if (scrut === true) {
          tmp7 = boyer2.cdr(t1);
          tmp8 = boyer2.cdr(t2);
          return boyer2.onewayunify1lst(tmp7, tmp8, u1)
        } else {
          return [
            false,
            u1
          ]
        }
      }
    }
  } 
  static onewayunify(t11, t21) {
    return boyer2.onewayunify1(t11, t21, boyer2.Nill)
  } 
  static rewritewithlemmas(t3, l, term2) {
    let param0, param1, lh, lt, scrut, first1, first0, b, u2, tmp, tmp1, tmp2;
    if (l instanceof NofibPrelude.Nil.class) {
      return t3
    } else if (l instanceof NofibPrelude.Cons.class) {
      param0 = l.head;
      param1 = l.tail;
      lh = param0;
      lt = param1;
      tmp = boyer2.cadr(lh);
      scrut = boyer2.onewayunify(t3, tmp);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        b = first0;
        u2 = first1;
        if (b === true) {
          tmp1 = boyer2.caddr(lh);
          tmp2 = boyer2.applysubst(u2, tmp1);
          return boyer2.rewrite(tmp2, term2)
        } else {
          return boyer2.rewritewithlemmas(t3, lt, term2)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static rewriteargs(x9, term3) {
    let param0, first1, first0, x10, y2, param01, tmp, tmp1;
    if (x9 instanceof boyer2.Nill.class) {
      return boyer2.Nill
    } else if (x9 instanceof boyer2.Atom.class) {
      param01 = x9.a;
      throw new globalThis.Error("error");
    } else if (x9 instanceof boyer2.Conss.class) {
      param0 = x9.a;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        x10 = first0;
        y2 = first1;
        tmp = boyer2.rewrite(x10, term3);
        tmp1 = boyer2.rewriteargs(y2, term3);
        return boyer2.Conss([
          tmp,
          tmp1
        ])
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static rewrite(x10, term4) {
    let param0, first1, first0, l11, l21, param01, x11, tmp, tmp1, tmp2, tmp3;
    if (x10 instanceof boyer2.Nill.class) {
      return boyer2.Nill
    } else if (x10 instanceof boyer2.Atom.class) {
      param01 = x10.a;
      x11 = param01;
      return boyer2.Atom(x11)
    } else if (x10 instanceof boyer2.Conss.class) {
      param0 = x10.a;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        l11 = first0;
        l21 = first1;
        tmp = boyer2.rewriteargs(l21, term4);
        tmp1 = boyer2.Conss([
          l11,
          tmp
        ]);
        tmp2 = boyer2.tv(l11);
        tmp3 = boyer2.getLUT([
          tmp2,
          term4
        ]);
        return boyer2.rewritewithlemmas(tmp1, tmp3, term4)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static subterm(i) {
    let c, str, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10;
    tmp = NofibPrelude.stringOfInt(i);
    tmp1 = NofibPrelude.stringConcat("c", tmp);
    c = tmp1;
    tmp2 = NofibPrelude.nofibStringToList("( ( x f ( plus ( plus a b )( plus ");
    tmp3 = NofibPrelude.nofibStringToList(" ( zero ) ) ) )( y f ( times ( times a b )( plus ");
    tmp4 = NofibPrelude.nofibStringToList(" d ) ) )( z f ( reverse ( append ( append a b ) ( [] ) ) ) )(u equal ( plus a b ) ( difference x y ) )(w lessp ( remainder a b )( member a ( length b ) ) ) )");
    tmp5 = NofibPrelude.stringConcat(c, tmp4);
    tmp6 = NofibPrelude.stringConcat(tmp3, tmp5);
    tmp7 = NofibPrelude.stringConcat(c, tmp6);
    tmp8 = NofibPrelude.stringConcat(tmp2, tmp7);
    str = tmp8;
    tmp9 = NofibPrelude.nofibStringToList(str);
    tmp10 = boyer2.strToToken(tmp9);
    return boyer2.mkLispList(tmp10)
  } 
  static report(b) {
    if (b === true) {
      return "The term is a tautology"
    } else {
      return "The term is not a tautology"
    }
  } 
  static tautp(term5) {
    let tmp;
    tmp = boyer2.rewrite(term5, boyer2.#lemmas);
    return boyer2.tautologyp([
      tmp,
      boyer2.Nill,
      boyer2.Nill
    ])
  } 
  static teststatement(i1) {
    let tmp;
    tmp = boyer2.subterm(i1);
    return boyer2.applysubst(tmp, boyer2.#statement)
  } 
  static testresult(i2) {
    let tmp;
    tmp = boyer2.teststatement(i2);
    return boyer2.tautp(tmp)
  } 
  static testBoyer2_nofib(n) {
    let tmp;
    tmp = boyer2.testresult(n);
    return boyer2.report(tmp)
  }
  static toString() { return "boyer2"; }
};
let boyer2 = boyer21; export default boyer2;
