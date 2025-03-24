import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let lastpiece1;
lastpiece1 = class lastpiece {
  static {
    lastpiece1 = lastpiece;
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75, tmp76, tmp77, tmp78, tmp79, tmp80, tmp81, tmp82, tmp83, tmp84, tmp85, tmp86, tmp87, tmp88, tmp89, tmp90, tmp91, tmp92, tmp93, tmp94, tmp95, tmp96, tmp97, tmp98, tmp99, tmp100, tmp101, tmp102, tmp103, tmp104, tmp105, tmp106, tmp107, tmp108, tmp109, tmp110, tmp111, tmp112, tmp113, tmp114, tmp115, tmp116, tmp117, tmp118, tmp119, tmp120, tmp121, tmp122, tmp123, tmp124, tmp125, tmp126, tmp127, tmp128, tmp129, tmp130, tmp131, tmp132, tmp133, tmp134, tmp135, tmp136, tmp137, tmp138, tmp139, tmp140, tmp141, tmp142, tmp143, tmp144, tmp145, tmp146, tmp147, tmp148, tmp149, tmp150, tmp151, tmp152, tmp153, tmp154, tmp155, tmp156, tmp157, tmp158, tmp159, tmp160, tmp161, tmp162, tmp163, tmp164, tmp165, tmp166, tmp167, tmp168, tmp169, tmp170, tmp171, tmp172, tmp173, tmp174, tmp175, tmp176, tmp177, tmp178, tmp179, tmp180, tmp181, tmp182, tmp183, tmp184, tmp185, tmp186, tmp187, tmp188, tmp189, tmp190, tmp191, tmp192, tmp193, tmp194, tmp195, tmp196, tmp197, tmp198, tmp199, tmp200, tmp201, tmp202, tmp203, tmp204, tmp205, tmp206, tmp207, tmp208, tmp209, tmp210, tmp211, tmp212, tmp213, tmp214, tmp215, tmp216, tmp217, tmp218, tmp219, tmp220, tmp221, tmp222, tmp223, tmp224, tmp225, tmp226, tmp227, tmp228, tmp229, tmp230, tmp231, tmp232, tmp233, tmp234, tmp235, tmp236, tmp237, tmp238, tmp239, tmp240, tmp241, tmp242, tmp243, tmp244, tmp245, tmp246, tmp247, tmp248, tmp249, tmp250, tmp251, tmp252, tmp253, tmp254, tmp255, tmp256, tmp257, tmp258, tmp259, tmp260, tmp261, tmp262, tmp263, tmp264, tmp265, tmp266, tmp267, tmp268, tmp269, tmp270, tmp271, tmp272, tmp273, tmp274, tmp275, tmp276, tmp277, tmp278, tmp279, tmp280, lambda;
    const GT$class = class GT {
      constructor() {}
      toString() { return "GT"; }
    };
    this.GT = new GT$class;
    this.GT.class = GT$class;
    const LT$class = class LT {
      constructor() {}
      toString() { return "LT"; }
    };
    this.LT = new LT$class;
    this.LT.class = LT$class;
    const EQ$class = class EQ {
      constructor() {}
      toString() { return "EQ"; }
    };
    this.EQ = new EQ$class;
    this.EQ.class = EQ$class;
    this.Map = class Map {
      constructor() {}
      toString() { return "Map"; }
    };
    const Tip$class = class Tip extends lastpiece.Map {
      constructor() {
        super();
      }
      toString() { return "Tip"; }
    };
    this.Tip = new Tip$class;
    this.Tip.class = Tip$class;
    this.Bin = function Bin(i1, k1, v1, l1, r1) {
      return new Bin.class(i1, k1, v1, l1, r1);
    };
    this.Bin.class = class Bin extends lastpiece.Map {
      constructor(i, k, v, l, r) {
        super();
        this.i = i;
        this.k = k;
        this.v = v;
        this.l = l;
        this.r = r;
      }
      toString() { return "Bin(" + globalThis.Predef.render(this.i) + ", " + globalThis.Predef.render(this.k) + ", " + globalThis.Predef.render(this.v) + ", " + globalThis.Predef.render(this.l) + ", " + globalThis.Predef.render(this.r) + ")"; }
    };
    this.P = function P(i1, a1, b1) {
      return new P.class(i1, a1, b1);
    };
    this.P.class = class P {
      constructor(i, a, b) {
        this.i = i;
        this.a = a;
        this.b = b;
      }
      toString() { return "P(" + globalThis.Predef.render(this.i) + ", " + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    this.S = class S {
      constructor() {}
      toString() { return "S"; }
    };
    const Male$class = class Male extends lastpiece.S {
      constructor() {
        super();
      }
      toString() { return "Male"; }
    };
    this.Male = new Male$class;
    this.Male.class = Male$class;
    const Female$class = class Female extends lastpiece.S {
      constructor() {
        super();
      }
      toString() { return "Female"; }
    };
    this.Female = new Female$class;
    this.Female.class = Female$class;
    this.Solution = class Solution {
      constructor() {}
      toString() { return "Solution"; }
    };
    this.Soln = function Soln(b1) {
      return new Soln.class(b1);
    };
    this.Soln.class = class Soln extends lastpiece.Solution {
      constructor(b) {
        super();
        this.b = b;
      }
      toString() { return "Soln(" + globalThis.Predef.render(this.b) + ")"; }
    };
    this.Choose = function Choose(s1) {
      return new Choose.class(s1);
    };
    this.Choose.class = class Choose extends lastpiece.Solution {
      constructor(s) {
        super();
        this.s = s;
      }
      toString() { return "Choose(" + globalThis.Predef.render(this.s) + ")"; }
    };
    this.Fail = function Fail(b1, s1) {
      return new Fail.class(b1, s1);
    };
    this.Fail.class = class Fail extends lastpiece.Solution {
      constructor(b, s) {
        super();
        this.b = b;
        this.s = s;
      }
      toString() { return "Fail(" + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.s) + ")"; }
    };
    this.maxRow = 8;
    this.maxCol = 8;
    this.emptyBoard = lastpiece.Tip;
    tmp = NofibPrelude.Cons([
      2,
      2
    ], NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons([
      2,
      1
    ], tmp);
    tmp2 = NofibPrelude.Cons([
      1,
      1
    ], tmp1);
    tmp3 = NofibPrelude.Cons([
      0,
      1
    ], tmp2);
    tmp4 = - 1;
    tmp5 = - 2;
    tmp6 = - 2;
    tmp7 = NofibPrelude.Cons([
      2,
      tmp6
    ], NofibPrelude.Nil);
    tmp8 = NofibPrelude.Cons([
      1,
      tmp5
    ], tmp7);
    tmp9 = NofibPrelude.Cons([
      1,
      tmp4
    ], tmp8);
    tmp10 = NofibPrelude.Cons([
      1,
      0
    ], tmp9);
    tmp11 = NofibPrelude.Cons(tmp10, NofibPrelude.Nil);
    tmp12 = NofibPrelude.Cons(tmp3, tmp11);
    tmp13 = lastpiece.P("n", tmp12, NofibPrelude.Nil);
    this.nPiece = tmp13;
    tmp14 = NofibPrelude.Cons([
      3,
      0
    ], NofibPrelude.Nil);
    tmp15 = NofibPrelude.Cons([
      2,
      0
    ], tmp14);
    tmp16 = NofibPrelude.Cons([
      1,
      0
    ], tmp15);
    tmp17 = NofibPrelude.Cons([
      0,
      1
    ], tmp16);
    tmp18 = NofibPrelude.Cons(tmp17, NofibPrelude.Nil);
    tmp19 = NofibPrelude.Cons([
      1,
      3
    ], NofibPrelude.Nil);
    tmp20 = NofibPrelude.Cons([
      0,
      3
    ], tmp19);
    tmp21 = NofibPrelude.Cons([
      0,
      2
    ], tmp20);
    tmp22 = NofibPrelude.Cons([
      0,
      1
    ], tmp21);
    tmp23 = - 1;
    tmp24 = NofibPrelude.Cons([
      3,
      tmp23
    ], NofibPrelude.Nil);
    tmp25 = NofibPrelude.Cons([
      3,
      0
    ], tmp24);
    tmp26 = NofibPrelude.Cons([
      2,
      0
    ], tmp25);
    tmp27 = NofibPrelude.Cons([
      1,
      0
    ], tmp26);
    tmp28 = NofibPrelude.Cons(tmp27, NofibPrelude.Nil);
    tmp29 = NofibPrelude.Cons(tmp22, tmp28);
    tmp30 = lastpiece.P("m", tmp18, tmp29);
    this.mPiece = tmp30;
    tmp31 = NofibPrelude.Cons([
      1,
      2
    ], NofibPrelude.Nil);
    tmp32 = NofibPrelude.Cons([
      0,
      3
    ], tmp31);
    tmp33 = NofibPrelude.Cons([
      0,
      2
    ], tmp32);
    tmp34 = NofibPrelude.Cons([
      0,
      1
    ], tmp33);
    tmp35 = - 1;
    tmp36 = NofibPrelude.Cons([
      2,
      tmp35
    ], NofibPrelude.Nil);
    tmp37 = NofibPrelude.Cons([
      3,
      0
    ], tmp36);
    tmp38 = NofibPrelude.Cons([
      2,
      0
    ], tmp37);
    tmp39 = NofibPrelude.Cons([
      1,
      0
    ], tmp38);
    tmp40 = NofibPrelude.Cons(tmp39, NofibPrelude.Nil);
    tmp41 = NofibPrelude.Cons(tmp34, tmp40);
    tmp42 = - 1;
    tmp43 = NofibPrelude.Cons([
      1,
      2
    ], NofibPrelude.Nil);
    tmp44 = NofibPrelude.Cons([
      1,
      1
    ], tmp43);
    tmp45 = NofibPrelude.Cons([
      1,
      0
    ], tmp44);
    tmp46 = NofibPrelude.Cons([
      1,
      tmp42
    ], tmp45);
    tmp47 = NofibPrelude.Cons([
      1,
      1
    ], NofibPrelude.Nil);
    tmp48 = NofibPrelude.Cons([
      3,
      0
    ], tmp47);
    tmp49 = NofibPrelude.Cons([
      2,
      0
    ], tmp48);
    tmp50 = NofibPrelude.Cons([
      1,
      0
    ], tmp49);
    tmp51 = NofibPrelude.Cons(tmp50, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(tmp46, tmp51);
    tmp53 = lastpiece.P("l", tmp41, tmp52);
    this.lPiece = tmp53;
    tmp54 = - 1;
    tmp55 = NofibPrelude.Cons([
      2,
      tmp54
    ], NofibPrelude.Nil);
    tmp56 = NofibPrelude.Cons([
      2,
      0
    ], tmp55);
    tmp57 = NofibPrelude.Cons([
      1,
      0
    ], tmp56);
    tmp58 = NofibPrelude.Cons([
      0,
      1
    ], tmp57);
    tmp59 = NofibPrelude.Cons(tmp58, NofibPrelude.Nil);
    tmp60 = NofibPrelude.Cons([
      2,
      2
    ], NofibPrelude.Nil);
    tmp61 = NofibPrelude.Cons([
      1,
      2
    ], tmp60);
    tmp62 = NofibPrelude.Cons([
      1,
      1
    ], tmp61);
    tmp63 = NofibPrelude.Cons([
      1,
      0
    ], tmp62);
    tmp64 = NofibPrelude.Cons(tmp63, NofibPrelude.Nil);
    tmp65 = lastpiece.P("k", tmp59, tmp64);
    this.kPiece = tmp65;
    tmp66 = NofibPrelude.Cons([
      1,
      1
    ], NofibPrelude.Nil);
    tmp67 = NofibPrelude.Cons([
      0,
      3
    ], tmp66);
    tmp68 = NofibPrelude.Cons([
      0,
      2
    ], tmp67);
    tmp69 = NofibPrelude.Cons([
      0,
      1
    ], tmp68);
    tmp70 = - 1;
    tmp71 = NofibPrelude.Cons([
      1,
      tmp70
    ], NofibPrelude.Nil);
    tmp72 = NofibPrelude.Cons([
      3,
      0
    ], tmp71);
    tmp73 = NofibPrelude.Cons([
      2,
      0
    ], tmp72);
    tmp74 = NofibPrelude.Cons([
      1,
      0
    ], tmp73);
    tmp75 = - 2;
    tmp76 = - 1;
    tmp77 = NofibPrelude.Cons([
      1,
      1
    ], NofibPrelude.Nil);
    tmp78 = NofibPrelude.Cons([
      1,
      0
    ], tmp77);
    tmp79 = NofibPrelude.Cons([
      1,
      tmp76
    ], tmp78);
    tmp80 = NofibPrelude.Cons([
      1,
      tmp75
    ], tmp79);
    tmp81 = NofibPrelude.Cons(tmp80, NofibPrelude.Nil);
    tmp82 = NofibPrelude.Cons(tmp74, tmp81);
    tmp83 = NofibPrelude.Cons(tmp69, tmp82);
    tmp84 = NofibPrelude.Cons([
      2,
      2
    ], NofibPrelude.Nil);
    tmp85 = NofibPrelude.Cons([
      3,
      0
    ], tmp84);
    tmp86 = NofibPrelude.Cons([
      2,
      0
    ], tmp85);
    tmp87 = NofibPrelude.Cons([
      1,
      0
    ], tmp86);
    tmp88 = NofibPrelude.Cons(tmp87, NofibPrelude.Nil);
    tmp89 = lastpiece.P("j", tmp83, tmp88);
    this.jPiece = tmp89;
    tmp90 = NofibPrelude.Cons([
      3,
      1
    ], NofibPrelude.Nil);
    tmp91 = NofibPrelude.Cons([
      2,
      1
    ], tmp90);
    tmp92 = NofibPrelude.Cons([
      2,
      0
    ], tmp91);
    tmp93 = NofibPrelude.Cons([
      1,
      0
    ], tmp92);
    tmp94 = - 1;
    tmp95 = NofibPrelude.Cons([
      1,
      tmp94
    ], NofibPrelude.Nil);
    tmp96 = NofibPrelude.Cons([
      1,
      0
    ], tmp95);
    tmp97 = NofibPrelude.Cons([
      0,
      2
    ], tmp96);
    tmp98 = NofibPrelude.Cons([
      0,
      1
    ], tmp97);
    tmp99 = NofibPrelude.Cons([
      3,
      1
    ], NofibPrelude.Nil);
    tmp100 = NofibPrelude.Cons([
      2,
      1
    ], tmp99);
    tmp101 = NofibPrelude.Cons([
      1,
      1
    ], tmp100);
    tmp102 = NofibPrelude.Cons([
      1,
      0
    ], tmp101);
    tmp103 = NofibPrelude.Cons(tmp102, NofibPrelude.Nil);
    tmp104 = NofibPrelude.Cons(tmp98, tmp103);
    tmp105 = NofibPrelude.Cons(tmp93, tmp104);
    tmp106 = - 1;
    tmp107 = - 2;
    tmp108 = NofibPrelude.Cons([
      1,
      tmp107
    ], NofibPrelude.Nil);
    tmp109 = NofibPrelude.Cons([
      1,
      tmp106
    ], tmp108);
    tmp110 = NofibPrelude.Cons([
      1,
      0
    ], tmp109);
    tmp111 = NofibPrelude.Cons([
      0,
      1
    ], tmp110);
    tmp112 = NofibPrelude.Cons(tmp111, NofibPrelude.Nil);
    tmp113 = lastpiece.P("i", tmp105, tmp112);
    this.iPiece = tmp113;
    tmp114 = NofibPrelude.Cons([
      2,
      2
    ], NofibPrelude.Nil);
    tmp115 = NofibPrelude.Cons([
      1,
      2
    ], tmp114);
    tmp116 = NofibPrelude.Cons([
      1,
      1
    ], tmp115);
    tmp117 = NofibPrelude.Cons([
      0,
      1
    ], tmp116);
    tmp118 = - 1;
    tmp119 = - 1;
    tmp120 = - 2;
    tmp121 = NofibPrelude.Cons([
      2,
      tmp120
    ], NofibPrelude.Nil);
    tmp122 = NofibPrelude.Cons([
      2,
      tmp119
    ], tmp121);
    tmp123 = NofibPrelude.Cons([
      1,
      tmp118
    ], tmp122);
    tmp124 = NofibPrelude.Cons([
      1,
      0
    ], tmp123);
    tmp125 = NofibPrelude.Cons([
      2,
      2
    ], NofibPrelude.Nil);
    tmp126 = NofibPrelude.Cons([
      2,
      1
    ], tmp125);
    tmp127 = NofibPrelude.Cons([
      1,
      1
    ], tmp126);
    tmp128 = NofibPrelude.Cons([
      1,
      0
    ], tmp127);
    tmp129 = NofibPrelude.Cons(tmp128, NofibPrelude.Nil);
    tmp130 = NofibPrelude.Cons(tmp124, tmp129);
    tmp131 = NofibPrelude.Cons(tmp117, tmp130);
    tmp132 = - 1;
    tmp133 = - 1;
    tmp134 = NofibPrelude.Cons([
      2,
      tmp133
    ], NofibPrelude.Nil);
    tmp135 = NofibPrelude.Cons([
      1,
      tmp132
    ], tmp134);
    tmp136 = NofibPrelude.Cons([
      1,
      0
    ], tmp135);
    tmp137 = NofibPrelude.Cons([
      0,
      1
    ], tmp136);
    tmp138 = NofibPrelude.Cons(tmp137, NofibPrelude.Nil);
    tmp139 = lastpiece.P("h", tmp131, tmp138);
    this.hPiece = tmp139;
    tmp140 = NofibPrelude.Cons([
      1,
      3
    ], NofibPrelude.Nil);
    tmp141 = NofibPrelude.Cons([
      1,
      2
    ], tmp140);
    tmp142 = NofibPrelude.Cons([
      1,
      1
    ], tmp141);
    tmp143 = NofibPrelude.Cons([
      0,
      1
    ], tmp142);
    tmp144 = - 1;
    tmp145 = - 1;
    tmp146 = - 1;
    tmp147 = NofibPrelude.Cons([
      3,
      tmp146
    ], NofibPrelude.Nil);
    tmp148 = NofibPrelude.Cons([
      2,
      tmp145
    ], tmp147);
    tmp149 = NofibPrelude.Cons([
      1,
      tmp144
    ], tmp148);
    tmp150 = NofibPrelude.Cons([
      1,
      0
    ], tmp149);
    tmp151 = NofibPrelude.Cons([
      1,
      3
    ], NofibPrelude.Nil);
    tmp152 = NofibPrelude.Cons([
      1,
      2
    ], tmp151);
    tmp153 = NofibPrelude.Cons([
      0,
      2
    ], tmp152);
    tmp154 = NofibPrelude.Cons([
      0,
      1
    ], tmp153);
    tmp155 = - 1;
    tmp156 = - 1;
    tmp157 = NofibPrelude.Cons([
      3,
      tmp156
    ], NofibPrelude.Nil);
    tmp158 = NofibPrelude.Cons([
      2,
      tmp155
    ], tmp157);
    tmp159 = NofibPrelude.Cons([
      2,
      0
    ], tmp158);
    tmp160 = NofibPrelude.Cons([
      1,
      0
    ], tmp159);
    tmp161 = NofibPrelude.Cons(tmp160, NofibPrelude.Nil);
    tmp162 = NofibPrelude.Cons(tmp154, tmp161);
    tmp163 = NofibPrelude.Cons(tmp150, tmp162);
    tmp164 = NofibPrelude.Cons(tmp143, tmp163);
    tmp165 = lastpiece.P("g", NofibPrelude.Nil, tmp164);
    this.gPiece = tmp165;
    tmp166 = NofibPrelude.Cons([
      3,
      1
    ], NofibPrelude.Nil);
    tmp167 = NofibPrelude.Cons([
      2,
      1
    ], tmp166);
    tmp168 = NofibPrelude.Cons([
      1,
      1
    ], tmp167);
    tmp169 = NofibPrelude.Cons([
      0,
      1
    ], tmp168);
    tmp170 = - 1;
    tmp171 = - 2;
    tmp172 = - 3;
    tmp173 = NofibPrelude.Cons([
      1,
      tmp172
    ], NofibPrelude.Nil);
    tmp174 = NofibPrelude.Cons([
      1,
      tmp171
    ], tmp173);
    tmp175 = NofibPrelude.Cons([
      1,
      tmp170
    ], tmp174);
    tmp176 = NofibPrelude.Cons([
      1,
      0
    ], tmp175);
    tmp177 = NofibPrelude.Cons([
      3,
      1
    ], NofibPrelude.Nil);
    tmp178 = NofibPrelude.Cons([
      3,
      0
    ], tmp177);
    tmp179 = NofibPrelude.Cons([
      2,
      0
    ], tmp178);
    tmp180 = NofibPrelude.Cons([
      1,
      0
    ], tmp179);
    tmp181 = NofibPrelude.Cons(tmp180, NofibPrelude.Nil);
    tmp182 = NofibPrelude.Cons(tmp176, tmp181);
    tmp183 = NofibPrelude.Cons(tmp169, tmp182);
    tmp184 = NofibPrelude.Cons([
      1,
      0
    ], NofibPrelude.Nil);
    tmp185 = NofibPrelude.Cons([
      0,
      3
    ], tmp184);
    tmp186 = NofibPrelude.Cons([
      0,
      2
    ], tmp185);
    tmp187 = NofibPrelude.Cons([
      0,
      1
    ], tmp186);
    tmp188 = NofibPrelude.Cons(tmp187, NofibPrelude.Nil);
    tmp189 = lastpiece.P("f", tmp183, tmp188);
    this.fPiece = tmp189;
    tmp190 = NofibPrelude.Cons([
      1,
      2
    ], NofibPrelude.Nil);
    tmp191 = NofibPrelude.Cons([
      1,
      1
    ], tmp190);
    tmp192 = NofibPrelude.Cons([
      0,
      1
    ], tmp191);
    tmp193 = - 1;
    tmp194 = - 1;
    tmp195 = NofibPrelude.Cons([
      2,
      tmp194
    ], NofibPrelude.Nil);
    tmp196 = NofibPrelude.Cons([
      1,
      tmp193
    ], tmp195);
    tmp197 = NofibPrelude.Cons([
      1,
      0
    ], tmp196);
    tmp198 = NofibPrelude.Cons(tmp197, NofibPrelude.Nil);
    tmp199 = NofibPrelude.Cons(tmp192, tmp198);
    tmp200 = NofibPrelude.Cons([
      1,
      2
    ], NofibPrelude.Nil);
    tmp201 = NofibPrelude.Cons([
      1,
      1
    ], tmp200);
    tmp202 = NofibPrelude.Cons([
      0,
      1
    ], tmp201);
    tmp203 = - 1;
    tmp204 = - 1;
    tmp205 = NofibPrelude.Cons([
      2,
      tmp204
    ], NofibPrelude.Nil);
    tmp206 = NofibPrelude.Cons([
      1,
      tmp203
    ], tmp205);
    tmp207 = NofibPrelude.Cons([
      1,
      0
    ], tmp206);
    tmp208 = NofibPrelude.Cons(tmp207, NofibPrelude.Nil);
    tmp209 = NofibPrelude.Cons(tmp202, tmp208);
    tmp210 = lastpiece.P("e", tmp199, tmp209);
    this.ePiece = tmp210;
    tmp211 = NofibPrelude.Cons([
      2,
      1
    ], NofibPrelude.Nil);
    tmp212 = NofibPrelude.Cons([
      1,
      1
    ], tmp211);
    tmp213 = NofibPrelude.Cons([
      0,
      1
    ], tmp212);
    tmp214 = - 1;
    tmp215 = - 2;
    tmp216 = NofibPrelude.Cons([
      1,
      tmp215
    ], NofibPrelude.Nil);
    tmp217 = NofibPrelude.Cons([
      1,
      tmp214
    ], tmp216);
    tmp218 = NofibPrelude.Cons([
      1,
      0
    ], tmp217);
    tmp219 = NofibPrelude.Cons(tmp218, NofibPrelude.Nil);
    tmp220 = NofibPrelude.Cons(tmp213, tmp219);
    tmp221 = NofibPrelude.Cons([
      2,
      1
    ], NofibPrelude.Nil);
    tmp222 = NofibPrelude.Cons([
      2,
      0
    ], tmp221);
    tmp223 = NofibPrelude.Cons([
      1,
      0
    ], tmp222);
    tmp224 = NofibPrelude.Cons(tmp223, NofibPrelude.Nil);
    tmp225 = lastpiece.P("d", tmp220, tmp224);
    this.dPiece = tmp225;
    tmp226 = NofibPrelude.Cons([
      1,
      1
    ], NofibPrelude.Nil);
    tmp227 = NofibPrelude.Cons([
      0,
      2
    ], tmp226);
    tmp228 = NofibPrelude.Cons([
      0,
      1
    ], tmp227);
    tmp229 = - 1;
    tmp230 = NofibPrelude.Cons([
      2,
      0
    ], NofibPrelude.Nil);
    tmp231 = NofibPrelude.Cons([
      1,
      tmp229
    ], tmp230);
    tmp232 = NofibPrelude.Cons([
      1,
      0
    ], tmp231);
    tmp233 = - 1;
    tmp234 = NofibPrelude.Cons([
      1,
      1
    ], NofibPrelude.Nil);
    tmp235 = NofibPrelude.Cons([
      1,
      0
    ], tmp234);
    tmp236 = NofibPrelude.Cons([
      1,
      tmp233
    ], tmp235);
    tmp237 = NofibPrelude.Cons([
      2,
      0
    ], NofibPrelude.Nil);
    tmp238 = NofibPrelude.Cons([
      1,
      1
    ], tmp237);
    tmp239 = NofibPrelude.Cons([
      1,
      0
    ], tmp238);
    tmp240 = NofibPrelude.Cons(tmp239, NofibPrelude.Nil);
    tmp241 = NofibPrelude.Cons(tmp236, tmp240);
    tmp242 = NofibPrelude.Cons(tmp232, tmp241);
    tmp243 = NofibPrelude.Cons(tmp228, tmp242);
    tmp244 = lastpiece.P("c", NofibPrelude.Nil, tmp243);
    this.cPiece = tmp244;
    tmp245 = NofibPrelude.Cons([
      1,
      2
    ], NofibPrelude.Nil);
    tmp246 = NofibPrelude.Cons([
      0,
      2
    ], tmp245);
    tmp247 = NofibPrelude.Cons([
      0,
      1
    ], tmp246);
    tmp248 = - 1;
    tmp249 = NofibPrelude.Cons([
      2,
      tmp248
    ], NofibPrelude.Nil);
    tmp250 = NofibPrelude.Cons([
      2,
      0
    ], tmp249);
    tmp251 = NofibPrelude.Cons([
      1,
      0
    ], tmp250);
    tmp252 = NofibPrelude.Cons([
      2,
      0
    ], NofibPrelude.Nil);
    tmp253 = NofibPrelude.Cons([
      1,
      0
    ], tmp252);
    tmp254 = NofibPrelude.Cons([
      0,
      1
    ], tmp253);
    tmp255 = NofibPrelude.Cons(tmp254, NofibPrelude.Nil);
    tmp256 = NofibPrelude.Cons(tmp251, tmp255);
    tmp257 = NofibPrelude.Cons(tmp247, tmp256);
    tmp258 = NofibPrelude.Cons([
      1,
      2
    ], NofibPrelude.Nil);
    tmp259 = NofibPrelude.Cons([
      1,
      1
    ], tmp258);
    tmp260 = NofibPrelude.Cons([
      1,
      0
    ], tmp259);
    tmp261 = NofibPrelude.Cons(tmp260, NofibPrelude.Nil);
    tmp262 = lastpiece.P("b", tmp257, tmp261);
    this.bPiece = tmp262;
    tmp263 = NofibPrelude.Cons(lastpiece.nPiece, NofibPrelude.Nil);
    tmp264 = NofibPrelude.Cons(lastpiece.mPiece, tmp263);
    tmp265 = NofibPrelude.Cons(lastpiece.lPiece, tmp264);
    tmp266 = NofibPrelude.Cons(lastpiece.kPiece, tmp265);
    tmp267 = NofibPrelude.Cons(lastpiece.jPiece, tmp266);
    tmp268 = NofibPrelude.Cons(lastpiece.iPiece, tmp267);
    tmp269 = NofibPrelude.Cons(lastpiece.hPiece, tmp268);
    tmp270 = NofibPrelude.Cons(lastpiece.gPiece, tmp269);
    tmp271 = NofibPrelude.Cons(lastpiece.fPiece, tmp270);
    tmp272 = NofibPrelude.Cons(lastpiece.ePiece, tmp271);
    tmp273 = NofibPrelude.Cons(lastpiece.dPiece, tmp272);
    tmp274 = NofibPrelude.Cons(lastpiece.cPiece, tmp273);
    tmp275 = NofibPrelude.Cons(lastpiece.bPiece, tmp274);
    this.initialPieces = tmp275;
    this.Mode = class Mode {
      constructor() {}
      toString() { return "Mode"; }
    };
    const PageMode$class = class PageMode extends lastpiece.Mode {
      constructor() {
        super();
      }
      toString() { return "PageMode"; }
    };
    this.PageMode = new PageMode$class;
    this.PageMode.class = PageMode$class;
    const ZigZagMode$class = class ZigZagMode extends lastpiece.Mode {
      constructor() {
        super();
      }
      toString() { return "ZigZagMode"; }
    };
    this.ZigZagMode = new ZigZagMode$class;
    this.ZigZagMode.class = ZigZagMode$class;
    const LeftMode$class = class LeftMode extends lastpiece.Mode {
      constructor() {
        super();
      }
      toString() { return "LeftMode"; }
    };
    this.LeftMode = new LeftMode$class;
    this.LeftMode.class = LeftMode$class;
    const OneLineMode$class = class OneLineMode extends lastpiece.Mode {
      constructor() {
        super();
      }
      toString() { return "OneLineMode"; }
    };
    this.OneLineMode = new OneLineMode$class;
    this.OneLineMode.class = OneLineMode$class;
    this.TextDetails = class TextDetails {
      constructor() {}
      toString() { return "TextDetails"; }
    };
    this.Chr = function Chr(c1) {
      return new Chr.class(c1);
    };
    this.Chr.class = class Chr extends lastpiece.TextDetails {
      constructor(c) {
        super();
        this.c = c;
      }
      toString() { return "Chr(" + globalThis.Predef.render(this.c) + ")"; }
    };
    this.Str = function Str(s1) {
      return new Str.class(s1);
    };
    this.Str.class = class Str extends lastpiece.TextDetails {
      constructor(s) {
        super();
        this.s = s;
      }
      toString() { return "Str(" + globalThis.Predef.render(this.s) + ")"; }
    };
    this.PStr = function PStr(s1) {
      return new PStr.class(s1);
    };
    this.PStr.class = class PStr extends lastpiece.TextDetails {
      constructor(s) {
        super();
        this.s = s;
      }
      toString() { return "PStr(" + globalThis.Predef.render(this.s) + ")"; }
    };
    this.AnnotDetails = class AnnotDetails {
      constructor() {}
      toString() { return "AnnotDetails"; }
    };
    const AnnotStart$class = class AnnotStart extends lastpiece.AnnotDetails {
      constructor() {
        super();
      }
      toString() { return "AnnotStart"; }
    };
    this.AnnotStart = new AnnotStart$class;
    this.AnnotStart.class = AnnotStart$class;
    const AnnotEnd$class = class AnnotEnd extends lastpiece.AnnotDetails {
      constructor() {
        super();
      }
      toString() { return "AnnotEnd"; }
    };
    this.AnnotEnd = new AnnotEnd$class;
    this.AnnotEnd.class = AnnotEnd$class;
    this.NoAnnot = function NoAnnot(t1, i1) {
      return new NoAnnot.class(t1, i1);
    };
    this.NoAnnot.class = class NoAnnot extends lastpiece.AnnotDetails {
      constructor(t, i) {
        super();
        this.t = t;
        this.i = i;
      }
      toString() { return "NoAnnot(" + globalThis.Predef.render(this.t) + ", " + globalThis.Predef.render(this.i) + ")"; }
    };
    this.IsEmptyy = class IsEmptyy {
      constructor() {}
      toString() { return "IsEmptyy"; }
    };
    const IsEmpty$class = class IsEmpty extends lastpiece.IsEmptyy {
      constructor() {
        super();
      }
      toString() { return "IsEmpty"; }
    };
    this.IsEmpty = new IsEmpty$class;
    this.IsEmpty.class = IsEmpty$class;
    const NotEmpty$class = class NotEmpty extends lastpiece.IsEmptyy {
      constructor() {
        super();
      }
      toString() { return "NotEmpty"; }
    };
    this.NotEmpty = new NotEmpty$class;
    this.NotEmpty.class = NotEmpty$class;
    this.Doc = class Doc {
      constructor() {}
      toString() { return "Doc"; }
    };
    const Empty$class = class Empty extends lastpiece.Doc {
      constructor() {
        super();
      }
      toString() { return "Empty"; }
    };
    this.Empty = new Empty$class;
    this.Empty.class = Empty$class;
    const NoDoc$class = class NoDoc extends lastpiece.Doc {
      constructor() {
        super();
      }
      toString() { return "NoDoc"; }
    };
    this.NoDoc = new NoDoc$class;
    this.NoDoc.class = NoDoc$class;
    this.NilAbove = function NilAbove(d1) {
      return new NilAbove.class(d1);
    };
    this.NilAbove.class = class NilAbove extends lastpiece.Doc {
      constructor(d) {
        super();
        this.d = d;
      }
      toString() { return "NilAbove(" + globalThis.Predef.render(this.d) + ")"; }
    };
    this.TextBeside = function TextBeside(a1, d1) {
      return new TextBeside.class(a1, d1);
    };
    this.TextBeside.class = class TextBeside extends lastpiece.Doc {
      constructor(a, d) {
        super();
        this.a = a;
        this.d = d;
      }
      toString() { return "TextBeside(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.d) + ")"; }
    };
    this.Nest = function Nest(i1, d1) {
      return new Nest.class(i1, d1);
    };
    this.Nest.class = class Nest extends lastpiece.Doc {
      constructor(i, d) {
        super();
        this.i = i;
        this.d = d;
      }
      toString() { return "Nest(" + globalThis.Predef.render(this.i) + ", " + globalThis.Predef.render(this.d) + ")"; }
    };
    this.Union = function Union(d11, d21) {
      return new Union.class(d11, d21);
    };
    this.Union.class = class Union extends lastpiece.Doc {
      constructor(d1, d2) {
        super();
        this.d1 = d1;
        this.d2 = d2;
      }
      toString() { return "Union(" + globalThis.Predef.render(this.d1) + ", " + globalThis.Predef.render(this.d2) + ")"; }
    };
    this.Beside = function Beside(d11, b1, d21) {
      return new Beside.class(d11, b1, d21);
    };
    this.Beside.class = class Beside extends lastpiece.Doc {
      constructor(d1, b, d2) {
        super();
        this.d1 = d1;
        this.b = b;
        this.d2 = d2;
      }
      toString() { return "Beside(" + globalThis.Predef.render(this.d1) + ", " + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.d2) + ")"; }
    };
    this.Above = function Above(d11, b1, d21) {
      return new Above.class(d11, b1, d21);
    };
    this.Above.class = class Above extends lastpiece.Doc {
      constructor(d1, b, d2) {
        super();
        this.d1 = d1;
        this.b = b;
        this.d2 = d2;
      }
      toString() { return "Above(" + globalThis.Predef.render(this.d1) + ", " + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.d2) + ")"; }
    };
    tmp276 = lastpiece.Chr(" ");
    tmp277 = lastpiece.NoAnnot(tmp276, 1);
    this.spaceText = tmp277;
    tmp278 = lastpiece.Chr("\n");
    tmp279 = lastpiece.NoAnnot(tmp278, 1);
    this.nlText = tmp279;
    lambda = (undefined, function () {
      let tmp281, tmp282;
      tmp281 = lastpiece.testLastPiece_nofib();
      tmp282 = NofibPrelude.nofibListToString(tmp281);
      return BenchmarkPrelude.print(tmp282)
    });
    tmp280 = lambda;
    BenchmarkPrelude.benchmark(tmp280)
  }
  static isSome(x) {
    if (x instanceof NofibPrelude.Some.class) {
      return true
    } else {
      return false
    }
  } 
  static mapMaybe(f, ls) {
    let param0, param1, h, t, scrut, param01, a, tmp;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      h = param0;
      t = param1;
      scrut = runtime.safeCall(f(h));
      if (scrut instanceof NofibPrelude.None.class) {
        return lastpiece.mapMaybe(f, t)
      } else if (scrut instanceof NofibPrelude.Some.class) {
        param01 = scrut.x;
        a = param01;
        tmp = lastpiece.mapMaybe(f, t);
        return NofibPrelude.Cons(a, tmp)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static compareIntInt(ab, cd) {
    let first1, first0, a, b, first11, first01, c, d, scrut, scrut1, scrut2, scrut3;
    if (globalThis.Array.isArray(ab) && ab.length === 2) {
      first0 = ab[0];
      first1 = ab[1];
      a = first0;
      b = first1;
      if (globalThis.Array.isArray(cd) && cd.length === 2) {
        first01 = cd[0];
        first11 = cd[1];
        c = first01;
        d = first11;
        scrut3 = a > c;
        if (scrut3 === true) {
          return lastpiece.GT
        } else {
          scrut2 = a < c;
          if (scrut2 === true) {
            return lastpiece.LT
          } else {
            scrut1 = b > d;
            if (scrut1 === true) {
              return lastpiece.GT
            } else {
              scrut = b < d;
              if (scrut === true) {
                return lastpiece.LT
              } else {
                return lastpiece.EQ
              }
            }
          }
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static mapLookup(k, m) {
    let param0, param1, param2, param3, param4, kx, x1, l, r, scrut;
    if (m instanceof lastpiece.Tip.class) {
      return NofibPrelude.None
    } else if (m instanceof lastpiece.Bin.class) {
      param0 = m.i;
      param1 = m.k;
      param2 = m.v;
      param3 = m.l;
      param4 = m.r;
      kx = param1;
      x1 = param2;
      l = param3;
      r = param4;
      scrut = lastpiece.compareIntInt(k, kx);
      if (scrut instanceof lastpiece.LT.class) {
        return lastpiece.mapLookup(k, l)
      } else if (scrut instanceof lastpiece.GT.class) {
        return lastpiece.mapLookup(k, r)
      } else if (scrut instanceof lastpiece.EQ.class) {
        return NofibPrelude.Some(x1)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static size(p) {
    let param0, param1, param2, param3, param4, sz;
    if (p instanceof lastpiece.Tip.class) {
      return 0
    } else if (p instanceof lastpiece.Bin.class) {
      param0 = p.i;
      param1 = p.k;
      param2 = p.v;
      param3 = p.l;
      param4 = p.r;
      sz = param0;
      return sz
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static bin(k1, x1, l, r) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = lastpiece.size(l);
    tmp1 = lastpiece.size(r);
    tmp2 = tmp + tmp1;
    tmp3 = tmp2 + 1;
    return lastpiece.Bin(tmp3, k1, x1, l, r)
  } 
  static singleL(k11, x11, t1, r1) {
    let param0, param1, param2, param3, param4, k2, x2, t2, t3, tmp;
    if (r1 instanceof lastpiece.Bin.class) {
      param0 = r1.i;
      param1 = r1.k;
      param2 = r1.v;
      param3 = r1.l;
      param4 = r1.r;
      k2 = param1;
      x2 = param2;
      t2 = param3;
      t3 = param4;
      tmp = lastpiece.bin(k11, x11, t1, t2);
      return lastpiece.bin(k2, x2, tmp, t3)
    } else {
      throw globalThis.Error("singleL Tip");
    }
  } 
  static singleR(k12, x12, l1, t3) {
    let param0, param1, param2, param3, param4, k2, x2, t11, t2, tmp;
    if (l1 instanceof lastpiece.Bin.class) {
      param0 = l1.i;
      param1 = l1.k;
      param2 = l1.v;
      param3 = l1.l;
      param4 = l1.r;
      k2 = param1;
      x2 = param2;
      t11 = param3;
      t2 = param4;
      tmp = lastpiece.bin(k12, x12, t2, t3);
      return lastpiece.bin(k2, x2, t11, tmp)
    } else {
      throw globalThis.Error("singleR Tip");
    }
  } 
  static doubleL(k13, x13, t11, r2) {
    let param0, param1, param2, param3, param4, k2, x2, param01, param11, param21, param31, param41, k3, x3, t2, t31, t4, tmp, tmp1;
    if (r2 instanceof lastpiece.Bin.class) {
      param0 = r2.i;
      param1 = r2.k;
      param2 = r2.v;
      param3 = r2.l;
      param4 = r2.r;
      k2 = param1;
      x2 = param2;
      if (param3 instanceof lastpiece.Bin.class) {
        param01 = param3.i;
        param11 = param3.k;
        param21 = param3.v;
        param31 = param3.l;
        param41 = param3.r;
        k3 = param11;
        x3 = param21;
        t2 = param31;
        t31 = param41;
        t4 = param4;
        tmp = lastpiece.bin(k13, x13, t11, t2);
        tmp1 = lastpiece.bin(k2, x2, t31, t4);
        return lastpiece.bin(k3, x3, tmp, tmp1)
      } else {
        throw globalThis.Error("doubleL Tip");
      }
    } else {
      throw globalThis.Error("doubleL Tip");
    }
  } 
  static doubleR(k14, x14, l2, t4) {
    let param0, param1, param2, param3, param4, k2, x2, t12, param01, param11, param21, param31, param41, k3, x3, t2, t31, tmp, tmp1;
    if (l2 instanceof lastpiece.Bin.class) {
      param0 = l2.i;
      param1 = l2.k;
      param2 = l2.v;
      param3 = l2.l;
      param4 = l2.r;
      k2 = param1;
      x2 = param2;
      t12 = param3;
      if (param4 instanceof lastpiece.Bin.class) {
        param01 = param4.i;
        param11 = param4.k;
        param21 = param4.v;
        param31 = param4.l;
        param41 = param4.r;
        k3 = param11;
        x3 = param21;
        t2 = param31;
        t31 = param41;
        tmp = lastpiece.bin(k2, x2, t12, t2);
        tmp1 = lastpiece.bin(k14, x14, t31, t4);
        return lastpiece.bin(k3, x3, tmp, tmp1)
      } else {
        throw globalThis.Error("doubleR Tip");
      }
    } else {
      throw globalThis.Error("doubleR Tip");
    }
  } 
  static rotateL(k2, x2, l3, r3) {
    let param0, param1, param2, param3, param4, ly, ry, scrut, tmp, tmp1, tmp2;
    if (r3 instanceof lastpiece.Bin.class) {
      param0 = r3.i;
      param1 = r3.k;
      param2 = r3.v;
      param3 = r3.l;
      param4 = r3.r;
      ly = param3;
      ry = param4;
      tmp = lastpiece.size(ly);
      tmp1 = lastpiece.size(ry);
      tmp2 = 2 * tmp1;
      scrut = tmp < tmp2;
      if (scrut === true) {
        return lastpiece.singleL(k2, x2, l3, r3)
      } else {
        return lastpiece.doubleL(k2, x2, l3, r3)
      }
    } else {
      throw globalThis.Error("rotateL Tip");
    }
  } 
  static rotateR(k3, x3, l4, r4) {
    let param0, param1, param2, param3, param4, ly, ry, scrut, tmp, tmp1, tmp2;
    if (l4 instanceof lastpiece.Bin.class) {
      param0 = l4.i;
      param1 = l4.k;
      param2 = l4.v;
      param3 = l4.l;
      param4 = l4.r;
      ly = param3;
      ry = param4;
      tmp = lastpiece.size(ry);
      tmp1 = lastpiece.size(ly);
      tmp2 = 2 * tmp1;
      scrut = tmp < tmp2;
      if (scrut === true) {
        return lastpiece.singleR(k3, x3, l4, r4)
      } else {
        return lastpiece.doubleR(k3, x3, l4, r4)
      }
    } else {
      throw globalThis.Error("rotateR Tip");
    }
  } 
  static balance(k4, x4, l5, r5) {
    let sizeL, sizeR, sizeX, scrut, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = lastpiece.size(l5);
    sizeL = tmp;
    tmp1 = lastpiece.size(r5);
    sizeR = tmp1;
    tmp2 = sizeL + sizeR;
    tmp3 = tmp2 + 1;
    sizeX = tmp3;
    tmp4 = sizeL + sizeR;
    scrut2 = tmp4 <= 1;
    if (scrut2 === true) {
      return lastpiece.Bin(sizeX, k4, x4, l5, r5)
    } else {
      tmp5 = 4 * sizeL;
      scrut1 = sizeR >= tmp5;
      if (scrut1 === true) {
        return lastpiece.rotateL(k4, x4, l5, r5)
      } else {
        tmp6 = 4 * sizeR;
        scrut = sizeL >= tmp6;
        if (scrut === true) {
          return lastpiece.rotateR(k4, x4, l5, r5)
        } else {
          return lastpiece.Bin(sizeX, k4, x4, l5, r5)
        }
      }
    }
  } 
  static insert(kx, x5, m1) {
    let param0, param1, param2, param3, param4, sz, ky, y, l6, r6, scrut, tmp, tmp1;
    if (m1 instanceof lastpiece.Tip.class) {
      return lastpiece.Bin(1, kx, x5, lastpiece.Tip, lastpiece.Tip)
    } else if (m1 instanceof lastpiece.Bin.class) {
      param0 = m1.i;
      param1 = m1.k;
      param2 = m1.v;
      param3 = m1.l;
      param4 = m1.r;
      sz = param0;
      ky = param1;
      y = param2;
      l6 = param3;
      r6 = param4;
      scrut = lastpiece.compareIntInt(kx, ky);
      if (scrut instanceof lastpiece.LT.class) {
        tmp = lastpiece.insert(kx, x5, l6);
        return lastpiece.balance(ky, y, tmp, r6)
      } else if (scrut instanceof lastpiece.GT.class) {
        tmp1 = lastpiece.insert(kx, x5, r6);
        return lastpiece.balance(ky, y, l6, tmp1)
      } else if (scrut instanceof lastpiece.EQ.class) {
        return lastpiece.Bin(sz, kx, x5, l6, r6)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static indent(n) {
    let scrut, tmp, tmp1;
    scrut = n <= 0;
    if (scrut === true) {
      return NofibPrelude.Nil
    } else {
      tmp = n - 1;
      tmp1 = lastpiece.indent(tmp);
      return NofibPrelude.Cons(" ", tmp1)
    }
  } 
  static flip(s) {
    if (s instanceof lastpiece.Male.class) {
      return lastpiece.Female
    } else if (s instanceof lastpiece.Female.class) {
      return lastpiece.Male
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static addIntInt(row_col, orow_ocol) {
    let first1, first0, row, col, first11, first01, orow, ocol, tmp, tmp1;
    if (globalThis.Array.isArray(row_col) && row_col.length === 2) {
      first0 = row_col[0];
      first1 = row_col[1];
      row = first0;
      col = first1;
      if (globalThis.Array.isArray(orow_ocol) && orow_ocol.length === 2) {
        first01 = orow_ocol[0];
        first11 = orow_ocol[1];
        orow = first01;
        ocol = first11;
        tmp = row + orow;
        tmp1 = col + ocol;
        return [
          tmp,
          tmp1
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static next(row_col1) {
    let first1, first0, row, col, tmp;
    if (globalThis.Array.isArray(row_col1) && row_col1.length === 2) {
      first0 = row_col1[0];
      first1 = row_col1[1];
      row = first0;
      col = first1;
      tmp = col + 1;
      return [
        row,
        tmp
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static check(bd, sq) {
    return lastpiece.mapLookup(sq, bd)
  } 
  static extend(bd1, sq1, id) {
    return lastpiece.insert(sq1, id, bd1)
  } 
  static extend_maybe(bd2, sq2, id1) {
    let first1, first0, row, col, scrut, param0, scrut1, tmp, tmp1, tmp2, tmp3, tmp4;
    if (globalThis.Array.isArray(sq2) && sq2.length === 2) {
      first0 = sq2[0];
      first1 = sq2[1];
      row = first0;
      col = first1;
      tmp = row > lastpiece.maxRow;
      tmp1 = col < 1;
      tmp2 = tmp || tmp1;
      tmp3 = col > lastpiece.maxCol;
      scrut1 = tmp2 || tmp3;
      if (scrut1 === true) {
        return NofibPrelude.None
      } else {
        scrut = lastpiece.check(bd2, sq2);
        if (scrut instanceof NofibPrelude.Some.class) {
          param0 = scrut.x;
          return NofibPrelude.None
        } else if (scrut instanceof NofibPrelude.None.class) {
          tmp4 = lastpiece.extend(bd2, sq2, id1);
          return NofibPrelude.Some(tmp4)
        } else {
          throw new globalThis.Error("match error");
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static pickOne(xs) {
    let go, lambda;
    go = function go(f1, xs1) {
      let param0, param1, x6, xs2, tmp, tmp1, lambda1;
      if (xs1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (xs1 instanceof NofibPrelude.Cons.class) {
        param0 = xs1.head;
        param1 = xs1.tail;
        x6 = param0;
        xs2 = param1;
        tmp = runtime.safeCall(f1(xs2));
        lambda1 = (undefined, function (p1) {
          let tmp2;
          tmp2 = runtime.safeCall(f1(p1));
          return NofibPrelude.Cons(x6, tmp2)
        });
        tmp1 = go(lambda1, xs2);
        return NofibPrelude.Cons([
          x6,
          tmp
        ], tmp1)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    lambda = (undefined, function (x6) {
      return x6
    });
    return go(lambda, xs)
  } 
  static fit(bd3, sq3, id2, os) {
    let param0, param1, o, os1, scrut, param01, bd11, tmp, tmp1;
    if (os instanceof NofibPrelude.Nil.class) {
      tmp = lastpiece.extend(bd3, sq3, id2);
      return NofibPrelude.Some(tmp)
    } else if (os instanceof NofibPrelude.Cons.class) {
      param0 = os.head;
      param1 = os.tail;
      o = param0;
      os1 = param1;
      tmp1 = lastpiece.addIntInt(sq3, o);
      scrut = lastpiece.extend_maybe(bd3, tmp1, id2);
      if (scrut instanceof NofibPrelude.Some.class) {
        param01 = scrut.x;
        bd11 = param01;
        return lastpiece.fit(bd11, sq3, id2, os1)
      } else if (scrut instanceof NofibPrelude.None.class) {
        return NofibPrelude.None
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static tryy(sq4, se, bd4, id_is_ps) {
    let first2, first1, first0, id3, os1, ps, scrut, param0, bd11, tmp, tmp1, tmp2;
    if (globalThis.Array.isArray(id_is_ps) && id_is_ps.length === 3) {
      first0 = id_is_ps[0];
      first1 = id_is_ps[1];
      first2 = id_is_ps[2];
      id3 = first0;
      os1 = first1;
      ps = first2;
      scrut = lastpiece.fit(bd4, sq4, id3, os1);
      if (scrut instanceof NofibPrelude.Some.class) {
        param0 = scrut.x;
        bd11 = param0;
        tmp = lastpiece.next(sq4);
        tmp1 = lastpiece.flip(se);
        tmp2 = lastpiece.search(tmp, tmp1, bd11, ps);
        return NofibPrelude.Some(tmp2)
      } else if (scrut instanceof NofibPrelude.None.class) {
        return NofibPrelude.None
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static search(row_col2, sey, bd5, ps) {
    let lscomp1, first1, first0, row, col, choices, scrut, ss, scrut1, param0, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, lambda;
    if (globalThis.Array.isArray(row_col2) && row_col2.length === 2) {
      first0 = row_col2[0];
      first1 = row_col2[1];
      row = first0;
      col = first1;
      if (ps instanceof NofibPrelude.Nil.class) {
        return lastpiece.Soln(bd5)
      } else {
        tmp = lastpiece.maxCol + 1;
        scrut2 = col === tmp;
        if (scrut2 === true) {
          tmp1 = row + 1;
          tmp2 = lastpiece.flip(sey);
          return lastpiece.search([
            tmp1,
            1
          ], tmp2, bd5, ps)
        } else {
          scrut1 = lastpiece.check(bd5, row_col2);
          if (scrut1 instanceof NofibPrelude.Some.class) {
            param0 = scrut1.x;
            tmp3 = lastpiece.next(row_col2);
            tmp4 = lastpiece.flip(sey);
            return lastpiece.search(tmp3, tmp4, bd5, ps)
          } else {
            lscomp1 = function lscomp1(ls1) {
              let lscomp2, param01, param1, first11, first01, param02, param11, param2, id3, ms, fs1, ps1, ls2, tmp7;
              if (ls1 instanceof NofibPrelude.Nil.class) {
                return NofibPrelude.Nil
              } else if (ls1 instanceof NofibPrelude.Cons.class) {
                param01 = ls1.head;
                param1 = ls1.tail;
                if (globalThis.Array.isArray(param01) && param01.length === 2) {
                  first01 = param01[0];
                  first11 = param01[1];
                  if (first01 instanceof lastpiece.P.class) {
                    param02 = first01.i;
                    param11 = first01.a;
                    param2 = first01.b;
                    id3 = param02;
                    ms = param11;
                    fs1 = param2;
                    ps1 = first11;
                    ls2 = param1;
                    lscomp2 = function lscomp2(ls21) {
                      let param03, param12, os1, ls3, tmp8;
                      if (ls21 instanceof NofibPrelude.Nil.class) {
                        return lscomp1(ls2)
                      } else if (ls21 instanceof NofibPrelude.Cons.class) {
                        param03 = ls21.head;
                        param12 = ls21.tail;
                        os1 = param03;
                        ls3 = param12;
                        tmp8 = lscomp2(ls3);
                        return NofibPrelude.Cons([
                          id3,
                          os1,
                          ps1
                        ], tmp8)
                      } else {
                        throw new globalThis.Error("match error");
                      }
                    };
                    if (sey instanceof lastpiece.Male.class) {
                      tmp7 = ms;
                    } else {
                      tmp7 = fs1;
                    }
                    return lscomp2(tmp7)
                  } else {
                    throw new globalThis.Error("match error");
                  }
                } else {
                  throw new globalThis.Error("match error");
                }
              } else {
                throw new globalThis.Error("match error");
              }
            };
            tmp5 = lastpiece.pickOne(ps);
            tmp6 = lscomp1(tmp5);
            choices = tmp6;
            lambda = (undefined, function (x6) {
              return lastpiece.tryy(row_col2, sey, bd5, x6)
            });
            scrut = lastpiece.mapMaybe(lambda, choices);
            if (scrut instanceof NofibPrelude.Nil.class) {
              return lastpiece.Fail(bd5, row_col2)
            } else {
              ss = scrut;
              return lastpiece.Choose(ss)
            }
          }
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static annotSize(p1) {
    let param0, param1, l6;
    if (p1 instanceof lastpiece.NoAnnot.class) {
      param0 = p1.t;
      param1 = p1.i;
      l6 = param1;
      return l6
    } else {
      return 0
    }
  } 
  static display(s1) {
    let param0, param1, bd6, first1, first0, row, col, param01, ss, param02, bd7, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    if (s1 instanceof lastpiece.Soln.class) {
      param02 = s1.b;
      bd7 = param02;
      tmp = NofibPrelude.nofibStringToList("Success!");
      tmp1 = lastpiece.text(tmp);
      tmp2 = lastpiece.displayBoard(bd7);
      tmp3 = lastpiece.nest(2, tmp2);
      tmp4 = NofibPrelude.Cons(tmp3, NofibPrelude.Nil);
      tmp5 = NofibPrelude.Cons(tmp1, tmp4);
      return lastpiece.vcat(tmp5)
    } else if (s1 instanceof lastpiece.Choose.class) {
      param01 = s1.s;
      ss = param01;
      tmp6 = NofibPrelude.map(lastpiece.display, ss);
      return lastpiece.vcat(tmp6)
    } else if (s1 instanceof lastpiece.Fail.class) {
      param0 = s1.b;
      param1 = s1.s;
      bd6 = param0;
      if (globalThis.Array.isArray(param1) && param1.length === 2) {
        first0 = param1[0];
        first1 = param1[1];
        row = first0;
        col = first1;
        return lastpiece.Empty
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static displayBoard(bd6) {
    let row, sq5, tmp, tmp1, tmp2, tmp3;
    sq5 = function sq(n1, col) {
      let scrut, param0, id3;
      scrut = lastpiece.check(bd6, [
        n1,
        col
      ]);
      if (scrut instanceof NofibPrelude.Some.class) {
        param0 = scrut.x;
        id3 = param0;
        return lastpiece.char(id3)
      } else if (scrut instanceof NofibPrelude.None.class) {
        return lastpiece.char(".")
      } else {
        throw new globalThis.Error("match error");
      }
    };
    row = function row(n1) {
      let tmp4, tmp5, lambda;
      tmp4 = NofibPrelude.enumFromTo(1, lastpiece.maxCol);
      lambda = (undefined, function (col) {
        return sq5(n1, col)
      });
      tmp5 = NofibPrelude.map(lambda, tmp4);
      return lastpiece.hcat(tmp5)
    };
    tmp = NofibPrelude.enumFromTo(1, lastpiece.maxCol);
    tmp1 = NofibPrelude.map(row, tmp);
    tmp2 = lastpiece.vcat(tmp1);
    tmp3 = lastpiece.text(NofibPrelude.Nil);
    return lastpiece.above_(tmp2, false, tmp3)
  } 
  static eliminateEmpty(cons, p2, g, q) {
    let first1, first0, q1, tmp;
    if (p2 instanceof lastpiece.Empty.class) {
      return q
    } else {
      if (globalThis.Array.isArray(q) && q.length === 2) {
        first0 = q[0];
        first1 = q[1];
        if (first0 instanceof lastpiece.NotEmpty.class) {
          q1 = first1;
          tmp = runtime.safeCall(cons(p2, g, q1));
        } else if (first0 instanceof lastpiece.IsEmpty.class) {
          tmp = p2;
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
      return [
        lastpiece.NotEmpty,
        tmp
      ]
    }
  } 
  static reduceVert(doc) {
    let param0, param1, param2, p3, g1, q1, tmp, tmp1, tmp2, lambda;
    if (doc instanceof lastpiece.Above.class) {
      param0 = doc.d1;
      param1 = doc.b;
      param2 = doc.d2;
      p3 = param0;
      g1 = param1;
      q1 = param2;
      tmp = lastpiece.reduceVert(p3);
      tmp1 = NofibPrelude.snd(tmp);
      tmp2 = lastpiece.reduceVert(q1);
      lambda = (undefined, function (a, b, c) {
        return lastpiece.Above(a, b, c)
      });
      return lastpiece.eliminateEmpty(lambda, tmp1, g1, tmp2)
    } else {
      return [
        lastpiece.NotEmpty,
        doc
      ]
    }
  } 
  static vcat(ls1) {
    let tmp, tmp1, lambda;
    lambda = (undefined, function (p3, q1) {
      return lastpiece.Above(p3, false, q1)
    });
    tmp = NofibPrelude.foldr(lambda, lastpiece.Empty, ls1);
    tmp1 = lastpiece.reduceVert(tmp);
    return NofibPrelude.snd(tmp1)
  } 
  static text(s2) {
    let sl, tmp, tmp1, tmp2;
    tmp = NofibPrelude.listLen(s2);
    sl = tmp;
    tmp1 = lastpiece.Str(s2);
    tmp2 = lastpiece.NoAnnot(tmp1, sl);
    return lastpiece.TextBeside(tmp2, lastpiece.Empty)
  } 
  static char(c) {
    let tmp, tmp1;
    tmp = lastpiece.Chr(c);
    tmp1 = lastpiece.NoAnnot(tmp, 1);
    return lastpiece.TextBeside(tmp1, lastpiece.Empty)
  } 
  static reduceHoriz(doc1) {
    let param0, param1, param2, p3, g1, q1, tmp, tmp1, tmp2, lambda;
    if (doc1 instanceof lastpiece.Beside.class) {
      param0 = doc1.d1;
      param1 = doc1.b;
      param2 = doc1.d2;
      p3 = param0;
      g1 = param1;
      q1 = param2;
      tmp = lastpiece.reduceHoriz(p3);
      tmp1 = NofibPrelude.snd(tmp);
      tmp2 = lastpiece.reduceHoriz(q1);
      lambda = (undefined, function (a, b, c1) {
        return lastpiece.Beside(a, b, c1)
      });
      return lastpiece.eliminateEmpty(lambda, tmp1, g1, tmp2)
    } else {
      return [
        lastpiece.NotEmpty,
        doc1
      ]
    }
  } 
  static hcat(ls2) {
    let tmp, tmp1, lambda;
    lambda = (undefined, function (p3, q1) {
      return lastpiece.Beside(p3, false, q1)
    });
    tmp = NofibPrelude.foldr(lambda, lastpiece.Empty, ls2);
    tmp1 = lastpiece.reduceHoriz(tmp);
    return NofibPrelude.snd(tmp1)
  } 
  static above_(p3, g1, q1) {
    if (q1 instanceof lastpiece.Empty.class) {
      return p3
    } else {
      if (g1 instanceof lastpiece.Empty.class) {
        return q1
      } else {
        return lastpiece.Above(p3, g1, q1)
      }
    }
  } 
  static nest(k5, p4) {
    let tmp;
    tmp = lastpiece.reduceDoc(p4);
    return lastpiece.mkNest(k5, tmp)
  } 
  static mkNest(k6, p5) {
    let scrut, param0, param1, k15, p11, tmp;
    if (p5 instanceof lastpiece.Nest.class) {
      param0 = p5.i;
      param1 = p5.d;
      k15 = param0;
      p11 = param1;
      tmp = k6 + k15;
      return lastpiece.mkNest(tmp, p11)
    } else if (p5 instanceof lastpiece.NoDoc.class) {
      return lastpiece.NoDoc
    } else if (p5 instanceof lastpiece.Empty.class) {
      return lastpiece.Empty
    } else {
      scrut = k6 === 0;
      if (scrut === true) {
        return p5
      } else {
        return lastpiece.Nest(k6, p5)
      }
    }
  } 
  static reduceDoc(p6) {
    let param0, param1, param2, p11, g2, q2, param01, param11, param21, p12, g3, q3, tmp, tmp1;
    if (p6 instanceof lastpiece.Beside.class) {
      param01 = p6.d1;
      param11 = p6.b;
      param21 = p6.d2;
      p12 = param01;
      g3 = param11;
      q3 = param21;
      tmp = lastpiece.reduceDoc(q3);
      return lastpiece.beside(p12, g3, tmp)
    } else if (p6 instanceof lastpiece.Above.class) {
      param0 = p6.d1;
      param1 = p6.b;
      param2 = p6.d2;
      p11 = param0;
      g2 = param1;
      q2 = param2;
      tmp1 = lastpiece.reduceDoc(q2);
      return lastpiece.above(p11, g2, tmp1)
    } else {
      return p6
    }
  } 
  static beside(p7, g2, q2) {
    let param0, param1, t, p11, rest, param01, p12, param02, param11, param2, param03, param12, param21, p13, g11, q11, scrut, param04, param13, k7, p14, param05, param14, p15, p21, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    if (p7 instanceof lastpiece.NoDoc.class) {
      return lastpiece.NoDoc
    } else if (p7 instanceof lastpiece.Union.class) {
      param05 = p7.d1;
      param14 = p7.d2;
      p15 = param05;
      p21 = param14;
      tmp = lastpiece.beside(p15, g2, q2);
      tmp1 = lastpiece.beside(p21, g2, q2);
      return lastpiece.Union(tmp, tmp1)
    } else if (p7 instanceof lastpiece.Empty.class) {
      return q2
    } else if (p7 instanceof lastpiece.Nest.class) {
      param04 = p7.i;
      param13 = p7.d;
      k7 = param04;
      p14 = param13;
      tmp2 = lastpiece.beside(p14, g2, q2);
      return lastpiece.Nest(k7, tmp2)
    } else if (p7 instanceof lastpiece.Beside.class) {
      param03 = p7.d1;
      param12 = p7.b;
      param21 = p7.d2;
      p13 = param03;
      g11 = param12;
      q11 = param21;
      scrut = g11 === g2;
      if (scrut === true) {
        tmp3 = lastpiece.beside(q11, g2, q2);
        return lastpiece.beside(p13, g11, tmp3)
      } else {
        tmp4 = lastpiece.Beside(p13, g11, q11);
        tmp5 = lastpiece.reduceDoc(tmp4);
        return lastpiece.beside(tmp5, g2, q2)
      }
    } else if (p7 instanceof lastpiece.Above.class) {
      param02 = p7.d1;
      param11 = p7.b;
      param2 = p7.d2;
      tmp6 = lastpiece.reduceDoc(p7);
      return lastpiece.beside(tmp6, g2, q2)
    } else if (p7 instanceof lastpiece.NilAbove.class) {
      param01 = p7.d;
      p12 = param01;
      tmp7 = lastpiece.beside(p12, g2, q2);
      return lastpiece.NilAbove(tmp7)
    } else if (p7 instanceof lastpiece.TextBeside.class) {
      param0 = p7.a;
      param1 = p7.d;
      t = param0;
      p11 = param1;
      if (p11 instanceof lastpiece.Empty.class) {
        tmp8 = lastpiece.nilBeside(g2, q2);
      } else {
        tmp8 = lastpiece.beside(p11, g2, q2);
      }
      rest = tmp8;
      return lastpiece.TextBeside(t, rest)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static above(p8, g3, q3) {
    let param0, param1, param2, param01, param11, param21, p11, g11, q11, tmp, tmp1, tmp2, tmp3;
    if (p8 instanceof lastpiece.Above.class) {
      param01 = p8.d1;
      param11 = p8.b;
      param21 = p8.d2;
      p11 = param01;
      g11 = param11;
      q11 = param21;
      tmp = lastpiece.above(q11, g3, q3);
      return lastpiece.above(p11, g11, tmp)
    } else if (p8 instanceof lastpiece.Beside.class) {
      param0 = p8.d1;
      param1 = p8.b;
      param2 = p8.d2;
      tmp1 = lastpiece.reduceDoc(p8);
      tmp2 = lastpiece.reduceDoc(q3);
      return lastpiece.aboveNest(tmp1, g3, 0, tmp2)
    } else {
      tmp3 = lastpiece.reduceDoc(q3);
      return lastpiece.aboveNest(p8, g3, 0, tmp3)
    }
  } 
  static nilBeside(g4, p9) {
    let param0, param1, p11;
    if (p9 instanceof lastpiece.Empty.class) {
      return lastpiece.Empty
    } else if (p9 instanceof lastpiece.Nest.class) {
      param0 = p9.i;
      param1 = p9.d;
      p11 = param1;
      return lastpiece.nilBeside(g4, p11)
    } else {
      if (g4 === true) {
        return lastpiece.TextBeside(lastpiece.spaceText, p9)
      } else {
        return p9
      }
    }
  } 
  static aboveNest(p10, g5, k7, q4) {
    let param0, param1, param2, param01, param11, param21, param02, param12, s3, p11, k15, rest, param03, p12, param04, param13, k16, p13, param05, param14, p14, p21, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    if (p10 instanceof lastpiece.NoDoc.class) {
      return lastpiece.NoDoc
    } else if (p10 instanceof lastpiece.Union.class) {
      param05 = p10.d1;
      param14 = p10.d2;
      p14 = param05;
      p21 = param14;
      tmp = lastpiece.aboveNest(p14, g5, k7, q4);
      tmp1 = lastpiece.aboveNest(p21, g5, k7, q4);
      return lastpiece.Union(tmp, tmp1)
    } else if (p10 instanceof lastpiece.Empty.class) {
      return lastpiece.mkNest(k7, q4)
    } else if (p10 instanceof lastpiece.Nest.class) {
      param04 = p10.i;
      param13 = p10.d;
      k16 = param04;
      p13 = param13;
      tmp2 = k7 - k16;
      tmp3 = lastpiece.aboveNest(p13, g5, tmp2, q4);
      return lastpiece.Nest(k16, tmp3)
    } else if (p10 instanceof lastpiece.NilAbove.class) {
      param03 = p10.d;
      p12 = param03;
      tmp4 = lastpiece.aboveNest(p12, g5, k7, q4);
      return lastpiece.NilAbove(tmp4)
    } else if (p10 instanceof lastpiece.TextBeside.class) {
      param02 = p10.a;
      param12 = p10.d;
      s3 = param02;
      p11 = param12;
      tmp5 = lastpiece.annotSize(s3);
      tmp6 = k7 - tmp5;
      k15 = tmp6;
      if (p11 instanceof lastpiece.Empty.class) {
        tmp7 = lastpiece.nilAboveNest(g5, k15, q4);
      } else {
        tmp7 = lastpiece.aboveNest(p11, g5, k15, q4);
      }
      rest = tmp7;
      return lastpiece.TextBeside(s3, rest)
    } else if (p10 instanceof lastpiece.Above.class) {
      param01 = p10.d1;
      param11 = p10.b;
      param21 = p10.d2;
      throw globalThis.Error("aboveNest Above");
    } else if (p10 instanceof lastpiece.Beside.class) {
      param0 = p10.d1;
      param1 = p10.b;
      param2 = p10.d2;
      throw globalThis.Error("aboveNest Beside");
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static nilAboveNest(g6, k8, q5) {
    let scrut, scrut1, param0, param1, k15, q11, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    if (q5 instanceof lastpiece.Empty.class) {
      return lastpiece.Empty
    } else if (q5 instanceof lastpiece.Nest.class) {
      param0 = q5.i;
      param1 = q5.d;
      k15 = param0;
      q11 = param1;
      tmp = k8 + k15;
      return lastpiece.nilAboveNest(g6, tmp, q11)
    } else {
      scrut = BenchmarkPrelude.not(g6);
      if (scrut === true) {
        scrut1 = k8 > 0;
        if (scrut1 === true) {
          tmp1 = lastpiece.indent(k8);
          tmp2 = lastpiece.Str(tmp1);
          tmp3 = lastpiece.NoAnnot(tmp2, k8);
          return lastpiece.TextBeside(tmp3, q5)
        } else {
          tmp4 = lastpiece.mkNest(k8, q5);
          return lastpiece.NilAbove(tmp4)
        }
      } else {
        tmp5 = lastpiece.mkNest(k8, q5);
        return lastpiece.NilAbove(tmp5)
      }
    }
  } 
  static printDoc(d) {
    let put, done, tmp;
    put = function put(k9, next) {
      let param0, s3, param01, s4, param02, c1;
      if (k9 instanceof lastpiece.Chr.class) {
        param02 = k9.c;
        c1 = param02;
        return NofibPrelude.Cons(c1, next)
      } else if (k9 instanceof lastpiece.Str.class) {
        param01 = k9.s;
        s4 = param01;
        return NofibPrelude.append(s4, next)
      } else if (k9 instanceof lastpiece.PStr.class) {
        param0 = k9.s;
        s3 = param0;
        return NofibPrelude.append(s3, next)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = NofibPrelude.Cons("\n", NofibPrelude.Nil);
    done = tmp;
    return lastpiece.fullRender(lastpiece.ZigZagMode, 200, 1.5, put, done, d)
  } 
  static fullRender(m2, l6, r6, txt, a, b) {
    let annTxt;
    annTxt = function annTxt(p11, x6) {
      let param0, param1, s3;
      if (p11 instanceof lastpiece.NoAnnot.class) {
        param0 = p11.t;
        param1 = p11.i;
        s3 = param0;
        return runtime.safeCall(txt(s3, x6))
      } else {
        return x6
      }
    };
    return lastpiece.fullRenderAnn(m2, l6, r6, annTxt, a, b)
  } 
  static ceiling(x6) {
    return runtime.safeCall(globalThis.Math.ceil(x6))
  } 
  static fullRenderAnn(m3, lineLen, ribbons, txt1, rest, doc2) {
    let ribbonLen, bestLineLen, doc11, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, lambda;
    if (m3 instanceof lastpiece.OneLineMode.class) {
      tmp = lastpiece.reduceDoc(doc2);
      lambda = (undefined, function (a1, b1) {
        return b1
      });
      return lastpiece.easyDisplay(lastpiece.spaceText, lambda, txt1, rest, tmp)
    } else if (m3 instanceof lastpiece.LeftMode.class) {
      tmp1 = lastpiece.reduceDoc(doc2);
      return lastpiece.easyDisplay(lastpiece.nlText, lastpiece.first, txt1, rest, tmp1)
    } else {
      tmp2 = lineLen / ribbons;
      tmp3 = lastpiece.ceiling(tmp2);
      ribbonLen = tmp3;
      if (m3 instanceof lastpiece.ZigZagMode.class) {
        tmp4 = 2147483647;
      } else {
        tmp4 = lineLen;
      }
      bestLineLen = tmp4;
      tmp5 = lastpiece.reduceDoc(doc2);
      tmp6 = lastpiece.best(bestLineLen, ribbonLen, tmp5);
      doc11 = tmp6;
      return lastpiece.displayDoc(m3, lineLen, ribbonLen, txt1, rest, doc11)
    }
  } 
  static easyDisplay(nlSpaceText, choose, txt2, end, x7) {
    let lay;
    lay = function lay(x8) {
      let param0, param1, param2, param01, param11, param21, param02, param12, s3, p11, param03, p12, param04, param13, p13, param05, param14, p14, q6, tmp, tmp1, tmp2;
      if (x8 instanceof lastpiece.NoDoc.class) {
        throw globalThis.Error("easyDisplay: NoDoc");
      } else if (x8 instanceof lastpiece.Union.class) {
        param05 = x8.d1;
        param14 = x8.d2;
        p14 = param05;
        q6 = param14;
        tmp = runtime.safeCall(choose(p14, q6));
        return lay(tmp)
      } else if (x8 instanceof lastpiece.Nest.class) {
        param04 = x8.i;
        param13 = x8.d;
        p13 = param13;
        return lay(p13)
      } else if (x8 instanceof lastpiece.Empty.class) {
        return end
      } else if (x8 instanceof lastpiece.NilAbove.class) {
        param03 = x8.d;
        p12 = param03;
        tmp1 = lay(p12);
        return runtime.safeCall(txt2(nlSpaceText, tmp1))
      } else if (x8 instanceof lastpiece.TextBeside.class) {
        param02 = x8.a;
        param12 = x8.d;
        s3 = param02;
        p11 = param12;
        tmp2 = lay(p11);
        return runtime.safeCall(txt2(s3, tmp2))
      } else if (x8 instanceof lastpiece.Above.class) {
        param01 = x8.d1;
        param11 = x8.b;
        param21 = x8.d2;
        throw globalThis.Error("easyDisplay Above");
      } else if (x8 instanceof lastpiece.Beside.class) {
        param0 = x8.d1;
        param1 = x8.b;
        param2 = x8.d2;
        throw globalThis.Error("easyDisplay Beside");
      } else {
        throw new globalThis.Error("match error");
      }
    };
    return lay(x7)
  } 
  static displayDoc(m4, pageWidth, ribbonWidth, txt3, end1, doc3) {
    let lay, gapWidth, shift, tmp, tmp1;
    lay = function lay(k9, docc) {
      let lay2, lay1, param0, param1, s3, p11, scrut, scrut1, param01, p12, param02, param11, k15, p13, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17;
      lay2 = function lay2(k10, param) {
        let param03, param12, p14, param04, param13, s4, p15, param05, p16, tmp18, tmp19, tmp20, tmp21;
        if (param instanceof lastpiece.NilAbove.class) {
          param05 = param.d;
          p16 = param05;
          tmp18 = lay(k10, p16);
          return runtime.safeCall(txt3(lastpiece.nlText, tmp18))
        } else if (param instanceof lastpiece.TextBeside.class) {
          param04 = param.a;
          param13 = param.d;
          s4 = param04;
          p15 = param13;
          tmp19 = lastpiece.annotSize(s4);
          tmp20 = k10 + tmp19;
          tmp21 = lay2(tmp20, p15);
          return runtime.safeCall(txt3(s4, tmp21))
        } else if (param instanceof lastpiece.Nest.class) {
          param03 = param.i;
          param12 = param.d;
          p14 = param12;
          return lay2(k10, p14)
        } else if (param instanceof lastpiece.Empty.class) {
          return end1
        } else {
          throw new globalThis.Error("match error");
        }
      };
      lay1 = function lay1(k10, s4, p14) {
        let r7, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24;
        tmp18 = lastpiece.annotSize(s4);
        tmp19 = k10 + tmp18;
        r7 = tmp19;
        tmp20 = lastpiece.indent(k10);
        tmp21 = lastpiece.Str(tmp20);
        tmp22 = lastpiece.NoAnnot(tmp21, k10);
        tmp23 = lay2(r7, p14);
        tmp24 = runtime.safeCall(txt3(s4, tmp23));
        return runtime.safeCall(txt3(tmp22, tmp24))
      };
      if (docc instanceof lastpiece.Nest.class) {
        param02 = docc.i;
        param11 = docc.d;
        k15 = param02;
        p13 = param11;
        tmp2 = k9 + k15;
        return lay(tmp2, p13)
      } else if (docc instanceof lastpiece.Empty.class) {
        return end1
      } else if (docc instanceof lastpiece.NilAbove.class) {
        param01 = docc.d;
        p12 = param01;
        tmp3 = lay(k9, p12);
        return runtime.safeCall(txt3(lastpiece.nlText, tmp3))
      } else if (docc instanceof lastpiece.TextBeside.class) {
        param0 = docc.a;
        param1 = docc.d;
        s3 = param0;
        p11 = param1;
        if (m4 instanceof lastpiece.ZigZagMode.class) {
          scrut1 = k9 >= gapWidth;
          if (scrut1 === true) {
            tmp4 = NofibPrelude.replicate(shift, "/");
            tmp5 = lastpiece.Str(tmp4);
            tmp6 = lastpiece.NoAnnot(tmp5, shift);
            tmp7 = k9 - shift;
            tmp8 = lay1(tmp7, s3, p11);
            tmp9 = runtime.safeCall(txt3(lastpiece.nlText, tmp8));
            tmp10 = runtime.safeCall(txt3(tmp6, tmp9));
            return runtime.safeCall(txt3(lastpiece.nlText, tmp10))
          } else {
            scrut = k9 < 0;
            if (scrut === true) {
              tmp11 = NofibPrelude.replicate(shift, "|");
              tmp12 = lastpiece.Str(tmp11);
              tmp13 = lastpiece.NoAnnot(tmp12, shift);
              tmp14 = k9 + shift;
              tmp15 = lay1(tmp14, s3, p11);
              tmp16 = runtime.safeCall(txt3(lastpiece.nlText, tmp15));
              tmp17 = runtime.safeCall(txt3(tmp13, tmp16));
              return runtime.safeCall(txt3(lastpiece.nlText, tmp17))
            } else {
              return lay1(k9, s3, p11)
            }
          }
        } else {
          return lay1(k9, s3, p11)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = pageWidth - ribbonWidth;
    gapWidth = tmp;
    tmp1 = NofibPrelude.intDiv(gapWidth, 2);
    shift = tmp1;
    return lay(0, doc3)
  } 
  static best(w0, r7, doc4) {
    let get, get1;
    get = function get(r8, w, docc) {
      let param0, param1, param2, param01, param11, param21, param02, param12, p11, q6, param03, param13, k9, p12, param04, param14, s3, p13, param05, p14, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
      if (docc instanceof lastpiece.Empty.class) {
        return lastpiece.Empty
      } else if (docc instanceof lastpiece.NoDoc.class) {
        return lastpiece.NoDoc
      } else if (docc instanceof lastpiece.NilAbove.class) {
        param05 = docc.d;
        p14 = param05;
        tmp = get(r8, w, p14);
        return lastpiece.NilAbove(tmp)
      } else if (docc instanceof lastpiece.TextBeside.class) {
        param04 = docc.a;
        param14 = docc.d;
        s3 = param04;
        p13 = param14;
        tmp1 = lastpiece.annotSize(s3);
        tmp2 = get1(r8, w, tmp1, p13);
        return lastpiece.TextBeside(s3, tmp2)
      } else if (docc instanceof lastpiece.Nest.class) {
        param03 = docc.i;
        param13 = docc.d;
        k9 = param03;
        p12 = param13;
        tmp3 = w - k9;
        tmp4 = get(r8, tmp3, p12);
        return lastpiece.Nest(k9, tmp4)
      } else if (docc instanceof lastpiece.Union.class) {
        param02 = docc.d1;
        param12 = docc.d2;
        p11 = param02;
        q6 = param12;
        tmp5 = get(r8, w, p11);
        tmp6 = get(r8, w, q6);
        return lastpiece.nicest(w, r8, tmp5, tmp6)
      } else if (docc instanceof lastpiece.Above.class) {
        param01 = docc.d1;
        param11 = docc.b;
        param21 = docc.d2;
        throw globalThis.Error("best get Above");
      } else if (docc instanceof lastpiece.Beside.class) {
        param0 = docc.d1;
        param1 = docc.b;
        param2 = docc.d2;
        throw globalThis.Error("best get Beside");
      } else {
        throw new globalThis.Error("match error");
      }
    };
    get1 = function get1(r8, w, sl, p11) {
      let param0, param1, param2, param01, param11, param21, param02, param12, p12, q6, param03, param13, p13, param04, param14, s3, p14, param05, p15, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
      if (p11 instanceof lastpiece.Empty.class) {
        return lastpiece.Empty
      } else if (p11 instanceof lastpiece.NoDoc.class) {
        return lastpiece.NoDoc
      } else if (p11 instanceof lastpiece.NilAbove.class) {
        param05 = p11.d;
        p15 = param05;
        tmp = w - sl;
        tmp1 = get(r8, tmp, p15);
        return lastpiece.NilAbove(tmp1)
      } else if (p11 instanceof lastpiece.TextBeside.class) {
        param04 = p11.a;
        param14 = p11.d;
        s3 = param04;
        p14 = param14;
        tmp2 = lastpiece.annotSize(s3);
        tmp3 = sl + tmp2;
        tmp4 = get1(r8, w, tmp3, p14);
        return lastpiece.TextBeside(s3, tmp4)
      } else if (p11 instanceof lastpiece.Nest.class) {
        param03 = p11.i;
        param13 = p11.d;
        p13 = param13;
        return get1(r8, w, sl, p13)
      } else if (p11 instanceof lastpiece.Union.class) {
        param02 = p11.d1;
        param12 = p11.d2;
        p12 = param02;
        q6 = param12;
        tmp5 = get1(r8, w, sl, p12);
        tmp6 = get1(r8, w, sl, q6);
        return lastpiece.nicest1(w, r8, sl, tmp5, tmp6)
      } else if (p11 instanceof lastpiece.Above.class) {
        param01 = p11.d1;
        param11 = p11.b;
        param21 = p11.d2;
        throw globalThis.Error("best get1 Above");
      } else if (p11 instanceof lastpiece.Beside.class) {
        param0 = p11.d1;
        param1 = p11.b;
        param2 = p11.d2;
        throw globalThis.Error("best get1 Beside");
      } else {
        throw new globalThis.Error("match error");
      }
    };
    return get(r7, w0, doc4)
  } 
  static nonEmptySet(doc5) {
    let param0, param1, param2, param01, param11, param21, param02, param12, p11, param03, param13, p12, param04, param05, param14;
    if (doc5 instanceof lastpiece.NoDoc.class) {
      return false
    } else if (doc5 instanceof lastpiece.Union.class) {
      param05 = doc5.d1;
      param14 = doc5.d2;
      return true
    } else if (doc5 instanceof lastpiece.Empty.class) {
      return true
    } else if (doc5 instanceof lastpiece.NilAbove.class) {
      param04 = doc5.d;
      return true
    } else if (doc5 instanceof lastpiece.TextBeside.class) {
      param03 = doc5.a;
      param13 = doc5.d;
      p12 = param13;
      return lastpiece.nonEmptySet(p12)
    } else if (doc5 instanceof lastpiece.Nest.class) {
      param02 = doc5.i;
      param12 = doc5.d;
      p11 = param12;
      return lastpiece.nonEmptySet(p11)
    } else if (doc5 instanceof lastpiece.Above.class) {
      param01 = doc5.d1;
      param11 = doc5.b;
      param21 = doc5.d2;
      throw globalThis.Error("nonEmptySet Above");
    } else if (doc5 instanceof lastpiece.Beside.class) {
      param0 = doc5.d1;
      param1 = doc5.b;
      param2 = doc5.d2;
      throw globalThis.Error("nonEmptySet Beside");
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static fits(n1, param) {
    let param0, param1, param01, param11, param02, param12, param2, param03, param13, param21, param04, param14, s3, p11, param05, scrut, tmp, tmp1;
    scrut = n1 < 0;
    if (scrut === true) {
      return false
    } else {
      if (param instanceof lastpiece.NoDoc.class) {
        return false
      } else if (param instanceof lastpiece.Empty.class) {
        return true
      } else if (param instanceof lastpiece.NilAbove.class) {
        param05 = param.d;
        return true
      } else if (param instanceof lastpiece.TextBeside.class) {
        param04 = param.a;
        param14 = param.d;
        s3 = param04;
        p11 = param14;
        tmp = lastpiece.annotSize(s3);
        tmp1 = n1 - tmp;
        return lastpiece.fits(tmp1, p11)
      } else if (param instanceof lastpiece.Above.class) {
        param03 = param.d1;
        param13 = param.b;
        param21 = param.d2;
        throw globalThis.Error("fits Above");
      } else if (param instanceof lastpiece.Beside.class) {
        param02 = param.d1;
        param12 = param.b;
        param2 = param.d2;
        throw globalThis.Error("fits Beside");
      } else if (param instanceof lastpiece.Union.class) {
        param01 = param.d1;
        param11 = param.d2;
        throw globalThis.Error("fits Union");
      } else if (param instanceof lastpiece.Nest.class) {
        param0 = param.i;
        param1 = param.d;
        throw globalThis.Error("fits Nest");
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  static first(p11, q6) {
    let scrut;
    scrut = lastpiece.nonEmptySet(p11);
    if (scrut === true) {
      return p11
    } else {
      return q6
    }
  } 
  static nicest1(w, r8, sl, p12, q7) {
    let scrut, tmp, tmp1;
    tmp = NofibPrelude.min(w, r8);
    tmp1 = tmp - sl;
    scrut = lastpiece.fits(tmp1, p12);
    if (scrut === true) {
      return p12
    } else {
      return q7
    }
  } 
  static nicest(w1, r9, p13, q8) {
    return lastpiece.nicest1(w1, r9, 0, p13, q8)
  } 
  static testLastPiece_nofib() {
    let initialBoard, solutions, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = NofibPrelude.Cons([
      1,
      1
    ], NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons([
      1,
      0
    ], tmp);
    tmp2 = lastpiece.fit(lastpiece.emptyBoard, [
      1,
      1
    ], "a", tmp1);
    tmp3 = NofibPrelude.fromSome(tmp2);
    initialBoard = tmp3;
    tmp4 = lastpiece.search([
      1,
      2
    ], lastpiece.Female, initialBoard, lastpiece.initialPieces);
    solutions = tmp4;
    tmp5 = lastpiece.display(solutions);
    return lastpiece.printDoc(tmp5)
  }
  static toString() { return "lastpiece"; }
};