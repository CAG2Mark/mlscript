import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let lscomp, banner1, lambda, lambda1, lscomp$;
lscomp$ = function lscomp$(c, ls) {
  let param0, param1, h, t, first1, first0, c_, letter, scrut, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    if (globalThis.Array.isArray(h) && h.length === 2) {
      first0 = h[0];
      first1 = h[1];
      c_ = first0;
      letter = first1;
      scrut = c_ === c;
      if (scrut === true) {
        tmp = lscomp$(c, t);
        return NofibPrelude.Cons(letter, tmp)
      } else {
        return lscomp$(c, t)
      }
    } else {
      return lscomp$(c, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp = function lscomp(c) {
  return (ls) => {
    return lscomp$(c, ls)
  }
};
lambda1 = (undefined, function (xs, ys) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.Cons(" ", NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(" ", tmp);
  tmp2 = NofibPrelude.append(tmp1, ys);
  return NofibPrelude.append(xs, tmp2)
});
lambda = (undefined, function (x) {
  let tmp;
  tmp = NofibPrelude.Cons("\n", NofibPrelude.Nil);
  return NofibPrelude.append(x, tmp)
});
banner1 = class banner {
  static {
    banner1 = banner;
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75, tmp76, tmp77, tmp78, tmp79, tmp80, tmp81, tmp82, tmp83, tmp84, tmp85, tmp86, tmp87, tmp88, tmp89, tmp90, tmp91, tmp92, tmp93, tmp94, tmp95, tmp96, tmp97, tmp98, tmp99, tmp100, tmp101, tmp102, tmp103, tmp104, tmp105, tmp106, tmp107, tmp108, tmp109, tmp110, tmp111, tmp112, tmp113, tmp114, tmp115, tmp116, tmp117, tmp118, tmp119, tmp120, tmp121, tmp122, tmp123, tmp124, tmp125, tmp126, tmp127, tmp128, tmp129, tmp130, tmp131, tmp132, tmp133, tmp134, tmp135, tmp136, tmp137, tmp138, tmp139, tmp140, tmp141, tmp142, tmp143, tmp144, tmp145, tmp146, tmp147, tmp148, tmp149, tmp150, tmp151, tmp152, tmp153, tmp154, tmp155, tmp156, tmp157, tmp158, tmp159, tmp160, tmp161, tmp162, tmp163, tmp164, tmp165, tmp166, tmp167, tmp168, tmp169, tmp170, tmp171, tmp172, tmp173, tmp174, tmp175, tmp176, tmp177, tmp178, tmp179, tmp180, tmp181, tmp182, tmp183, tmp184, tmp185, tmp186, tmp187, tmp188, tmp189, tmp190, tmp191, tmp192, tmp193, tmp194, tmp195, tmp196, tmp197, tmp198, tmp199, tmp200, tmp201, tmp202, tmp203, tmp204, tmp205, tmp206, tmp207, tmp208, tmp209, tmp210, tmp211, tmp212, tmp213, tmp214, tmp215, tmp216, tmp217, tmp218, tmp219, tmp220, tmp221, tmp222, tmp223, tmp224, tmp225, tmp226, tmp227, tmp228, tmp229, tmp230, tmp231, tmp232, tmp233, tmp234, tmp235, tmp236, tmp237, tmp238, tmp239, tmp240, tmp241, tmp242, tmp243, tmp244, tmp245, tmp246, tmp247, tmp248, tmp249, tmp250, tmp251, tmp252, tmp253, tmp254, tmp255, tmp256, tmp257, tmp258, tmp259, tmp260, tmp261, tmp262, tmp263, tmp264, tmp265, tmp266, tmp267, tmp268, tmp269, tmp270, tmp271, tmp272, tmp273, tmp274, tmp275, tmp276, tmp277, tmp278, tmp279, tmp280, tmp281, tmp282, tmp283, tmp284, tmp285, tmp286, tmp287, tmp288, tmp289, tmp290, tmp291, tmp292, tmp293, tmp294, tmp295, tmp296, tmp297, tmp298, tmp299, tmp300, tmp301, tmp302, tmp303, tmp304, tmp305, tmp306, tmp307, tmp308, tmp309, tmp310, tmp311, tmp312, tmp313, tmp314, tmp315, tmp316, tmp317, tmp318, tmp319, tmp320, tmp321, tmp322, tmp323, tmp324, tmp325, tmp326, tmp327, tmp328, tmp329, tmp330, tmp331, tmp332, tmp333, tmp334, tmp335, tmp336, tmp337, tmp338, tmp339, tmp340, tmp341, tmp342, tmp343, tmp344, tmp345, tmp346, tmp347, tmp348, tmp349, tmp350, tmp351, tmp352, tmp353, tmp354, tmp355, tmp356, tmp357, tmp358, tmp359, tmp360, tmp361, tmp362, tmp363, tmp364, tmp365, tmp366, tmp367, tmp368, tmp369, tmp370, tmp371, tmp372, tmp373, tmp374, tmp375, tmp376, tmp377, tmp378, tmp379, tmp380, tmp381, tmp382, tmp383, tmp384, tmp385, tmp386, tmp387, tmp388, tmp389, tmp390, tmp391, tmp392, tmp393, tmp394, tmp395, tmp396, tmp397, tmp398, tmp399, tmp400, tmp401, tmp402, tmp403, tmp404, tmp405, tmp406, tmp407, tmp408, tmp409, tmp410, tmp411, tmp412, tmp413, tmp414, tmp415, tmp416, tmp417, tmp418, tmp419, tmp420, tmp421, tmp422, tmp423, tmp424, tmp425, tmp426, tmp427, tmp428, tmp429, tmp430, tmp431, tmp432, tmp433, tmp434, tmp435, tmp436, tmp437, tmp438, tmp439, tmp440, tmp441, tmp442, tmp443, tmp444, tmp445, tmp446, tmp447, tmp448, tmp449, tmp450, tmp451, tmp452, tmp453, tmp454, tmp455, tmp456, tmp457, tmp458, tmp459, tmp460, tmp461, tmp462, tmp463, tmp464, tmp465, tmp466, tmp467, tmp468, tmp469, tmp470, tmp471, tmp472, tmp473, tmp474, tmp475, tmp476, tmp477, tmp478, tmp479, tmp480, tmp481, tmp482, tmp483, tmp484, tmp485, tmp486, tmp487, tmp488, tmp489, tmp490, tmp491, tmp492, lambda2;
    tmp = NofibPrelude.nofibStringToList("     ");
    tmp1 = NofibPrelude.nofibStringToList("     ");
    tmp2 = NofibPrelude.nofibStringToList("     ");
    tmp3 = NofibPrelude.nofibStringToList("     ");
    tmp4 = NofibPrelude.nofibStringToList("     ");
    tmp5 = NofibPrelude.Cons(tmp4, NofibPrelude.Nil);
    tmp6 = NofibPrelude.Cons(tmp3, tmp5);
    tmp7 = NofibPrelude.Cons(tmp2, tmp6);
    tmp8 = NofibPrelude.Cons(tmp1, tmp7);
    tmp9 = NofibPrelude.Cons(tmp, tmp8);
    this.blank = tmp9;
    tmp10 = NofibPrelude.nofibStringToList("  A  ");
    tmp11 = NofibPrelude.nofibStringToList(" A A ");
    tmp12 = NofibPrelude.nofibStringToList("AAAAA");
    tmp13 = NofibPrelude.nofibStringToList("A   A");
    tmp14 = NofibPrelude.nofibStringToList("A   A");
    tmp15 = NofibPrelude.Cons(tmp14, NofibPrelude.Nil);
    tmp16 = NofibPrelude.Cons(tmp13, tmp15);
    tmp17 = NofibPrelude.Cons(tmp12, tmp16);
    tmp18 = NofibPrelude.Cons(tmp11, tmp17);
    tmp19 = NofibPrelude.Cons(tmp10, tmp18);
    tmp20 = NofibPrelude.nofibStringToList("BBBB ");
    tmp21 = NofibPrelude.nofibStringToList("B   B");
    tmp22 = NofibPrelude.nofibStringToList("BBBB ");
    tmp23 = NofibPrelude.nofibStringToList("B   B");
    tmp24 = NofibPrelude.nofibStringToList("BBBB ");
    tmp25 = NofibPrelude.Cons(tmp24, NofibPrelude.Nil);
    tmp26 = NofibPrelude.Cons(tmp23, tmp25);
    tmp27 = NofibPrelude.Cons(tmp22, tmp26);
    tmp28 = NofibPrelude.Cons(tmp21, tmp27);
    tmp29 = NofibPrelude.Cons(tmp20, tmp28);
    tmp30 = NofibPrelude.nofibStringToList(" CCCC");
    tmp31 = NofibPrelude.nofibStringToList("C    ");
    tmp32 = NofibPrelude.nofibStringToList("C    ");
    tmp33 = NofibPrelude.nofibStringToList("C    ");
    tmp34 = NofibPrelude.nofibStringToList(" CCCC");
    tmp35 = NofibPrelude.Cons(tmp34, NofibPrelude.Nil);
    tmp36 = NofibPrelude.Cons(tmp33, tmp35);
    tmp37 = NofibPrelude.Cons(tmp32, tmp36);
    tmp38 = NofibPrelude.Cons(tmp31, tmp37);
    tmp39 = NofibPrelude.Cons(tmp30, tmp38);
    tmp40 = NofibPrelude.nofibStringToList("DDDD ");
    tmp41 = NofibPrelude.nofibStringToList("D   D");
    tmp42 = NofibPrelude.nofibStringToList("D   D");
    tmp43 = NofibPrelude.nofibStringToList("D   D");
    tmp44 = NofibPrelude.nofibStringToList("DDDD ");
    tmp45 = NofibPrelude.Cons(tmp44, NofibPrelude.Nil);
    tmp46 = NofibPrelude.Cons(tmp43, tmp45);
    tmp47 = NofibPrelude.Cons(tmp42, tmp46);
    tmp48 = NofibPrelude.Cons(tmp41, tmp47);
    tmp49 = NofibPrelude.Cons(tmp40, tmp48);
    tmp50 = NofibPrelude.nofibStringToList("EEEEE");
    tmp51 = NofibPrelude.nofibStringToList("E    ");
    tmp52 = NofibPrelude.nofibStringToList("EEEEE");
    tmp53 = NofibPrelude.nofibStringToList("E    ");
    tmp54 = NofibPrelude.nofibStringToList("EEEEE");
    tmp55 = NofibPrelude.Cons(tmp54, NofibPrelude.Nil);
    tmp56 = NofibPrelude.Cons(tmp53, tmp55);
    tmp57 = NofibPrelude.Cons(tmp52, tmp56);
    tmp58 = NofibPrelude.Cons(tmp51, tmp57);
    tmp59 = NofibPrelude.Cons(tmp50, tmp58);
    tmp60 = NofibPrelude.nofibStringToList("FFFFF");
    tmp61 = NofibPrelude.nofibStringToList("F    ");
    tmp62 = NofibPrelude.nofibStringToList("FFFF ");
    tmp63 = NofibPrelude.nofibStringToList("F    ");
    tmp64 = NofibPrelude.nofibStringToList("F    ");
    tmp65 = NofibPrelude.Cons(tmp64, NofibPrelude.Nil);
    tmp66 = NofibPrelude.Cons(tmp63, tmp65);
    tmp67 = NofibPrelude.Cons(tmp62, tmp66);
    tmp68 = NofibPrelude.Cons(tmp61, tmp67);
    tmp69 = NofibPrelude.Cons(tmp60, tmp68);
    tmp70 = NofibPrelude.nofibStringToList(" GGGG");
    tmp71 = NofibPrelude.nofibStringToList("G    ");
    tmp72 = NofibPrelude.nofibStringToList("G  GG");
    tmp73 = NofibPrelude.nofibStringToList("G   G");
    tmp74 = NofibPrelude.nofibStringToList(" GGG ");
    tmp75 = NofibPrelude.Cons(tmp74, NofibPrelude.Nil);
    tmp76 = NofibPrelude.Cons(tmp73, tmp75);
    tmp77 = NofibPrelude.Cons(tmp72, tmp76);
    tmp78 = NofibPrelude.Cons(tmp71, tmp77);
    tmp79 = NofibPrelude.Cons(tmp70, tmp78);
    tmp80 = NofibPrelude.nofibStringToList("H   H");
    tmp81 = NofibPrelude.nofibStringToList("H   H");
    tmp82 = NofibPrelude.nofibStringToList("HHHHH");
    tmp83 = NofibPrelude.nofibStringToList("H   H");
    tmp84 = NofibPrelude.nofibStringToList("H   H");
    tmp85 = NofibPrelude.Cons(tmp84, NofibPrelude.Nil);
    tmp86 = NofibPrelude.Cons(tmp83, tmp85);
    tmp87 = NofibPrelude.Cons(tmp82, tmp86);
    tmp88 = NofibPrelude.Cons(tmp81, tmp87);
    tmp89 = NofibPrelude.Cons(tmp80, tmp88);
    tmp90 = NofibPrelude.nofibStringToList("IIIII");
    tmp91 = NofibPrelude.nofibStringToList("  I  ");
    tmp92 = NofibPrelude.nofibStringToList("  I  ");
    tmp93 = NofibPrelude.nofibStringToList("  I  ");
    tmp94 = NofibPrelude.nofibStringToList("IIIII");
    tmp95 = NofibPrelude.Cons(tmp94, NofibPrelude.Nil);
    tmp96 = NofibPrelude.Cons(tmp93, tmp95);
    tmp97 = NofibPrelude.Cons(tmp92, tmp96);
    tmp98 = NofibPrelude.Cons(tmp91, tmp97);
    tmp99 = NofibPrelude.Cons(tmp90, tmp98);
    tmp100 = NofibPrelude.nofibStringToList("JJJJJ");
    tmp101 = NofibPrelude.nofibStringToList("   J ");
    tmp102 = NofibPrelude.nofibStringToList("   J ");
    tmp103 = NofibPrelude.nofibStringToList("J  J ");
    tmp104 = NofibPrelude.nofibStringToList(" JJ  ");
    tmp105 = NofibPrelude.Cons(tmp104, NofibPrelude.Nil);
    tmp106 = NofibPrelude.Cons(tmp103, tmp105);
    tmp107 = NofibPrelude.Cons(tmp102, tmp106);
    tmp108 = NofibPrelude.Cons(tmp101, tmp107);
    tmp109 = NofibPrelude.Cons(tmp100, tmp108);
    tmp110 = NofibPrelude.nofibStringToList("K   K");
    tmp111 = NofibPrelude.nofibStringToList("K  K ");
    tmp112 = NofibPrelude.nofibStringToList("KKK  ");
    tmp113 = NofibPrelude.nofibStringToList("K  K ");
    tmp114 = NofibPrelude.nofibStringToList("K   K");
    tmp115 = NofibPrelude.Cons(tmp114, NofibPrelude.Nil);
    tmp116 = NofibPrelude.Cons(tmp113, tmp115);
    tmp117 = NofibPrelude.Cons(tmp112, tmp116);
    tmp118 = NofibPrelude.Cons(tmp111, tmp117);
    tmp119 = NofibPrelude.Cons(tmp110, tmp118);
    tmp120 = NofibPrelude.nofibStringToList("L    ");
    tmp121 = NofibPrelude.nofibStringToList("L    ");
    tmp122 = NofibPrelude.nofibStringToList("L    ");
    tmp123 = NofibPrelude.nofibStringToList("L    ");
    tmp124 = NofibPrelude.nofibStringToList("LLLLL");
    tmp125 = NofibPrelude.Cons(tmp124, NofibPrelude.Nil);
    tmp126 = NofibPrelude.Cons(tmp123, tmp125);
    tmp127 = NofibPrelude.Cons(tmp122, tmp126);
    tmp128 = NofibPrelude.Cons(tmp121, tmp127);
    tmp129 = NofibPrelude.Cons(tmp120, tmp128);
    tmp130 = NofibPrelude.nofibStringToList("M   M");
    tmp131 = NofibPrelude.nofibStringToList("MM MM");
    tmp132 = NofibPrelude.nofibStringToList("M M M");
    tmp133 = NofibPrelude.nofibStringToList("M   M");
    tmp134 = NofibPrelude.nofibStringToList("M   M");
    tmp135 = NofibPrelude.Cons(tmp134, NofibPrelude.Nil);
    tmp136 = NofibPrelude.Cons(tmp133, tmp135);
    tmp137 = NofibPrelude.Cons(tmp132, tmp136);
    tmp138 = NofibPrelude.Cons(tmp131, tmp137);
    tmp139 = NofibPrelude.Cons(tmp130, tmp138);
    tmp140 = NofibPrelude.nofibStringToList("N   N");
    tmp141 = NofibPrelude.nofibStringToList("NN  N");
    tmp142 = NofibPrelude.nofibStringToList("N N N");
    tmp143 = NofibPrelude.nofibStringToList("N  NN");
    tmp144 = NofibPrelude.nofibStringToList("N   N");
    tmp145 = NofibPrelude.Cons(tmp144, NofibPrelude.Nil);
    tmp146 = NofibPrelude.Cons(tmp143, tmp145);
    tmp147 = NofibPrelude.Cons(tmp142, tmp146);
    tmp148 = NofibPrelude.Cons(tmp141, tmp147);
    tmp149 = NofibPrelude.Cons(tmp140, tmp148);
    tmp150 = NofibPrelude.nofibStringToList(" OOO ");
    tmp151 = NofibPrelude.nofibStringToList("O   O");
    tmp152 = NofibPrelude.nofibStringToList("O   O");
    tmp153 = NofibPrelude.nofibStringToList("O   O");
    tmp154 = NofibPrelude.nofibStringToList(" OOO ");
    tmp155 = NofibPrelude.Cons(tmp154, NofibPrelude.Nil);
    tmp156 = NofibPrelude.Cons(tmp153, tmp155);
    tmp157 = NofibPrelude.Cons(tmp152, tmp156);
    tmp158 = NofibPrelude.Cons(tmp151, tmp157);
    tmp159 = NofibPrelude.Cons(tmp150, tmp158);
    tmp160 = NofibPrelude.nofibStringToList("PPPP ");
    tmp161 = NofibPrelude.nofibStringToList("P   P");
    tmp162 = NofibPrelude.nofibStringToList("PPPP ");
    tmp163 = NofibPrelude.nofibStringToList("P    ");
    tmp164 = NofibPrelude.nofibStringToList("P    ");
    tmp165 = NofibPrelude.Cons(tmp164, NofibPrelude.Nil);
    tmp166 = NofibPrelude.Cons(tmp163, tmp165);
    tmp167 = NofibPrelude.Cons(tmp162, tmp166);
    tmp168 = NofibPrelude.Cons(tmp161, tmp167);
    tmp169 = NofibPrelude.Cons(tmp160, tmp168);
    tmp170 = NofibPrelude.nofibStringToList(" QQQ ");
    tmp171 = NofibPrelude.nofibStringToList("Q   Q");
    tmp172 = NofibPrelude.nofibStringToList("Q Q Q");
    tmp173 = NofibPrelude.nofibStringToList("Q  Q ");
    tmp174 = NofibPrelude.nofibStringToList(" QQ Q");
    tmp175 = NofibPrelude.Cons(tmp174, NofibPrelude.Nil);
    tmp176 = NofibPrelude.Cons(tmp173, tmp175);
    tmp177 = NofibPrelude.Cons(tmp172, tmp176);
    tmp178 = NofibPrelude.Cons(tmp171, tmp177);
    tmp179 = NofibPrelude.Cons(tmp170, tmp178);
    tmp180 = NofibPrelude.nofibStringToList("RRRR ");
    tmp181 = NofibPrelude.nofibStringToList("R   R");
    tmp182 = NofibPrelude.nofibStringToList("RRRR ");
    tmp183 = NofibPrelude.nofibStringToList("R  R ");
    tmp184 = NofibPrelude.nofibStringToList("R   R");
    tmp185 = NofibPrelude.Cons(tmp184, NofibPrelude.Nil);
    tmp186 = NofibPrelude.Cons(tmp183, tmp185);
    tmp187 = NofibPrelude.Cons(tmp182, tmp186);
    tmp188 = NofibPrelude.Cons(tmp181, tmp187);
    tmp189 = NofibPrelude.Cons(tmp180, tmp188);
    tmp190 = NofibPrelude.nofibStringToList(" SSSS");
    tmp191 = NofibPrelude.nofibStringToList("S    ");
    tmp192 = NofibPrelude.nofibStringToList(" SSS ");
    tmp193 = NofibPrelude.nofibStringToList("    S");
    tmp194 = NofibPrelude.nofibStringToList("SSSS ");
    tmp195 = NofibPrelude.Cons(tmp194, NofibPrelude.Nil);
    tmp196 = NofibPrelude.Cons(tmp193, tmp195);
    tmp197 = NofibPrelude.Cons(tmp192, tmp196);
    tmp198 = NofibPrelude.Cons(tmp191, tmp197);
    tmp199 = NofibPrelude.Cons(tmp190, tmp198);
    tmp200 = NofibPrelude.nofibStringToList("TTTTT");
    tmp201 = NofibPrelude.nofibStringToList("  T  ");
    tmp202 = NofibPrelude.nofibStringToList("  T  ");
    tmp203 = NofibPrelude.nofibStringToList("  T  ");
    tmp204 = NofibPrelude.nofibStringToList("  T  ");
    tmp205 = NofibPrelude.Cons(tmp204, NofibPrelude.Nil);
    tmp206 = NofibPrelude.Cons(tmp203, tmp205);
    tmp207 = NofibPrelude.Cons(tmp202, tmp206);
    tmp208 = NofibPrelude.Cons(tmp201, tmp207);
    tmp209 = NofibPrelude.Cons(tmp200, tmp208);
    tmp210 = NofibPrelude.nofibStringToList("U   U");
    tmp211 = NofibPrelude.nofibStringToList("U   U");
    tmp212 = NofibPrelude.nofibStringToList("U   U");
    tmp213 = NofibPrelude.nofibStringToList("U   U");
    tmp214 = NofibPrelude.nofibStringToList(" UUU ");
    tmp215 = NofibPrelude.Cons(tmp214, NofibPrelude.Nil);
    tmp216 = NofibPrelude.Cons(tmp213, tmp215);
    tmp217 = NofibPrelude.Cons(tmp212, tmp216);
    tmp218 = NofibPrelude.Cons(tmp211, tmp217);
    tmp219 = NofibPrelude.Cons(tmp210, tmp218);
    tmp220 = NofibPrelude.nofibStringToList("V   V");
    tmp221 = NofibPrelude.nofibStringToList("V   V");
    tmp222 = NofibPrelude.nofibStringToList("V   V");
    tmp223 = NofibPrelude.nofibStringToList(" V V ");
    tmp224 = NofibPrelude.nofibStringToList("  V  ");
    tmp225 = NofibPrelude.Cons(tmp224, NofibPrelude.Nil);
    tmp226 = NofibPrelude.Cons(tmp223, tmp225);
    tmp227 = NofibPrelude.Cons(tmp222, tmp226);
    tmp228 = NofibPrelude.Cons(tmp221, tmp227);
    tmp229 = NofibPrelude.Cons(tmp220, tmp228);
    tmp230 = NofibPrelude.nofibStringToList("W   W");
    tmp231 = NofibPrelude.nofibStringToList("W   W");
    tmp232 = NofibPrelude.nofibStringToList("W   W");
    tmp233 = NofibPrelude.nofibStringToList("W W W");
    tmp234 = NofibPrelude.nofibStringToList(" W W ");
    tmp235 = NofibPrelude.Cons(tmp234, NofibPrelude.Nil);
    tmp236 = NofibPrelude.Cons(tmp233, tmp235);
    tmp237 = NofibPrelude.Cons(tmp232, tmp236);
    tmp238 = NofibPrelude.Cons(tmp231, tmp237);
    tmp239 = NofibPrelude.Cons(tmp230, tmp238);
    tmp240 = NofibPrelude.nofibStringToList("X   X");
    tmp241 = NofibPrelude.nofibStringToList(" X X ");
    tmp242 = NofibPrelude.nofibStringToList("  X  ");
    tmp243 = NofibPrelude.nofibStringToList(" X X ");
    tmp244 = NofibPrelude.nofibStringToList("X   X");
    tmp245 = NofibPrelude.Cons(tmp244, NofibPrelude.Nil);
    tmp246 = NofibPrelude.Cons(tmp243, tmp245);
    tmp247 = NofibPrelude.Cons(tmp242, tmp246);
    tmp248 = NofibPrelude.Cons(tmp241, tmp247);
    tmp249 = NofibPrelude.Cons(tmp240, tmp248);
    tmp250 = NofibPrelude.nofibStringToList("Y   Y");
    tmp251 = NofibPrelude.nofibStringToList(" Y Y ");
    tmp252 = NofibPrelude.nofibStringToList("  Y  ");
    tmp253 = NofibPrelude.nofibStringToList("  Y  ");
    tmp254 = NofibPrelude.nofibStringToList("  Y  ");
    tmp255 = NofibPrelude.Cons(tmp254, NofibPrelude.Nil);
    tmp256 = NofibPrelude.Cons(tmp253, tmp255);
    tmp257 = NofibPrelude.Cons(tmp252, tmp256);
    tmp258 = NofibPrelude.Cons(tmp251, tmp257);
    tmp259 = NofibPrelude.Cons(tmp250, tmp258);
    tmp260 = NofibPrelude.nofibStringToList("ZZZZZ");
    tmp261 = NofibPrelude.nofibStringToList("   Z ");
    tmp262 = NofibPrelude.nofibStringToList("  Z  ");
    tmp263 = NofibPrelude.nofibStringToList(" Z   ");
    tmp264 = NofibPrelude.nofibStringToList("ZZZZZ");
    tmp265 = NofibPrelude.Cons(tmp264, NofibPrelude.Nil);
    tmp266 = NofibPrelude.Cons(tmp263, tmp265);
    tmp267 = NofibPrelude.Cons(tmp262, tmp266);
    tmp268 = NofibPrelude.Cons(tmp261, tmp267);
    tmp269 = NofibPrelude.Cons(tmp260, tmp268);
    tmp270 = NofibPrelude.Cons(tmp269, NofibPrelude.Nil);
    tmp271 = NofibPrelude.Cons(tmp259, tmp270);
    tmp272 = NofibPrelude.Cons(tmp249, tmp271);
    tmp273 = NofibPrelude.Cons(tmp239, tmp272);
    tmp274 = NofibPrelude.Cons(tmp229, tmp273);
    tmp275 = NofibPrelude.Cons(tmp219, tmp274);
    tmp276 = NofibPrelude.Cons(tmp209, tmp275);
    tmp277 = NofibPrelude.Cons(tmp199, tmp276);
    tmp278 = NofibPrelude.Cons(tmp189, tmp277);
    tmp279 = NofibPrelude.Cons(tmp179, tmp278);
    tmp280 = NofibPrelude.Cons(tmp169, tmp279);
    tmp281 = NofibPrelude.Cons(tmp159, tmp280);
    tmp282 = NofibPrelude.Cons(tmp149, tmp281);
    tmp283 = NofibPrelude.Cons(tmp139, tmp282);
    tmp284 = NofibPrelude.Cons(tmp129, tmp283);
    tmp285 = NofibPrelude.Cons(tmp119, tmp284);
    tmp286 = NofibPrelude.Cons(tmp109, tmp285);
    tmp287 = NofibPrelude.Cons(tmp99, tmp286);
    tmp288 = NofibPrelude.Cons(tmp89, tmp287);
    tmp289 = NofibPrelude.Cons(tmp79, tmp288);
    tmp290 = NofibPrelude.Cons(tmp69, tmp289);
    tmp291 = NofibPrelude.Cons(tmp59, tmp290);
    tmp292 = NofibPrelude.Cons(tmp49, tmp291);
    tmp293 = NofibPrelude.Cons(tmp39, tmp292);
    tmp294 = NofibPrelude.Cons(tmp29, tmp293);
    tmp295 = NofibPrelude.Cons(tmp19, tmp294);
    this.alphas = tmp295;
    tmp296 = NofibPrelude.nofibStringToList("    ");
    tmp297 = NofibPrelude.nofibStringToList("   ");
    tmp298 = NofibPrelude.nofibStringToList("  ");
    tmp299 = NofibPrelude.nofibStringToList(" ");
    tmp300 = NofibPrelude.nofibStringToList("");
    tmp301 = NofibPrelude.Cons(tmp300, NofibPrelude.Nil);
    tmp302 = NofibPrelude.Cons(tmp299, tmp301);
    tmp303 = NofibPrelude.Cons(tmp298, tmp302);
    tmp304 = NofibPrelude.Cons(tmp297, tmp303);
    tmp305 = NofibPrelude.Cons(tmp296, tmp304);
    this.slant = tmp305;
    tmp306 = NofibPrelude.nofibStringToList("     ");
    tmp307 = NofibPrelude.nofibStringToList("     ");
    tmp308 = NofibPrelude.nofibStringToList("     ");
    tmp309 = NofibPrelude.nofibStringToList("  .. ");
    tmp310 = NofibPrelude.nofibStringToList("  .. ");
    tmp311 = NofibPrelude.Cons(tmp310, NofibPrelude.Nil);
    tmp312 = NofibPrelude.Cons(tmp309, tmp311);
    tmp313 = NofibPrelude.Cons(tmp308, tmp312);
    tmp314 = NofibPrelude.Cons(tmp307, tmp313);
    tmp315 = NofibPrelude.Cons(tmp306, tmp314);
    tmp316 = NofibPrelude.nofibStringToList(" ??? ");
    tmp317 = NofibPrelude.nofibStringToList("?   ?");
    tmp318 = NofibPrelude.nofibStringToList("   ? ");
    tmp319 = NofibPrelude.nofibStringToList("  ?  ");
    tmp320 = NofibPrelude.nofibStringToList("  .  ");
    tmp321 = NofibPrelude.Cons(tmp320, NofibPrelude.Nil);
    tmp322 = NofibPrelude.Cons(tmp319, tmp321);
    tmp323 = NofibPrelude.Cons(tmp318, tmp322);
    tmp324 = NofibPrelude.Cons(tmp317, tmp323);
    tmp325 = NofibPrelude.Cons(tmp316, tmp324);
    tmp326 = NofibPrelude.nofibStringToList("  !  ");
    tmp327 = NofibPrelude.nofibStringToList("  !  ");
    tmp328 = NofibPrelude.nofibStringToList("  !  ");
    tmp329 = NofibPrelude.nofibStringToList("  !  ");
    tmp330 = NofibPrelude.nofibStringToList("  .  ");
    tmp331 = NofibPrelude.Cons(tmp330, NofibPrelude.Nil);
    tmp332 = NofibPrelude.Cons(tmp329, tmp331);
    tmp333 = NofibPrelude.Cons(tmp328, tmp332);
    tmp334 = NofibPrelude.Cons(tmp327, tmp333);
    tmp335 = NofibPrelude.Cons(tmp326, tmp334);
    tmp336 = NofibPrelude.nofibStringToList("     ");
    tmp337 = NofibPrelude.nofibStringToList("     ");
    tmp338 = NofibPrelude.nofibStringToList("-----");
    tmp339 = NofibPrelude.nofibStringToList("     ");
    tmp340 = NofibPrelude.nofibStringToList("     ");
    tmp341 = NofibPrelude.Cons(tmp340, NofibPrelude.Nil);
    tmp342 = NofibPrelude.Cons(tmp339, tmp341);
    tmp343 = NofibPrelude.Cons(tmp338, tmp342);
    tmp344 = NofibPrelude.Cons(tmp337, tmp343);
    tmp345 = NofibPrelude.Cons(tmp336, tmp344);
    tmp346 = NofibPrelude.nofibStringToList("  +  ");
    tmp347 = NofibPrelude.nofibStringToList("  +  ");
    tmp348 = NofibPrelude.nofibStringToList("+++++");
    tmp349 = NofibPrelude.nofibStringToList("  +  ");
    tmp350 = NofibPrelude.nofibStringToList("  +  ");
    tmp351 = NofibPrelude.Cons(tmp350, NofibPrelude.Nil);
    tmp352 = NofibPrelude.Cons(tmp349, tmp351);
    tmp353 = NofibPrelude.Cons(tmp348, tmp352);
    tmp354 = NofibPrelude.Cons(tmp347, tmp353);
    tmp355 = NofibPrelude.Cons(tmp346, tmp354);
    tmp356 = NofibPrelude.nofibStringToList("     ");
    tmp357 = NofibPrelude.nofibStringToList("  :: ");
    tmp358 = NofibPrelude.nofibStringToList("     ");
    tmp359 = NofibPrelude.nofibStringToList("  :: ");
    tmp360 = NofibPrelude.nofibStringToList("     ");
    tmp361 = NofibPrelude.Cons(tmp360, NofibPrelude.Nil);
    tmp362 = NofibPrelude.Cons(tmp359, tmp361);
    tmp363 = NofibPrelude.Cons(tmp358, tmp362);
    tmp364 = NofibPrelude.Cons(tmp357, tmp363);
    tmp365 = NofibPrelude.Cons(tmp356, tmp364);
    tmp366 = NofibPrelude.nofibStringToList("     ");
    tmp367 = NofibPrelude.nofibStringToList("  ;; ");
    tmp368 = NofibPrelude.nofibStringToList("     ");
    tmp369 = NofibPrelude.nofibStringToList("  ;; ");
    tmp370 = NofibPrelude.nofibStringToList(" ;;  ");
    tmp371 = NofibPrelude.Cons(tmp370, NofibPrelude.Nil);
    tmp372 = NofibPrelude.Cons(tmp369, tmp371);
    tmp373 = NofibPrelude.Cons(tmp368, tmp372);
    tmp374 = NofibPrelude.Cons(tmp367, tmp373);
    tmp375 = NofibPrelude.Cons(tmp366, tmp374);
    tmp376 = NofibPrelude.Cons([
      ";",
      tmp375
    ], NofibPrelude.Nil);
    tmp377 = NofibPrelude.Cons([
      ":",
      tmp365
    ], tmp376);
    tmp378 = NofibPrelude.Cons([
      "+",
      tmp355
    ], tmp377);
    tmp379 = NofibPrelude.Cons([
      "-",
      tmp345
    ], tmp378);
    tmp380 = NofibPrelude.Cons([
      "!",
      tmp335
    ], tmp379);
    tmp381 = NofibPrelude.Cons([
      "?",
      tmp325
    ], tmp380);
    tmp382 = NofibPrelude.Cons([
      ".",
      tmp315
    ], tmp381);
    this.punct = tmp382;
    tmp383 = NofibPrelude.nofibStringToList(" OOO ");
    tmp384 = NofibPrelude.nofibStringToList("0  00");
    tmp385 = NofibPrelude.nofibStringToList("0 0 0");
    tmp386 = NofibPrelude.nofibStringToList("00  0");
    tmp387 = NofibPrelude.nofibStringToList(" 000 ");
    tmp388 = NofibPrelude.Cons(tmp387, NofibPrelude.Nil);
    tmp389 = NofibPrelude.Cons(tmp386, tmp388);
    tmp390 = NofibPrelude.Cons(tmp385, tmp389);
    tmp391 = NofibPrelude.Cons(tmp384, tmp390);
    tmp392 = NofibPrelude.Cons(tmp383, tmp391);
    tmp393 = NofibPrelude.nofibStringToList("  1  ");
    tmp394 = NofibPrelude.nofibStringToList(" 11  ");
    tmp395 = NofibPrelude.nofibStringToList("  1  ");
    tmp396 = NofibPrelude.nofibStringToList("  1  ");
    tmp397 = NofibPrelude.nofibStringToList("11111");
    tmp398 = NofibPrelude.Cons(tmp397, NofibPrelude.Nil);
    tmp399 = NofibPrelude.Cons(tmp396, tmp398);
    tmp400 = NofibPrelude.Cons(tmp395, tmp399);
    tmp401 = NofibPrelude.Cons(tmp394, tmp400);
    tmp402 = NofibPrelude.Cons(tmp393, tmp401);
    tmp403 = NofibPrelude.nofibStringToList(" 222 ");
    tmp404 = NofibPrelude.nofibStringToList("2   2");
    tmp405 = NofibPrelude.nofibStringToList("   2 ");
    tmp406 = NofibPrelude.nofibStringToList("  2  ");
    tmp407 = NofibPrelude.nofibStringToList("22222");
    tmp408 = NofibPrelude.Cons(tmp407, NofibPrelude.Nil);
    tmp409 = NofibPrelude.Cons(tmp406, tmp408);
    tmp410 = NofibPrelude.Cons(tmp405, tmp409);
    tmp411 = NofibPrelude.Cons(tmp404, tmp410);
    tmp412 = NofibPrelude.Cons(tmp403, tmp411);
    tmp413 = NofibPrelude.nofibStringToList("3333 ");
    tmp414 = NofibPrelude.nofibStringToList("    3");
    tmp415 = NofibPrelude.nofibStringToList(" 333 ");
    tmp416 = NofibPrelude.nofibStringToList("    3");
    tmp417 = NofibPrelude.nofibStringToList("3333 ");
    tmp418 = NofibPrelude.Cons(tmp417, NofibPrelude.Nil);
    tmp419 = NofibPrelude.Cons(tmp416, tmp418);
    tmp420 = NofibPrelude.Cons(tmp415, tmp419);
    tmp421 = NofibPrelude.Cons(tmp414, tmp420);
    tmp422 = NofibPrelude.Cons(tmp413, tmp421);
    tmp423 = NofibPrelude.nofibStringToList("   4 ");
    tmp424 = NofibPrelude.nofibStringToList("  44 ");
    tmp425 = NofibPrelude.nofibStringToList(" 4 4 ");
    tmp426 = NofibPrelude.nofibStringToList("44444");
    tmp427 = NofibPrelude.nofibStringToList("   4 ");
    tmp428 = NofibPrelude.Cons(tmp427, NofibPrelude.Nil);
    tmp429 = NofibPrelude.Cons(tmp426, tmp428);
    tmp430 = NofibPrelude.Cons(tmp425, tmp429);
    tmp431 = NofibPrelude.Cons(tmp424, tmp430);
    tmp432 = NofibPrelude.Cons(tmp423, tmp431);
    tmp433 = NofibPrelude.nofibStringToList("55555");
    tmp434 = NofibPrelude.nofibStringToList("5    ");
    tmp435 = NofibPrelude.nofibStringToList("5555 ");
    tmp436 = NofibPrelude.nofibStringToList("    5");
    tmp437 = NofibPrelude.nofibStringToList("5555 ");
    tmp438 = NofibPrelude.Cons(tmp437, NofibPrelude.Nil);
    tmp439 = NofibPrelude.Cons(tmp436, tmp438);
    tmp440 = NofibPrelude.Cons(tmp435, tmp439);
    tmp441 = NofibPrelude.Cons(tmp434, tmp440);
    tmp442 = NofibPrelude.Cons(tmp433, tmp441);
    tmp443 = NofibPrelude.nofibStringToList("   66");
    tmp444 = NofibPrelude.nofibStringToList("  6  ");
    tmp445 = NofibPrelude.nofibStringToList(" 666 ");
    tmp446 = NofibPrelude.nofibStringToList("6   6");
    tmp447 = NofibPrelude.nofibStringToList(" 666 ");
    tmp448 = NofibPrelude.Cons(tmp447, NofibPrelude.Nil);
    tmp449 = NofibPrelude.Cons(tmp446, tmp448);
    tmp450 = NofibPrelude.Cons(tmp445, tmp449);
    tmp451 = NofibPrelude.Cons(tmp444, tmp450);
    tmp452 = NofibPrelude.Cons(tmp443, tmp451);
    tmp453 = NofibPrelude.nofibStringToList("77777");
    tmp454 = NofibPrelude.nofibStringToList("    7");
    tmp455 = NofibPrelude.nofibStringToList("   7 ");
    tmp456 = NofibPrelude.nofibStringToList("   7 ");
    tmp457 = NofibPrelude.nofibStringToList("  7  ");
    tmp458 = NofibPrelude.Cons(tmp457, NofibPrelude.Nil);
    tmp459 = NofibPrelude.Cons(tmp456, tmp458);
    tmp460 = NofibPrelude.Cons(tmp455, tmp459);
    tmp461 = NofibPrelude.Cons(tmp454, tmp460);
    tmp462 = NofibPrelude.Cons(tmp453, tmp461);
    tmp463 = NofibPrelude.nofibStringToList(" 888 ");
    tmp464 = NofibPrelude.nofibStringToList("8   8");
    tmp465 = NofibPrelude.nofibStringToList(" 888 ");
    tmp466 = NofibPrelude.nofibStringToList("8   8");
    tmp467 = NofibPrelude.nofibStringToList(" 888 ");
    tmp468 = NofibPrelude.Cons(tmp467, NofibPrelude.Nil);
    tmp469 = NofibPrelude.Cons(tmp466, tmp468);
    tmp470 = NofibPrelude.Cons(tmp465, tmp469);
    tmp471 = NofibPrelude.Cons(tmp464, tmp470);
    tmp472 = NofibPrelude.Cons(tmp463, tmp471);
    tmp473 = NofibPrelude.nofibStringToList(" 999 ");
    tmp474 = NofibPrelude.nofibStringToList("9   9");
    tmp475 = NofibPrelude.nofibStringToList(" 999 ");
    tmp476 = NofibPrelude.nofibStringToList("  9  ");
    tmp477 = NofibPrelude.nofibStringToList("99   ");
    tmp478 = NofibPrelude.Cons(tmp477, NofibPrelude.Nil);
    tmp479 = NofibPrelude.Cons(tmp476, tmp478);
    tmp480 = NofibPrelude.Cons(tmp475, tmp479);
    tmp481 = NofibPrelude.Cons(tmp474, tmp480);
    tmp482 = NofibPrelude.Cons(tmp473, tmp481);
    tmp483 = NofibPrelude.Cons(tmp482, NofibPrelude.Nil);
    tmp484 = NofibPrelude.Cons(tmp472, tmp483);
    tmp485 = NofibPrelude.Cons(tmp462, tmp484);
    tmp486 = NofibPrelude.Cons(tmp452, tmp485);
    tmp487 = NofibPrelude.Cons(tmp442, tmp486);
    tmp488 = NofibPrelude.Cons(tmp432, tmp487);
    tmp489 = NofibPrelude.Cons(tmp422, tmp488);
    tmp490 = NofibPrelude.Cons(tmp412, tmp489);
    tmp491 = NofibPrelude.Cons(tmp402, tmp490);
    tmp492 = NofibPrelude.Cons(tmp392, tmp491);
    this.digits = tmp492;
    lambda2 = (undefined, function () {
      let tmp493;
      tmp493 = banner.testBanner_nofib(1);
      return NofibPrelude.nofibListToString(tmp493)
    });
    BenchmarkPrelude.benchmark(lambda2)
  }
  static unlines(ls) {
    let tmp;
    tmp = NofibPrelude.map(lambda, ls);
    return NofibPrelude.concat(tmp)
  } 
  static join(ls1) {
    let tmp;
    tmp = lambda1;
    return NofibPrelude.foldr1(tmp, ls1)
  } 
  static isUpper(c) {
    let n, scrut, scrut1, tmp;
    tmp = NofibPrelude.int_of_char(c);
    n = tmp;
    scrut = n >= 65;
    if (scrut === true) {
      scrut1 = n <= 90;
      if (scrut1 === true) {
        return true
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static isLower(c1) {
    let n, scrut, scrut1, tmp;
    tmp = NofibPrelude.int_of_char(c1);
    n = tmp;
    scrut = n >= 97;
    if (scrut === true) {
      scrut1 = n <= 122;
      if (scrut1 === true) {
        return true
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static isDigit(c2) {
    let n, scrut, scrut1, tmp;
    tmp = NofibPrelude.int_of_char(c2);
    n = tmp;
    scrut = n >= 48;
    if (scrut === true) {
      scrut1 = n <= 57;
      if (scrut1 === true) {
        return true
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static isSpace(c3) {
    let n, tmp;
    tmp = NofibPrelude.int_of_char(c3);
    n = tmp;
    return n == 32
  } 
  static picChar(c4) {
    let scrut, scrut1, scrut2, scrut3, scrut4, scrut5, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12;
    scrut5 = banner.isUpper(c4);
    if (scrut5 === true) {
      tmp = NofibPrelude.int_of_char(c4);
      tmp1 = NofibPrelude.int_of_char("A");
      tmp2 = tmp - tmp1;
      return NofibPrelude.atIndex(tmp2, banner.alphas)
    } else {
      scrut4 = banner.isLower(c4);
      if (scrut4 === true) {
        tmp3 = NofibPrelude.int_of_char(c4);
        tmp4 = NofibPrelude.int_of_char("a");
        tmp5 = tmp3 - tmp4;
        return NofibPrelude.atIndex(tmp5, banner.alphas)
      } else {
        scrut3 = banner.isSpace(c4);
        if (scrut3 === true) {
          return banner.blank
        } else {
          scrut2 = banner.isDigit(c4);
          if (scrut2 === true) {
            tmp6 = NofibPrelude.int_of_char(c4);
            tmp7 = NofibPrelude.int_of_char("0");
            tmp8 = tmp6 - tmp7;
            return NofibPrelude.atIndex(tmp8, banner.digits)
          } else {
            scrut1 = c4 === "/";
            if (scrut1 === true) {
              return banner.slant
            } else {
              scrut = c4 === "=";
              if (scrut === true) {
                return NofibPrelude.reverse(banner.slant)
              } else {
                tmp9 = lscomp$(c4, banner.punct);
                tmp10 = NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil);
                tmp11 = NofibPrelude.Cons(NofibPrelude.Nil, tmp10);
                tmp12 = NofibPrelude.append(tmp9, tmp11);
                return NofibPrelude.head(tmp12)
              }
            }
          }
        }
      }
    }
  } 
  static say(s) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = NofibPrelude.map(banner.picChar, s);
    tmp1 = NofibPrelude.transpose(tmp);
    tmp2 = NofibPrelude.map(banner.join, tmp1);
    tmp3 = banner.unlines(tmp2);
    return NofibPrelude.Cons("\n", tmp3)
  } 
  static testBanner_nofib(n) {
    let x, tmp, tmp1, tmp2;
    tmp = NofibPrelude.nofibStringToList("Is this not a great banner?");
    x = tmp;
    tmp1 = NofibPrelude.replicate(n, x);
    tmp2 = NofibPrelude.concat(tmp1);
    return banner.say(tmp2)
  }
  static toString() { return "banner"; }
};
let banner = banner1; export default banner;
