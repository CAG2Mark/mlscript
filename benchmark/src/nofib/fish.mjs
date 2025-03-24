import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let fish1;
fish1 = class fish {
  static #ls;
  static {
    fish1 = fish;
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75, tmp76, tmp77, tmp78, tmp79, tmp80, tmp81, tmp82, tmp83, tmp84, tmp85, tmp86, tmp87, tmp88, tmp89, tmp90, tmp91, tmp92, tmp93, tmp94, tmp95, tmp96, tmp97, tmp98, tmp99, tmp100, tmp101, tmp102, tmp103, tmp104, tmp105, tmp106, tmp107, tmp108, tmp109, tmp110, tmp111, tmp112, tmp113, tmp114, tmp115, tmp116, tmp117, tmp118, tmp119, tmp120, lambda;
    tmp = NofibPrelude.Cons([
      14,
      2,
      16,
      2
    ], NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons([
      11,
      0,
      14,
      2
    ], tmp);
    tmp2 = NofibPrelude.Cons([
      13,
      5,
      16,
      4
    ], tmp1);
    tmp3 = NofibPrelude.Cons([
      10,
      4,
      13,
      5
    ], tmp2);
    tmp4 = NofibPrelude.Cons([
      12,
      7,
      16,
      6
    ], tmp3);
    tmp5 = NofibPrelude.Cons([
      9,
      6,
      12,
      7
    ], tmp4);
    tmp6 = NofibPrelude.Cons([
      12,
      9,
      16,
      8
    ], tmp5);
    tmp7 = NofibPrelude.Cons([
      8,
      8,
      12,
      9
    ], tmp6);
    tmp8 = NofibPrelude.Cons([
      8,
      12,
      16,
      10
    ], tmp7);
    tmp9 = NofibPrelude.Cons([
      14,
      16,
      16,
      15
    ], tmp8);
    tmp10 = NofibPrelude.Cons([
      13,
      15,
      16,
      14
    ], tmp9);
    tmp11 = NofibPrelude.Cons([
      12,
      16,
      13,
      15
    ], tmp10);
    tmp12 = NofibPrelude.Cons([
      12,
      14,
      16,
      13
    ], tmp11);
    tmp13 = NofibPrelude.Cons([
      10,
      16,
      12,
      14
    ], tmp12);
    tmp14 = NofibPrelude.Cons([
      12,
      12,
      16,
      12
    ], tmp13);
    tmp15 = NofibPrelude.Cons([
      8,
      16,
      12,
      12
    ], tmp14);
    tmp16 = NofibPrelude.Cons([
      6,
      15,
      8,
      16
    ], tmp15);
    tmp17 = NofibPrelude.Cons([
      0,
      16,
      6,
      15
    ], tmp16);
    tmp18 = NofibPrelude.Cons([
      4,
      13,
      0,
      16
    ], tmp17);
    tmp19 = NofibPrelude.Cons([
      8,
      8,
      4,
      13
    ], tmp18);
    tmp20 = NofibPrelude.Cons([
      9,
      6,
      8,
      8
    ], tmp19);
    tmp21 = NofibPrelude.Cons([
      10,
      4,
      9,
      6
    ], tmp20);
    tmp22 = NofibPrelude.Cons([
      11,
      0,
      10,
      4
    ], tmp21);
    tmp23 = NofibPrelude.Cons([
      7,
      6,
      4,
      5
    ], tmp22);
    tmp24 = NofibPrelude.Cons([
      4,
      10,
      7,
      6
    ], tmp23);
    tmp25 = NofibPrelude.Cons([
      4,
      5,
      4,
      10
    ], tmp24);
    tmp26 = NofibPrelude.Cons([
      6,
      0,
      4,
      4
    ], tmp25);
    tmp27 = NofibPrelude.Cons([
      0,
      8,
      0,
      3
    ], tmp26);
    tmp28 = NofibPrelude.Cons([
      3,
      4,
      0,
      8
    ], tmp27);
    tmp29 = NofibPrelude.Cons([
      0,
      3,
      3,
      4
    ], tmp28);
    this.p_tile = tmp29;
    tmp30 = NofibPrelude.Cons([
      0,
      12,
      0,
      16
    ], NofibPrelude.Nil);
    tmp31 = NofibPrelude.Cons([
      0,
      0,
      0,
      8
    ], tmp30);
    tmp32 = NofibPrelude.Cons([
      12,
      0,
      16,
      0
    ], tmp31);
    tmp33 = NofibPrelude.Cons([
      0,
      0,
      8,
      0
    ], tmp32);
    tmp34 = NofibPrelude.Cons([
      15,
      0,
      16,
      2
    ], tmp33);
    tmp35 = NofibPrelude.Cons([
      14,
      0,
      16,
      4
    ], tmp34);
    tmp36 = NofibPrelude.Cons([
      13,
      0,
      16,
      6
    ], tmp35);
    tmp37 = NofibPrelude.Cons([
      15,
      10,
      16,
      16
    ], tmp36);
    tmp38 = NofibPrelude.Cons([
      16,
      8,
      15,
      10
    ], tmp37);
    tmp39 = NofibPrelude.Cons([
      13,
      4,
      16,
      8
    ], tmp38);
    tmp40 = NofibPrelude.Cons([
      12,
      0,
      13,
      4
    ], tmp39);
    tmp41 = NofibPrelude.Cons([
      10,
      0,
      14,
      11
    ], tmp40);
    tmp42 = NofibPrelude.Cons([
      8,
      5,
      8,
      8
    ], tmp41);
    tmp43 = NofibPrelude.Cons([
      6,
      0,
      8,
      5
    ], tmp42);
    tmp44 = NofibPrelude.Cons([
      6,
      5,
      6,
      7
    ], tmp43);
    tmp45 = NofibPrelude.Cons([
      4,
      0,
      6,
      5
    ], tmp44);
    tmp46 = NofibPrelude.Cons([
      4,
      5,
      4,
      7
    ], tmp45);
    tmp47 = NofibPrelude.Cons([
      2,
      0,
      4,
      5
    ], tmp46);
    tmp48 = NofibPrelude.Cons([
      12,
      12,
      10,
      10
    ], tmp47);
    tmp49 = NofibPrelude.Cons([
      8,
      12,
      12,
      12
    ], tmp48);
    tmp50 = NofibPrelude.Cons([
      10,
      10,
      8,
      12
    ], tmp49);
    tmp51 = NofibPrelude.Cons([
      11,
      15,
      9,
      13
    ], tmp50);
    tmp52 = NofibPrelude.Cons([
      8,
      15,
      11,
      15
    ], tmp51);
    tmp53 = NofibPrelude.Cons([
      9,
      13,
      8,
      15
    ], tmp52);
    tmp54 = NofibPrelude.Cons([
      0,
      10,
      7,
      11
    ], tmp53);
    tmp55 = NofibPrelude.Cons([
      6,
      16,
      7,
      15
    ], tmp54);
    tmp56 = NofibPrelude.Cons([
      4,
      16,
      5,
      14
    ], tmp55);
    tmp57 = NofibPrelude.Cons([
      2,
      16,
      3,
      13
    ], tmp56);
    tmp58 = NofibPrelude.Cons([
      7,
      15,
      8,
      16
    ], tmp57);
    tmp59 = NofibPrelude.Cons([
      5,
      14,
      7,
      15
    ], tmp58);
    tmp60 = NofibPrelude.Cons([
      3,
      13,
      5,
      14
    ], tmp59);
    tmp61 = NofibPrelude.Cons([
      0,
      12,
      3,
      13
    ], tmp60);
    tmp62 = NofibPrelude.Cons([
      12,
      10,
      16,
      16
    ], tmp61);
    tmp63 = NofibPrelude.Cons([
      8,
      8,
      12,
      10
    ], tmp62);
    tmp64 = NofibPrelude.Cons([
      6,
      7,
      8,
      8
    ], tmp63);
    tmp65 = NofibPrelude.Cons([
      4,
      7,
      6,
      7
    ], tmp64);
    tmp66 = NofibPrelude.Cons([
      0,
      8,
      4,
      7
    ], tmp65);
    this.q_tile = tmp66;
    tmp67 = NofibPrelude.Cons([
      15,
      15,
      16,
      14
    ], NofibPrelude.Nil);
    tmp68 = NofibPrelude.Cons([
      14,
      14,
      16,
      12
    ], tmp67);
    tmp69 = NofibPrelude.Cons([
      13,
      13,
      16,
      10
    ], tmp68);
    tmp70 = NofibPrelude.Cons([
      12,
      12,
      16,
      8
    ], tmp69);
    tmp71 = NofibPrelude.Cons([
      11,
      16,
      12,
      12
    ], tmp70);
    tmp72 = NofibPrelude.Cons([
      12,
      3,
      16,
      0
    ], tmp71);
    tmp73 = NofibPrelude.Cons([
      5,
      5,
      12,
      3
    ], tmp72);
    tmp74 = NofibPrelude.Cons([
      8,
      2,
      12,
      0
    ], tmp73);
    tmp75 = NofibPrelude.Cons([
      3,
      3,
      8,
      2
    ], tmp74);
    tmp76 = NofibPrelude.Cons([
      2,
      2,
      8,
      0
    ], tmp75);
    tmp77 = NofibPrelude.Cons([
      1,
      1,
      4,
      0
    ], tmp76);
    tmp78 = NofibPrelude.Cons([
      12,
      12,
      11,
      16
    ], tmp77);
    tmp79 = NofibPrelude.Cons([
      16,
      8,
      12,
      12
    ], tmp78);
    tmp80 = NofibPrelude.Cons([
      2,
      12,
      0,
      16
    ], tmp79);
    tmp81 = NofibPrelude.Cons([
      5,
      10,
      2,
      12
    ], tmp80);
    tmp82 = NofibPrelude.Cons([
      8,
      8,
      5,
      10
    ], tmp81);
    tmp83 = NofibPrelude.Cons([
      14,
      6,
      8,
      8
    ], tmp82);
    tmp84 = NofibPrelude.Cons([
      16,
      4,
      14,
      6
    ], tmp83);
    tmp85 = NofibPrelude.Cons([
      11,
      10,
      6,
      16
    ], tmp84);
    tmp86 = NofibPrelude.Cons([
      16,
      6,
      11,
      10
    ], tmp85);
    tmp87 = NofibPrelude.Cons([
      0,
      12,
      1,
      14
    ], tmp86);
    tmp88 = NofibPrelude.Cons([
      0,
      8,
      2,
      12
    ], tmp87);
    tmp89 = NofibPrelude.Cons([
      0,
      4,
      5,
      10
    ], tmp88);
    tmp90 = NofibPrelude.Cons([
      12,
      12,
      16,
      16
    ], tmp89);
    tmp91 = NofibPrelude.Cons([
      0,
      0,
      8,
      8
    ], tmp90);
    this.r_tile = tmp91;
    tmp92 = NofibPrelude.Cons([
      15,
      8,
      15,
      5
    ], NofibPrelude.Nil);
    tmp93 = NofibPrelude.Cons([
      13,
      7,
      15,
      8
    ], tmp92);
    tmp94 = NofibPrelude.Cons([
      15,
      5,
      13,
      7
    ], tmp93);
    tmp95 = NofibPrelude.Cons([
      12,
      7,
      12,
      4
    ], tmp94);
    tmp96 = NofibPrelude.Cons([
      10,
      6,
      12,
      7
    ], tmp95);
    tmp97 = NofibPrelude.Cons([
      12,
      4,
      10,
      6
    ], tmp96);
    tmp98 = NofibPrelude.Cons([
      10,
      16,
      11,
      10
    ], tmp97);
    tmp99 = NofibPrelude.Cons([
      15,
      9,
      16,
      8
    ], tmp98);
    tmp100 = NofibPrelude.Cons([
      14,
      11,
      15,
      9
    ], tmp99);
    tmp101 = NofibPrelude.Cons([
      13,
      13,
      14,
      11
    ], tmp100);
    tmp102 = NofibPrelude.Cons([
      12,
      16,
      13,
      13
    ], tmp101);
    tmp103 = NofibPrelude.Cons([
      7,
      13,
      8,
      16
    ], tmp102);
    tmp104 = NofibPrelude.Cons([
      7,
      8,
      7,
      13
    ], tmp103);
    tmp105 = NofibPrelude.Cons([
      8,
      6,
      7,
      8
    ], tmp104);
    tmp106 = NofibPrelude.Cons([
      10,
      4,
      8,
      6
    ], tmp105);
    tmp107 = NofibPrelude.Cons([
      16,
      0,
      10,
      4
    ], tmp106);
    tmp108 = NofibPrelude.Cons([
      15,
      9,
      16,
      10
    ], tmp107);
    tmp109 = NofibPrelude.Cons([
      14,
      11,
      16,
      12
    ], tmp108);
    tmp110 = NofibPrelude.Cons([
      13,
      13,
      16,
      14
    ], tmp109);
    tmp111 = NofibPrelude.Cons([
      0,
      14,
      7,
      13
    ], tmp110);
    tmp112 = NofibPrelude.Cons([
      0,
      12,
      7,
      10
    ], tmp111);
    tmp113 = NofibPrelude.Cons([
      0,
      10,
      7,
      8
    ], tmp112);
    tmp114 = NofibPrelude.Cons([
      0,
      8,
      8,
      6
    ], tmp113);
    tmp115 = NofibPrelude.Cons([
      0,
      6,
      7,
      4
    ], tmp114);
    tmp116 = NofibPrelude.Cons([
      0,
      4,
      2,
      1
    ], tmp115);
    tmp117 = NofibPrelude.Cons([
      8,
      2,
      16,
      0
    ], tmp116);
    tmp118 = NofibPrelude.Cons([
      4,
      2,
      8,
      2
    ], tmp117);
    tmp119 = NofibPrelude.Cons([
      0,
      0,
      4,
      2
    ], tmp118);
    this.s_tile = tmp119;
    lambda = (undefined, function () {
      return fish.testFish_nofib(1)
    });
    tmp120 = BenchmarkPrelude.benchmark(lambda);
    fish.#ls = tmp120;
    fish.#ls
  }
  static vec_add(v1, v2) {
    let first1, first0, x1, y1, first11, first01, x2, y2, tmp, tmp1;
    if (globalThis.Array.isArray(v1) && v1.length === 2) {
      first0 = v1[0];
      first1 = v1[1];
      x1 = first0;
      y1 = first1;
      if (globalThis.Array.isArray(v2) && v2.length === 2) {
        first01 = v2[0];
        first11 = v2[1];
        x2 = first01;
        y2 = first11;
        tmp = x1 + x2;
        tmp1 = y1 + y2;
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
  static vec_sub(v11, v21) {
    let first1, first0, x1, y1, first11, first01, x2, y2, tmp, tmp1;
    if (globalThis.Array.isArray(v11) && v11.length === 2) {
      first0 = v11[0];
      first1 = v11[1];
      x1 = first0;
      y1 = first1;
      if (globalThis.Array.isArray(v21) && v21.length === 2) {
        first01 = v21[0];
        first11 = v21[1];
        x2 = first01;
        y2 = first11;
        tmp = x1 - x2;
        tmp1 = y1 - y2;
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
  static scale_vec2(v, a, b) {
    let first1, first0, x, y, tmp, tmp1, tmp2, tmp3;
    if (globalThis.Array.isArray(v) && v.length === 2) {
      first0 = v[0];
      first1 = v[1];
      x = first0;
      y = first1;
      tmp = x * a;
      tmp1 = NofibPrelude.intDiv(tmp, b);
      tmp2 = y * a;
      tmp3 = NofibPrelude.intDiv(tmp2, b);
      return [
        tmp1,
        tmp3
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static nil(a1, b1, c) {
    return NofibPrelude.Nil
  } 
  static tup2(a_b, c_d) {
    let first1, first0, a2, b2, first11, first01, c1, d;
    if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
      first0 = a_b[0];
      first1 = a_b[1];
      a2 = first0;
      b2 = first1;
      if (globalThis.Array.isArray(c_d) && c_d.length === 2) {
        first01 = c_d[0];
        first11 = c_d[1];
        c1 = first01;
        d = first11;
        return [
          a2,
          b2,
          c1,
          d
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static grid(m, n, segments, a2, b2, c1) {
    let lscomp;
    lscomp = function lscomp(ls) {
      let param0, param1, first3, first2, first1, first0, x0, y0, x1, y1, t, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        if (globalThis.Array.isArray(param0) && param0.length === 4) {
          first0 = param0[0];
          first1 = param0[1];
          first2 = param0[2];
          first3 = param0[3];
          x0 = first0;
          y0 = first1;
          x1 = first2;
          y1 = first3;
          t = param1;
          tmp = fish.scale_vec2(b2, x0, m);
          tmp1 = fish.vec_add(a2, tmp);
          tmp2 = fish.scale_vec2(c1, y0, n);
          tmp3 = fish.vec_add(tmp1, tmp2);
          tmp4 = fish.scale_vec2(b2, x1, m);
          tmp5 = fish.vec_add(a2, tmp4);
          tmp6 = fish.scale_vec2(c1, y1, n);
          tmp7 = fish.vec_add(tmp5, tmp6);
          tmp8 = fish.tup2(tmp3, tmp7);
          tmp9 = lscomp(t);
          return NofibPrelude.Cons(tmp8, tmp9)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    return lscomp(segments)
  } 
  static rot(p, a3, b3, c2) {
    let tmp, tmp1;
    tmp = fish.vec_add(a3, b3);
    tmp1 = fish.vec_sub([
      0,
      0
    ], b3);
    return runtime.safeCall(p(tmp, c2, tmp1))
  } 
  static beside(m1, n1, p1, q, a4, b4, c3) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    tmp = m1 + n1;
    tmp1 = fish.scale_vec2(b4, m1, tmp);
    tmp2 = runtime.safeCall(p1(a4, tmp1, c3));
    tmp3 = m1 + n1;
    tmp4 = fish.scale_vec2(b4, m1, tmp3);
    tmp5 = fish.vec_add(a4, tmp4);
    tmp6 = n1 + m1;
    tmp7 = fish.scale_vec2(b4, n1, tmp6);
    tmp8 = runtime.safeCall(q(tmp5, tmp7, c3));
    return NofibPrelude.append(tmp2, tmp8)
  } 
  static above(m2, n2, p2, q1, a5, b5, c4) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    tmp = m2 + n2;
    tmp1 = fish.scale_vec2(c4, n2, tmp);
    tmp2 = fish.vec_add(a5, tmp1);
    tmp3 = n2 + m2;
    tmp4 = fish.scale_vec2(c4, m2, tmp3);
    tmp5 = runtime.safeCall(p2(tmp2, b5, tmp4));
    tmp6 = m2 + n2;
    tmp7 = fish.scale_vec2(c4, n2, tmp6);
    tmp8 = runtime.safeCall(q1(a5, b5, tmp7));
    return NofibPrelude.append(tmp5, tmp8)
  } 
  static tile_to_grid(arg, arg2, arg3, arg4) {
    return fish.grid(16, 16, arg, arg2, arg3, arg4)
  } 
  static p(arg1, q6, q7) {
    return fish.tile_to_grid(fish.p_tile, arg1, q6, q7)
  } 
  static q(arg5, q61, q71) {
    return fish.tile_to_grid(fish.q_tile, arg5, q61, q71)
  } 
  static r(arg6, q62, q72) {
    return fish.tile_to_grid(fish.r_tile, arg6, q62, q72)
  } 
  static s(arg7, q63, q73) {
    return fish.tile_to_grid(fish.s_tile, arg7, q63, q73)
  } 
  static quartet(a6, b6, c5, d, arg8, a61, a7) {
    let lambda, lambda1;
    lambda = (undefined, function (p5, p6, p7) {
      return fish.beside(1, 1, a6, b6, p5, p6, p7)
    });
    lambda1 = (undefined, function (p5, p6, p7) {
      return fish.beside(1, 1, c5, d, p5, p6, p7)
    });
    return fish.above(1, 1, lambda, lambda1, arg8, a61, a7)
  } 
  static t(arg9, q64, q74) {
    return fish.quartet(fish.p, fish.q, fish.r, fish.s, arg9, q64, q74)
  } 
  static cycle_(p11, arg10, p3, p4) {
    let lambda, lambda1, lambda2;
    lambda = (undefined, function (a8, b7, c6) {
      let lambda3;
      lambda3 = (undefined, function (a9, b8, c7) {
        let lambda4;
        lambda4 = (undefined, function (a10, b9, c8) {
          return fish.rot(p11, a10, b9, c8)
        });
        return fish.rot(lambda4, a9, b8, c7)
      });
      return fish.rot(lambda3, a8, b7, c6)
    });
    lambda1 = (undefined, function (a8, b7, c6) {
      return fish.rot(p11, a8, b7, c6)
    });
    lambda2 = (undefined, function (a8, b7, c6) {
      let lambda3;
      lambda3 = (undefined, function (a9, b8, c7) {
        return fish.rot(p11, a9, b8, c7)
      });
      return fish.rot(lambda3, a8, b7, c6)
    });
    return fish.quartet(p11, lambda, lambda1, lambda2, arg10, p3, p4)
  } 
  static u(arg11, p21, p31) {
    let lambda;
    lambda = (undefined, function (a8, b7, c6) {
      return fish.rot(fish.q, a8, b7, c6)
    });
    return fish.cycle_(lambda, arg11, p21, p31)
  } 
  static side1(arg12, q65, q75) {
    let lambda;
    lambda = (undefined, function (a8, b7, c6) {
      return fish.rot(fish.t, a8, b7, c6)
    });
    return fish.quartet(fish.nil, fish.nil, lambda, fish.t, arg12, q65, q75)
  } 
  static side2(arg13, q66, q76) {
    let lambda;
    lambda = (undefined, function (a8, b7, c6) {
      return fish.rot(fish.t, a8, b7, c6)
    });
    return fish.quartet(fish.side1, fish.side1, lambda, fish.t, arg13, q66, q76)
  } 
  static corner1(arg14, q67, q77) {
    return fish.quartet(fish.nil, fish.nil, fish.nil, fish.u, arg14, q67, q77)
  } 
  static corner2(arg15, q68, q78) {
    let lambda;
    lambda = (undefined, function (a8, b7, c6) {
      return fish.rot(fish.side1, a8, b7, c6)
    });
    return fish.quartet(fish.corner1, fish.side1, lambda, fish.u, arg15, q68, q78)
  } 
  static pseudocorner(arg16, q69, q79) {
    let lambda, lambda1;
    lambda = (undefined, function (a8, b7, c6) {
      return fish.rot(fish.side2, a8, b7, c6)
    });
    lambda1 = (undefined, function (a8, b7, c6) {
      return fish.rot(fish.t, a8, b7, c6)
    });
    return fish.quartet(fish.corner2, fish.side2, lambda, lambda1, arg16, q69, q79)
  } 
  static pseudolimit(arg17, p22, p32) {
    return fish.cycle_(fish.pseudocorner, arg17, p22, p32)
  } 
  static nonet(p12, p23, p33, p41, p5, p6, p7, p8, p9, arg18, arg21) {
    let lambda, lambda1;
    lambda = (undefined, function (b51, b61, b7) {
      let lambda2;
      lambda2 = (undefined, function (b52, b62, b71) {
        return fish.beside(1, 1, p23, p33, b52, b62, b71)
      });
      return fish.beside(1, 2, p12, lambda2, b51, b61, b7)
    });
    lambda1 = (undefined, function (a11, a21, a31) {
      let lambda2, lambda3;
      lambda2 = (undefined, function (b51, b61, b7) {
        let lambda4;
        lambda4 = (undefined, function (b52, b62, b71) {
          return fish.beside(1, 1, p5, p6, b52, b62, b71)
        });
        return fish.beside(1, 2, p41, lambda4, b51, b61, b7)
      });
      lambda3 = (undefined, function (b51, b61, b7) {
        let lambda4;
        lambda4 = (undefined, function (b52, b62, b71) {
          return fish.beside(1, 1, p8, p9, b52, b62, b71)
        });
        return fish.beside(1, 2, p7, lambda4, b51, b61, b7)
      });
      return fish.above(1, 1, lambda2, lambda3, a11, a21, a31)
    });
    return fish.above(1, 2, lambda, lambda1, arg18, arg21)
  } 
  static showFourTupleofInt(a_b_c_d) {
    let first3, first2, first1, first0, a8, b7, c6, d1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17;
    if (globalThis.Array.isArray(a_b_c_d) && a_b_c_d.length === 4) {
      first0 = a_b_c_d[0];
      first1 = a_b_c_d[1];
      first2 = a_b_c_d[2];
      first3 = a_b_c_d[3];
      a8 = first0;
      b7 = first1;
      c6 = first2;
      d1 = first3;
      tmp = NofibPrelude.nofibStringToList("(");
      tmp1 = NofibPrelude.stringOfInt(a8);
      tmp2 = NofibPrelude.nofibStringToList(tmp1);
      tmp3 = NofibPrelude.nofibStringToList(",");
      tmp4 = NofibPrelude.stringOfInt(b7);
      tmp5 = NofibPrelude.nofibStringToList(tmp4);
      tmp6 = NofibPrelude.nofibStringToList(",");
      tmp7 = NofibPrelude.stringOfInt(c6);
      tmp8 = NofibPrelude.nofibStringToList(tmp7);
      tmp9 = NofibPrelude.nofibStringToList(",");
      tmp10 = NofibPrelude.stringOfInt(d1);
      tmp11 = NofibPrelude.nofibStringToList(tmp10);
      tmp12 = NofibPrelude.append(tmp9, tmp11);
      tmp13 = NofibPrelude.append(tmp8, tmp12);
      tmp14 = NofibPrelude.append(tmp6, tmp13);
      tmp15 = NofibPrelude.append(tmp5, tmp14);
      tmp16 = NofibPrelude.append(tmp3, tmp15);
      tmp17 = NofibPrelude.append(tmp2, tmp16);
      return NofibPrelude.append(tmp, tmp17)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static fmt(ls) {
    let showl, param0, param1, x, xs, tmp, tmp1, tmp2, tmp3;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.nofibStringToList("[]")
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x = param0;
      xs = param1;
      showl = function showl(ls1, s) {
        let param01, param11, x1, xs1, tmp4, tmp5, tmp6, tmp7;
        if (ls1 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Cons("]", s)
        } else if (ls1 instanceof NofibPrelude.Cons.class) {
          param01 = ls1.head;
          param11 = ls1.tail;
          x1 = param01;
          xs1 = param11;
          tmp4 = NofibPrelude.nofibStringToList(",|");
          tmp5 = fish.showFourTupleofInt(x1);
          tmp6 = showl(xs1, s);
          tmp7 = NofibPrelude.append(tmp5, tmp6);
          return NofibPrelude.append(tmp4, tmp7)
        } else {
          throw new globalThis.Error("match error");
        }
      };
      tmp = NofibPrelude.nofibStringToList("[|");
      tmp1 = fish.showFourTupleofInt(x);
      tmp2 = showl(xs, "");
      tmp3 = NofibPrelude.append(tmp1, tmp2);
      return NofibPrelude.append(tmp, tmp3)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static testFish_nofib(n3) {
    let tmp, tmp1, lambda;
    lambda = (undefined, function (i) {
      let n4, tmp2, tmp3, tmp4;
      tmp2 = NofibPrelude.min(0, i);
      n4 = tmp2;
      tmp3 = 640 + n4;
      tmp4 = 640 + n4;
      return fish.pseudolimit([
        0,
        0
      ], [
        tmp3,
        0
      ], [
        0,
        tmp4
      ])
    });
    tmp = lambda;
    tmp1 = NofibPrelude.enumFromTo(0, n3);
    return NofibPrelude.map(tmp, tmp1)
  }
  static toString() { return "fish"; }
};
let fish = fish1; export default fish;
