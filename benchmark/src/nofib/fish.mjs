import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let s, tup2, cycle_, t, corner1, nonet, p, r, side2, beside, quartet, showFourTupleofInt, side1, u, rot, vec_sub, vec_add, testFish_nofib, above, nil, grid, pseudocorner, corner2, scale_vec2, q, tile_to_grid, pseudolimit, fmt, p_tile, q_tile, r_tile, s_tile, ls, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75, tmp76, tmp77, tmp78, tmp79, tmp80, tmp81, tmp82, tmp83, tmp84, tmp85, tmp86, tmp87, tmp88, tmp89, tmp90, tmp91, tmp92, tmp93, tmp94, tmp95, tmp96, tmp97, tmp98, tmp99, tmp100, tmp101, tmp102, tmp103, tmp104, tmp105, tmp106, tmp107, tmp108, tmp109, tmp110, tmp111, tmp112, tmp113, tmp114, tmp115, tmp116, tmp117, tmp118, tmp119, tmp120, lambda;
vec_add = function vec_add(v1, v2) {
  let first1, first0, x1, y1, first11, first01, x2, y2, tmp121, tmp122;
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
      tmp121 = x1 + x2;
      tmp122 = y1 + y2;
      return [
        tmp121,
        tmp122
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
vec_sub = function vec_sub(v1, v2) {
  let first1, first0, x1, y1, first11, first01, x2, y2, tmp121, tmp122;
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
      tmp121 = x1 - x2;
      tmp122 = y1 - y2;
      return [
        tmp121,
        tmp122
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
scale_vec2 = function scale_vec2(v, a, b) {
  let first1, first0, x, y, tmp121, tmp122, tmp123, tmp124;
  if (globalThis.Array.isArray(v) && v.length === 2) {
    first0 = v[0];
    first1 = v[1];
    x = first0;
    y = first1;
    tmp121 = x * a;
    tmp122 = NofibPrelude.intDiv(tmp121, b);
    tmp123 = y * a;
    tmp124 = NofibPrelude.intDiv(tmp123, b);
    return [
      tmp122,
      tmp124
    ]
  } else {
    throw new globalThis.Error("match error");
  }
};
nil = function nil(a, b, c) {
  return NofibPrelude.Nil
};
tup2 = function tup2(a_b, c_d) {
  let first1, first0, a, b, first11, first01, c, d;
  if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
    first0 = a_b[0];
    first1 = a_b[1];
    a = first0;
    b = first1;
    if (globalThis.Array.isArray(c_d) && c_d.length === 2) {
      first01 = c_d[0];
      first11 = c_d[1];
      c = first01;
      d = first11;
      return [
        a,
        b,
        c,
        d
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
grid = function grid(m, n, segments, a, b, c) {
  let lscomp;
  lscomp = function lscomp(ls1) {
    let param0, param1, first3, first2, first1, first0, x0, y0, x1, y1, t1, tmp121, tmp122, tmp123, tmp124, tmp125, tmp126, tmp127, tmp128, tmp129, tmp130;
    if (ls1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls1 instanceof NofibPrelude.Cons.class) {
      param0 = ls1.head;
      param1 = ls1.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 4) {
        first0 = param0[0];
        first1 = param0[1];
        first2 = param0[2];
        first3 = param0[3];
        x0 = first0;
        y0 = first1;
        x1 = first2;
        y1 = first3;
        t1 = param1;
        tmp121 = scale_vec2(b, x0, m);
        tmp122 = vec_add(a, tmp121);
        tmp123 = scale_vec2(c, y0, n);
        tmp124 = vec_add(tmp122, tmp123);
        tmp125 = scale_vec2(b, x1, m);
        tmp126 = vec_add(a, tmp125);
        tmp127 = scale_vec2(c, y1, n);
        tmp128 = vec_add(tmp126, tmp127);
        tmp129 = tup2(tmp124, tmp128);
        tmp130 = lscomp(t1);
        return NofibPrelude.Cons(tmp129, tmp130)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  return lscomp(segments)
};
rot = function rot(p1, a, b, c) {
  let tmp121, tmp122;
  tmp121 = vec_add(a, b);
  tmp122 = vec_sub([
    0,
    0
  ], b);
  return runtime.safeCall(p1(tmp121, c, tmp122))
};
beside = function beside(m, n, p1, q1, a, b, c) {
  let tmp121, tmp122, tmp123, tmp124, tmp125, tmp126, tmp127, tmp128, tmp129;
  tmp121 = m + n;
  tmp122 = scale_vec2(b, m, tmp121);
  tmp123 = runtime.safeCall(p1(a, tmp122, c));
  tmp124 = m + n;
  tmp125 = scale_vec2(b, m, tmp124);
  tmp126 = vec_add(a, tmp125);
  tmp127 = n + m;
  tmp128 = scale_vec2(b, n, tmp127);
  tmp129 = runtime.safeCall(q1(tmp126, tmp128, c));
  return NofibPrelude.append(tmp123, tmp129)
};
above = function above(m, n, p1, q1, a, b, c) {
  let tmp121, tmp122, tmp123, tmp124, tmp125, tmp126, tmp127, tmp128, tmp129;
  tmp121 = m + n;
  tmp122 = scale_vec2(c, n, tmp121);
  tmp123 = vec_add(a, tmp122);
  tmp124 = n + m;
  tmp125 = scale_vec2(c, m, tmp124);
  tmp126 = runtime.safeCall(p1(tmp123, b, tmp125));
  tmp127 = m + n;
  tmp128 = scale_vec2(c, n, tmp127);
  tmp129 = runtime.safeCall(q1(a, b, tmp128));
  return NofibPrelude.append(tmp126, tmp129)
};
tile_to_grid = function tile_to_grid(arg, arg2, arg3, arg4) {
  return grid(16, 16, arg, arg2, arg3, arg4)
};
p = function p(arg, q6, q7) {
  return tile_to_grid(p_tile, arg, q6, q7)
};
q = function q(arg, q6, q7) {
  return tile_to_grid(q_tile, arg, q6, q7)
};
r = function r(arg, q6, q7) {
  return tile_to_grid(r_tile, arg, q6, q7)
};
s = function s(arg, q6, q7) {
  return tile_to_grid(s_tile, arg, q6, q7)
};
quartet = function quartet(a, b, c, d, arg, a6, a7) {
  let lambda1, lambda2;
  lambda1 = (undefined, function (p5, p6, p7) {
    return beside(1, 1, a, b, p5, p6, p7)
  });
  lambda2 = (undefined, function (p5, p6, p7) {
    return beside(1, 1, c, d, p5, p6, p7)
  });
  return above(1, 1, lambda1, lambda2, arg, a6, a7)
};
t = function t(arg, q6, q7) {
  return quartet(p, q, r, s, arg, q6, q7)
};
cycle_ = function cycle_(p1, arg, p3, p4) {
  let lambda1, lambda2, lambda3;
  lambda1 = (undefined, function (a, b, c) {
    let lambda4;
    lambda4 = (undefined, function (a1, b1, c1) {
      let lambda5;
      lambda5 = (undefined, function (a2, b2, c2) {
        return rot(p1, a2, b2, c2)
      });
      return rot(lambda5, a1, b1, c1)
    });
    return rot(lambda4, a, b, c)
  });
  lambda2 = (undefined, function (a, b, c) {
    return rot(p1, a, b, c)
  });
  lambda3 = (undefined, function (a, b, c) {
    let lambda4;
    lambda4 = (undefined, function (a1, b1, c1) {
      return rot(p1, a1, b1, c1)
    });
    return rot(lambda4, a, b, c)
  });
  return quartet(p1, lambda1, lambda2, lambda3, arg, p3, p4)
};
u = function u(arg, p2, p3) {
  let lambda1;
  lambda1 = (undefined, function (a, b, c) {
    return rot(q, a, b, c)
  });
  return cycle_(lambda1, arg, p2, p3)
};
side1 = function side1(arg, q6, q7) {
  let lambda1;
  lambda1 = (undefined, function (a, b, c) {
    return rot(t, a, b, c)
  });
  return quartet(nil, nil, lambda1, t, arg, q6, q7)
};
side2 = function side2(arg, q6, q7) {
  let lambda1;
  lambda1 = (undefined, function (a, b, c) {
    return rot(t, a, b, c)
  });
  return quartet(side1, side1, lambda1, t, arg, q6, q7)
};
corner1 = function corner1(arg, q6, q7) {
  return quartet(nil, nil, nil, u, arg, q6, q7)
};
corner2 = function corner2(arg, q6, q7) {
  let lambda1;
  lambda1 = (undefined, function (a, b, c) {
    return rot(side1, a, b, c)
  });
  return quartet(corner1, side1, lambda1, u, arg, q6, q7)
};
pseudocorner = function pseudocorner(arg, q6, q7) {
  let lambda1, lambda2;
  lambda1 = (undefined, function (a, b, c) {
    return rot(side2, a, b, c)
  });
  lambda2 = (undefined, function (a, b, c) {
    return rot(t, a, b, c)
  });
  return quartet(corner2, side2, lambda1, lambda2, arg, q6, q7)
};
pseudolimit = function pseudolimit(arg, p2, p3) {
  return cycle_(pseudocorner, arg, p2, p3)
};
nonet = function nonet(p1, p2, p3, p4, p5, p6, p7, p8, p9, arg1, arg2) {
  let lambda1, lambda2;
  lambda1 = (undefined, function (b5, b6, b7) {
    let lambda3;
    lambda3 = (undefined, function (b51, b61, b71) {
      return beside(1, 1, p2, p3, b51, b61, b71)
    });
    return beside(1, 2, p1, lambda3, b5, b6, b7)
  });
  lambda2 = (undefined, function (a1, a2, a3) {
    let lambda3, lambda4;
    lambda3 = (undefined, function (b5, b6, b7) {
      let lambda5;
      lambda5 = (undefined, function (b51, b61, b71) {
        return beside(1, 1, p5, p6, b51, b61, b71)
      });
      return beside(1, 2, p4, lambda5, b5, b6, b7)
    });
    lambda4 = (undefined, function (b5, b6, b7) {
      let lambda5;
      lambda5 = (undefined, function (b51, b61, b71) {
        return beside(1, 1, p8, p9, b51, b61, b71)
      });
      return beside(1, 2, p7, lambda5, b5, b6, b7)
    });
    return above(1, 1, lambda3, lambda4, a1, a2, a3)
  });
  return above(1, 2, lambda1, lambda2, arg1, arg2)
};
showFourTupleofInt = function showFourTupleofInt(a_b_c_d) {
  let first3, first2, first1, first0, a, b, c, d, tmp121, tmp122, tmp123, tmp124, tmp125, tmp126, tmp127, tmp128, tmp129, tmp130, tmp131, tmp132, tmp133, tmp134, tmp135, tmp136, tmp137, tmp138;
  if (globalThis.Array.isArray(a_b_c_d) && a_b_c_d.length === 4) {
    first0 = a_b_c_d[0];
    first1 = a_b_c_d[1];
    first2 = a_b_c_d[2];
    first3 = a_b_c_d[3];
    a = first0;
    b = first1;
    c = first2;
    d = first3;
    tmp121 = NofibPrelude.nofibStringToList("(");
    tmp122 = NofibPrelude.stringOfInt(a);
    tmp123 = NofibPrelude.nofibStringToList(tmp122);
    tmp124 = NofibPrelude.nofibStringToList(",");
    tmp125 = NofibPrelude.stringOfInt(b);
    tmp126 = NofibPrelude.nofibStringToList(tmp125);
    tmp127 = NofibPrelude.nofibStringToList(",");
    tmp128 = NofibPrelude.stringOfInt(c);
    tmp129 = NofibPrelude.nofibStringToList(tmp128);
    tmp130 = NofibPrelude.nofibStringToList(",");
    tmp131 = NofibPrelude.stringOfInt(d);
    tmp132 = NofibPrelude.nofibStringToList(tmp131);
    tmp133 = NofibPrelude.append(tmp130, tmp132);
    tmp134 = NofibPrelude.append(tmp129, tmp133);
    tmp135 = NofibPrelude.append(tmp127, tmp134);
    tmp136 = NofibPrelude.append(tmp126, tmp135);
    tmp137 = NofibPrelude.append(tmp124, tmp136);
    tmp138 = NofibPrelude.append(tmp123, tmp137);
    return NofibPrelude.append(tmp121, tmp138)
  } else {
    throw new globalThis.Error("match error");
  }
};
fmt = function fmt(ls1) {
  let showl, param0, param1, x, xs, tmp121, tmp122, tmp123, tmp124;
  if (ls1 instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.nofibStringToList("[]")
  } else if (ls1 instanceof NofibPrelude.Cons.class) {
    param0 = ls1.head;
    param1 = ls1.tail;
    x = param0;
    xs = param1;
    showl = function showl(ls2, s1) {
      let param01, param11, x1, xs1, tmp125, tmp126, tmp127, tmp128;
      if (ls2 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Cons("]", s1)
      } else if (ls2 instanceof NofibPrelude.Cons.class) {
        param01 = ls2.head;
        param11 = ls2.tail;
        x1 = param01;
        xs1 = param11;
        tmp125 = NofibPrelude.nofibStringToList(",|");
        tmp126 = showFourTupleofInt(x1);
        tmp127 = showl(xs1, s1);
        tmp128 = NofibPrelude.append(tmp126, tmp127);
        return NofibPrelude.append(tmp125, tmp128)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp121 = NofibPrelude.nofibStringToList("[|");
    tmp122 = showFourTupleofInt(x);
    tmp123 = showl(xs, "");
    tmp124 = NofibPrelude.append(tmp122, tmp123);
    return NofibPrelude.append(tmp121, tmp124)
  } else {
    throw new globalThis.Error("match error");
  }
};
testFish_nofib = function testFish_nofib(n) {
  let tmp121, tmp122, lambda1;
  lambda1 = (undefined, function (i) {
    let n1, tmp123, tmp124, tmp125;
    tmp123 = NofibPrelude.min(0, i);
    n1 = tmp123;
    tmp124 = 640 + n1;
    tmp125 = 640 + n1;
    return pseudolimit([
      0,
      0
    ], [
      tmp124,
      0
    ], [
      0,
      tmp125
    ])
  });
  tmp121 = lambda1;
  tmp122 = NofibPrelude.enumFromTo(0, n);
  return NofibPrelude.map(tmp121, tmp122)
};
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
p_tile = tmp29;
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
q_tile = tmp66;
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
r_tile = tmp91;
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
s_tile = tmp119;
tmp120 = testFish_nofib(1);
ls = tmp120;
lambda = (undefined, function () {
  return ls
});
BenchmarkPrelude.benchmark(lambda)