import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let elt, shiftr, testLife_nofib, shift, last, copy_lz, zip3, disp, shiftl, gen, glue, zipWith3, star, row, generations, append_lz_lz, init, lzfy, limit, start, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda14;
last = function last(a_t) {
  let go, param0, param1, a, t;
  go = function go(h, t1) {
    let param01, param11, head, t2;
    if (t1 instanceof NofibPrelude.Nil.class) {
      return h
    } else if (t1 instanceof NofibPrelude.Cons.class) {
      param01 = t1.head;
      param11 = t1.tail;
      head = param01;
      t2 = param11;
      return go(head, t2)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  if (a_t instanceof NofibPrelude.Cons.class) {
    param0 = a_t.head;
    param1 = a_t.tail;
    a = param0;
    t = param1;
    return go(a, t)
  } else {
    throw new globalThis.Error("match error");
  }
};
copy_lz = function copy_lz(n, x) {
  let tmp57, lambda15;
  lambda15 = (undefined, function () {
    let scrut, tmp58, tmp59;
    scrut = n === 0;
    if (scrut === true) {
      return NofibPrelude.LzNil
    } else {
      tmp58 = n - 1;
      tmp59 = copy_lz(tmp58, x);
      return NofibPrelude.LzCons(x, tmp59)
    }
  });
  tmp57 = lambda15;
  return NofibPrelude.lazy(tmp57)
};
append_lz_lz = function append_lz_lz(xs, ys) {
  let tmp57, lambda15;
  lambda15 = (undefined, function () {
    let scrut, param0, param1, h, t, tmp58;
    scrut = NofibPrelude.force(xs);
    if (scrut instanceof NofibPrelude.LzNil.class) {
      return NofibPrelude.force(ys)
    } else if (scrut instanceof NofibPrelude.LzCons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      h = param0;
      t = param1;
      tmp58 = NofibPrelude.append_lz_lz(t, ys);
      return NofibPrelude.LzCons(h, tmp58)
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp57 = lambda15;
  return NofibPrelude.lazy(tmp57)
};
init = function init(ls) {
  let param0, param1, a, t, a1, tmp57;
  if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    a1 = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      a = param0;
      t = param1;
      tmp57 = init(t);
      return NofibPrelude.Cons(a, tmp57)
    }
  } else {
    throw globalThis.Error(ls);
  }
};
zipWith3 = function zipWith3(f, xs, ys, zs) {
  let param0, param1, hx, tx, param01, param11, hy, ty, param02, param12, hz, tz, tmp57, tmp58;
  if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    hx = param0;
    tx = param1;
    if (ys instanceof NofibPrelude.Cons.class) {
      param01 = ys.head;
      param11 = ys.tail;
      hy = param01;
      ty = param11;
      if (zs instanceof NofibPrelude.Cons.class) {
        param02 = zs.head;
        param12 = zs.tail;
        hz = param02;
        tz = param12;
        tmp57 = runtime.safeCall(f(hx, hy, hz));
        tmp58 = zipWith3(f, tx, ty, tz);
        return NofibPrelude.Cons(tmp57, tmp58)
      } else {
        return NofibPrelude.Nil
      }
    } else {
      return NofibPrelude.Nil
    }
  } else {
    return NofibPrelude.Nil
  }
};
zip3 = function zip3(xs, ys, zs) {
  let param0, param1, hx, tx, param01, param11, hy, ty, param02, param12, hz, tz, tmp57;
  if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    hx = param0;
    tx = param1;
    if (ys instanceof NofibPrelude.Cons.class) {
      param01 = ys.head;
      param11 = ys.tail;
      hy = param01;
      ty = param11;
      if (zs instanceof NofibPrelude.Cons.class) {
        param02 = zs.head;
        param12 = zs.tail;
        hz = param02;
        tz = param12;
        tmp57 = NofibPrelude.zip3(tx, ty, tz);
        return NofibPrelude.Cons([
          hx,
          hy,
          hz
        ], tmp57)
      } else {
        return NofibPrelude.Nil
      }
    } else {
      return NofibPrelude.Nil
    }
  } else {
    return NofibPrelude.Nil
  }
};
lzfy = function lzfy(ls) {
  let tmp57, lambda15;
  lambda15 = (undefined, function () {
    let param0, param1, a, t, tmp58;
    if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      a = param0;
      t = param1;
      tmp58 = lzfy(t);
      return NofibPrelude.LzCons(a, tmp58)
    } else {
      return NofibPrelude.LzNil
    }
  });
  tmp57 = lambda15;
  return NofibPrelude.lazy(tmp57)
};
elt = function elt(a_b_c, d_e_f, g_h_i) {
  let first2, first1, first0, a, b, c, first21, first11, first01, d, e, f, first22, first12, first02, g, h, i, tot, scrut, scrut1, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65;
  if (globalThis.Array.isArray(a_b_c) && a_b_c.length === 3) {
    first0 = a_b_c[0];
    first1 = a_b_c[1];
    first2 = a_b_c[2];
    a = first0;
    b = first1;
    c = first2;
    if (globalThis.Array.isArray(d_e_f) && d_e_f.length === 3) {
      first01 = d_e_f[0];
      first11 = d_e_f[1];
      first21 = d_e_f[2];
      d = first01;
      e = first11;
      f = first21;
      if (globalThis.Array.isArray(g_h_i) && g_h_i.length === 3) {
        first02 = g_h_i[0];
        first12 = g_h_i[1];
        first22 = g_h_i[2];
        g = first02;
        h = first12;
        i = first22;
        tmp57 = a + b;
        tmp58 = tmp57 + c;
        tmp59 = tmp58 + d;
        tmp60 = tmp59 + f;
        tmp61 = tmp60 + g;
        tmp62 = tmp61 + h;
        tmp63 = tmp62 + i;
        tot = tmp63;
        tmp64 = tot < 2;
        tmp65 = tot > 3;
        scrut1 = tmp64 || tmp65;
        if (scrut1 === true) {
          return 0
        } else {
          scrut = tot === 3;
          if (scrut === true) {
            return 1
          } else {
            return e
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
};
shiftr = function shiftr(x, xs) {
  let tmp57;
  tmp57 = init(xs);
  return NofibPrelude.Cons(x, tmp57)
};
shiftl = function shiftl(x, xs) {
  let tmp57, tmp58;
  tmp57 = init(xs);
  tmp58 = NofibPrelude.Cons(x, NofibPrelude.Nil);
  return NofibPrelude.append(tmp57, tmp58)
};
shift = function shift(x, xs) {
  let tmp57, tmp58;
  tmp57 = shiftr(x, xs);
  tmp58 = shiftl(x, xs);
  return NofibPrelude.zip3(tmp57, xs, tmp58)
};
row = function row(last_this_next) {
  let first2, first1, first0, last1, this_, next, tmp57, tmp58, tmp59;
  if (globalThis.Array.isArray(last_this_next) && last_this_next.length === 3) {
    first0 = last_this_next[0];
    first1 = last_this_next[1];
    first2 = last_this_next[2];
    last1 = first0;
    this_ = first1;
    next = first2;
    tmp57 = shift(0, last1);
    tmp58 = shift(0, this_);
    tmp59 = shift(0, next);
    return zipWith3(elt, tmp57, tmp58, tmp59)
  } else {
    throw new globalThis.Error("match error");
  }
};
gen = function gen(n, board) {
  let tmp57, tmp58;
  tmp57 = NofibPrelude.replicate(n, 0);
  tmp58 = shift(tmp57, board);
  return NofibPrelude.map(row, tmp58)
};
star = function star(x) {
  let scrut, scrut1;
  scrut1 = x === 0;
  if (scrut1 === true) {
    return NofibPrelude.nofibStringToList("  ")
  } else {
    scrut = x === 1;
    if (scrut === true) {
      return NofibPrelude.nofibStringToList(" o")
    } else {
      throw new globalThis.Error("match error");
    }
  }
};
glue = function glue(s, xs, ys) {
  let tmp57;
  tmp57 = NofibPrelude.append(s, ys);
  return NofibPrelude.append(xs, tmp57)
};
limit = function limit(ls) {
  let scrut, param0, param1, x, ys, scrut1, param01, param11, y, xs, scrut2, tmp57, tmp58, lambda15;
  scrut = NofibPrelude.force(ls);
  if (scrut instanceof NofibPrelude.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    x = param0;
    ys = param1;
    scrut1 = NofibPrelude.force(ys);
    if (scrut1 instanceof NofibPrelude.LzCons.class) {
      param01 = scrut1.head;
      param11 = scrut1.tail;
      y = param01;
      xs = param11;
      scrut2 = NofibPrelude.listEqBy(NofibPrelude.listEq, x, y);
      if (scrut2 === true) {
        return NofibPrelude.Cons(x, NofibPrelude.Nil)
      } else {
        lambda15 = (undefined, function () {
          return NofibPrelude.LzCons(y, xs)
        });
        tmp57 = NofibPrelude.lazy(lambda15);
        tmp58 = limit(tmp57);
        return NofibPrelude.Cons(x, tmp58)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
disp = function disp(gen_xss) {
  let first1, first0, genn, xss, tmp57, lambda15;
  if (globalThis.Array.isArray(gen_xss) && gen_xss.length === 2) {
    first0 = gen_xss[0];
    first1 = gen_xss[1];
    genn = first0;
    xss = first1;
    lambda15 = (undefined, function () {
      let tmp58, tmp59, tmp60, tmp61, lambda16, lambda17;
      tmp58 = NofibPrelude.nofibStringToList("nn");
      lambda16 = (undefined, function (x) {
        let tmp62;
        tmp62 = NofibPrelude.map(star, x);
        return NofibPrelude.concat(tmp62)
      });
      tmp59 = NofibPrelude.map(lambda16, xss);
      lambda17 = (undefined, function (a, b) {
        let tmp62;
        tmp62 = NofibPrelude.Cons("n", NofibPrelude.Nil);
        return glue(tmp62, a, b)
      });
      tmp60 = NofibPrelude.foldr(lambda17, NofibPrelude.Nil, tmp59);
      tmp61 = NofibPrelude.append(tmp58, tmp60);
      return NofibPrelude.append(genn, tmp61)
    });
    tmp57 = lambda15;
    return NofibPrelude.lazy(tmp57)
  } else {
    throw new globalThis.Error("match error");
  }
};
generations = function generations(sz) {
  let tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, lambda15, lambda16, lambda17;
  tmp57 = NofibPrelude.enumFrom(0);
  lambda15 = (undefined, function (i) {
    let tmp68;
    tmp68 = NofibPrelude.stringOfInt(i);
    return NofibPrelude.nofibStringToList(tmp68)
  });
  tmp58 = NofibPrelude.map_lz(lambda15, tmp57);
  lambda16 = (undefined, function (l) {
    let tmp68, tmp69;
    tmp68 = copy_lz(sz, 0);
    tmp69 = NofibPrelude.append_lz_lz(l, tmp68);
    return NofibPrelude.take_lz(sz, tmp69)
  });
  tmp59 = lambda16;
  tmp60 = copy_lz(sz, 0);
  tmp61 = copy_lz(sz, tmp60);
  tmp62 = NofibPrelude.append_nl_lz(start, tmp61);
  tmp63 = NofibPrelude.map_lz(tmp59, tmp62);
  tmp64 = NofibPrelude.take_lz(sz, tmp63);
  lambda17 = (undefined, function (b) {
    return gen(sz, b)
  });
  tmp65 = NofibPrelude.iterate(lambda17, tmp64);
  tmp66 = limit(tmp65);
  tmp67 = NofibPrelude.zip_lz_nl(tmp58, tmp66);
  return NofibPrelude.map(disp, tmp67)
};
testLife_nofib = function testLife_nofib(n) {
  let tmp57, tmp58, tmp59;
  tmp57 = generations(n);
  tmp58 = last(tmp57);
  tmp59 = NofibPrelude.force(tmp58);
  return NofibPrelude.listLen(tmp59)
};
lambda = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp = NofibPrelude.lazy(lambda);
lambda1 = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp1 = NofibPrelude.lazy(lambda1);
lambda2 = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp2 = NofibPrelude.lazy(lambda2);
lambda3 = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp3 = NofibPrelude.lazy(lambda3);
lambda4 = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp4 = NofibPrelude.lazy(lambda4);
lambda5 = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp5 = NofibPrelude.lazy(lambda5);
lambda6 = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp6 = NofibPrelude.lazy(lambda6);
lambda7 = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp7 = NofibPrelude.lazy(lambda7);
lambda8 = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp8 = NofibPrelude.lazy(lambda8);
lambda9 = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp9 = NofibPrelude.lazy(lambda9);
lambda10 = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp10 = NofibPrelude.lazy(lambda10);
lambda11 = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp11 = NofibPrelude.lazy(lambda11);
lambda12 = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp12 = NofibPrelude.lazy(lambda12);
lambda13 = (undefined, function () {
  return NofibPrelude.LzNil
});
tmp13 = NofibPrelude.lazy(lambda13);
tmp14 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp15 = NofibPrelude.Cons(1, tmp14);
tmp16 = NofibPrelude.Cons(1, tmp15);
tmp17 = NofibPrelude.Cons(1, tmp16);
tmp18 = NofibPrelude.Cons(1, tmp17);
tmp19 = NofibPrelude.Cons(1, tmp18);
tmp20 = NofibPrelude.Cons(0, tmp19);
tmp21 = NofibPrelude.Cons(1, tmp20);
tmp22 = NofibPrelude.Cons(1, tmp21);
tmp23 = NofibPrelude.Cons(1, tmp22);
tmp24 = NofibPrelude.Cons(1, tmp23);
tmp25 = NofibPrelude.Cons(1, tmp24);
tmp26 = NofibPrelude.Cons(0, tmp25);
tmp27 = NofibPrelude.Cons(1, tmp26);
tmp28 = NofibPrelude.Cons(1, tmp27);
tmp29 = NofibPrelude.Cons(1, tmp28);
tmp30 = NofibPrelude.Cons(1, tmp29);
tmp31 = NofibPrelude.Cons(1, tmp30);
tmp32 = NofibPrelude.Cons(0, tmp31);
tmp33 = NofibPrelude.Cons(1, tmp32);
tmp34 = NofibPrelude.Cons(1, tmp33);
tmp35 = NofibPrelude.Cons(1, tmp34);
tmp36 = NofibPrelude.Cons(1, tmp35);
tmp37 = NofibPrelude.Cons(1, tmp36);
tmp38 = NofibPrelude.Cons(0, tmp37);
tmp39 = NofibPrelude.Cons(0, tmp38);
tmp40 = NofibPrelude.Cons(0, tmp39);
tmp41 = lzfy(tmp40);
tmp42 = NofibPrelude.Cons(tmp41, NofibPrelude.Nil);
tmp43 = NofibPrelude.Cons(tmp13, tmp42);
tmp44 = NofibPrelude.Cons(tmp12, tmp43);
tmp45 = NofibPrelude.Cons(tmp11, tmp44);
tmp46 = NofibPrelude.Cons(tmp10, tmp45);
tmp47 = NofibPrelude.Cons(tmp9, tmp46);
tmp48 = NofibPrelude.Cons(tmp8, tmp47);
tmp49 = NofibPrelude.Cons(tmp7, tmp48);
tmp50 = NofibPrelude.Cons(tmp6, tmp49);
tmp51 = NofibPrelude.Cons(tmp5, tmp50);
tmp52 = NofibPrelude.Cons(tmp4, tmp51);
tmp53 = NofibPrelude.Cons(tmp3, tmp52);
tmp54 = NofibPrelude.Cons(tmp2, tmp53);
tmp55 = NofibPrelude.Cons(tmp1, tmp54);
tmp56 = NofibPrelude.Cons(tmp, tmp55);
start = tmp56;
lambda14 = (undefined, function () {
  return testLife_nofib(15)
});
BenchmarkPrelude.benchmark(lambda14)