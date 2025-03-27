import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let go, life1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda$, lambda$1, lambda$2, lambda$3, lambda$4, lambda$5, lambda$6;
lambda7 = (undefined, function (i) {
  let tmp;
  tmp = NofibPrelude.stringOfInt(i);
  return NofibPrelude.nofibStringToList(tmp)
});
lambda$6 = function lambda$(sz, l) {
  let tmp, tmp1;
  tmp = life1.copy_lz(sz, 0);
  tmp1 = life1.append_lz_lz(l, tmp);
  return NofibPrelude.take_lz(sz, tmp1)
};
lambda8 = (undefined, function (sz) {
  return (l) => {
    return lambda$6(sz, l)
  }
});
lambda$5 = function lambda$(sz, b) {
  return life1.gen(sz, b)
};
lambda9 = (undefined, function (sz) {
  return (b) => {
    return lambda$5(sz, b)
  }
});
lambda5 = (undefined, function (x) {
  let tmp;
  tmp = NofibPrelude.map(life1.star, x);
  return NofibPrelude.concat(tmp)
});
lambda6 = (undefined, function (a, b) {
  let tmp;
  tmp = NofibPrelude.Cons("n", NofibPrelude.Nil);
  return life1.glue(tmp, a, b)
});
lambda$4 = function lambda$(genn, xss) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.nofibStringToList("nn");
  tmp1 = NofibPrelude.map(lambda5, xss);
  tmp2 = NofibPrelude.foldr(lambda6, NofibPrelude.Nil, tmp1);
  tmp3 = NofibPrelude.append(tmp, tmp2);
  return NofibPrelude.append(genn, tmp3)
};
lambda4 = (undefined, function (genn, xss) {
  return () => {
    return lambda$4(genn, xss)
  }
});
lambda$3 = function lambda$(y, xs) {
  return NofibPrelude.LzCons(y, xs)
};
lambda3 = (undefined, function (y, xs) {
  return () => {
    return lambda$3(y, xs)
  }
});
lambda$2 = function lambda$(ls) {
  let param0, param1, a, t, tmp;
  if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    a = param0;
    t = param1;
    tmp = life1.lzfy(t);
    return NofibPrelude.LzCons(a, tmp)
  } else {
    return NofibPrelude.LzNil
  }
};
lambda2 = (undefined, function (ls) {
  return () => {
    return lambda$2(ls)
  }
});
lambda$1 = function lambda$(xs, ys) {
  let scrut, param0, param1, h, t, tmp;
  scrut = NofibPrelude.force(xs);
  if (scrut instanceof NofibPrelude.LzNil.class) {
    return NofibPrelude.force(ys)
  } else if (scrut instanceof NofibPrelude.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    h = param0;
    t = param1;
    tmp = life1.append_lz_lz(t, ys);
    return NofibPrelude.LzCons(h, tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda1 = (undefined, function (xs, ys) {
  return () => {
    return lambda$1(xs, ys)
  }
});
lambda$ = function lambda$(n, x) {
  let scrut, tmp, tmp1;
  scrut = n === 0;
  if (scrut === true) {
    return NofibPrelude.LzNil
  } else {
    tmp = n - 1;
    tmp1 = life1.copy_lz(tmp, x);
    return NofibPrelude.LzCons(x, tmp1)
  }
};
lambda = (undefined, function (n, x) {
  return () => {
    return lambda$(n, x)
  }
});
go = function go(h, t) {
  let param0, param1, head, t1;
  if (t instanceof NofibPrelude.Nil.class) {
    return h
  } else if (t instanceof NofibPrelude.Cons.class) {
    param0 = t.head;
    param1 = t.tail;
    head = param0;
    t1 = param1;
    return go(head, t1)
  } else {
    throw new globalThis.Error("match error");
  }
};
life1 = class life {
  static {
    life1 = life;
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, lambda10, lambda11, lambda12, lambda13, lambda14, lambda15, lambda16, lambda17, lambda18, lambda19, lambda20, lambda21, lambda22, lambda23, lambda24;
    lambda10 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp = NofibPrelude.lazy(lambda10);
    lambda11 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp1 = NofibPrelude.lazy(lambda11);
    lambda12 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp2 = NofibPrelude.lazy(lambda12);
    lambda13 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp3 = NofibPrelude.lazy(lambda13);
    lambda14 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp4 = NofibPrelude.lazy(lambda14);
    lambda15 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp5 = NofibPrelude.lazy(lambda15);
    lambda16 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp6 = NofibPrelude.lazy(lambda16);
    lambda17 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp7 = NofibPrelude.lazy(lambda17);
    lambda18 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp8 = NofibPrelude.lazy(lambda18);
    lambda19 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp9 = NofibPrelude.lazy(lambda19);
    lambda20 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp10 = NofibPrelude.lazy(lambda20);
    lambda21 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp11 = NofibPrelude.lazy(lambda21);
    lambda22 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp12 = NofibPrelude.lazy(lambda22);
    lambda23 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    tmp13 = NofibPrelude.lazy(lambda23);
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
    tmp41 = life.lzfy(tmp40);
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
    this.start = tmp56;
    lambda24 = (undefined, function () {
      return life.testLife_nofib(15)
    });
    BenchmarkPrelude.benchmark(lambda24)
  }
  static last(a_t) {
    let param0, param1, a, t;
    if (a_t instanceof NofibPrelude.Cons.class) {
      param0 = a_t.head;
      param1 = a_t.tail;
      a = param0;
      t = param1;
      return go(a, t)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static copy_lz(n, x) {
    let tmp;
    tmp = runtime.safeCall(lambda(n, x));
    return NofibPrelude.lazy(tmp)
  } 
  static append_lz_lz(xs, ys) {
    let tmp;
    tmp = runtime.safeCall(lambda1(xs, ys));
    return NofibPrelude.lazy(tmp)
  } 
  static init(ls) {
    let param0, param1, a, t, a1, tmp;
    if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      a1 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else {
        a = param0;
        t = param1;
        tmp = life.init(t);
        return NofibPrelude.Cons(a, tmp)
      }
    } else {
      throw globalThis.Error(ls);
    }
  } 
  static zipWith3(f, xs1, ys1, zs) {
    let param0, param1, hx, tx, param01, param11, hy, ty, param02, param12, hz, tz, tmp, tmp1;
    if (xs1 instanceof NofibPrelude.Cons.class) {
      param0 = xs1.head;
      param1 = xs1.tail;
      hx = param0;
      tx = param1;
      if (ys1 instanceof NofibPrelude.Cons.class) {
        param01 = ys1.head;
        param11 = ys1.tail;
        hy = param01;
        ty = param11;
        if (zs instanceof NofibPrelude.Cons.class) {
          param02 = zs.head;
          param12 = zs.tail;
          hz = param02;
          tz = param12;
          tmp = runtime.safeCall(f(hx, hy, hz));
          tmp1 = life.zipWith3(f, tx, ty, tz);
          return NofibPrelude.Cons(tmp, tmp1)
        } else {
          return NofibPrelude.Nil
        }
      } else {
        return NofibPrelude.Nil
      }
    } else {
      return NofibPrelude.Nil
    }
  } 
  static zip3(xs2, ys2, zs1) {
    let param0, param1, hx, tx, param01, param11, hy, ty, param02, param12, hz, tz, tmp;
    if (xs2 instanceof NofibPrelude.Cons.class) {
      param0 = xs2.head;
      param1 = xs2.tail;
      hx = param0;
      tx = param1;
      if (ys2 instanceof NofibPrelude.Cons.class) {
        param01 = ys2.head;
        param11 = ys2.tail;
        hy = param01;
        ty = param11;
        if (zs1 instanceof NofibPrelude.Cons.class) {
          param02 = zs1.head;
          param12 = zs1.tail;
          hz = param02;
          tz = param12;
          tmp = life.zip3(tx, ty, tz);
          return NofibPrelude.Cons([
            hx,
            hy,
            hz
          ], tmp)
        } else {
          return NofibPrelude.Nil
        }
      } else {
        return NofibPrelude.Nil
      }
    } else {
      return NofibPrelude.Nil
    }
  } 
  static lzfy(ls1) {
    let tmp;
    tmp = runtime.safeCall(lambda2(ls1));
    return NofibPrelude.lazy(tmp)
  } 
  static elt(a_b_c, d_e_f, g_h_i) {
    let first2, first1, first0, a, b, c, first21, first11, first01, d, e, f1, first22, first12, first02, g, h, i, tot, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
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
        f1 = first21;
        if (globalThis.Array.isArray(g_h_i) && g_h_i.length === 3) {
          first02 = g_h_i[0];
          first12 = g_h_i[1];
          first22 = g_h_i[2];
          g = first02;
          h = first12;
          i = first22;
          tmp = a + b;
          tmp1 = tmp + c;
          tmp2 = tmp1 + d;
          tmp3 = tmp2 + f1;
          tmp4 = tmp3 + g;
          tmp5 = tmp4 + h;
          tmp6 = tmp5 + i;
          tot = tmp6;
          tmp7 = tot < 2;
          tmp8 = tot > 3;
          scrut1 = tmp7 || tmp8;
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
  } 
  static shiftr(x1, xs3) {
    let tmp;
    tmp = life.init(xs3);
    return NofibPrelude.Cons(x1, tmp)
  } 
  static shiftl(x2, xs4) {
    let tmp, tmp1;
    tmp = life.init(xs4);
    tmp1 = NofibPrelude.Cons(x2, NofibPrelude.Nil);
    return NofibPrelude.append(tmp, tmp1)
  } 
  static shift(x3, xs5) {
    let tmp, tmp1;
    tmp = life.shiftr(x3, xs5);
    tmp1 = life.shiftl(x3, xs5);
    return life.zip3(tmp, xs5, tmp1)
  } 
  static row(last_this_next) {
    let first2, first1, first0, last, this_, next, tmp, tmp1, tmp2;
    if (globalThis.Array.isArray(last_this_next) && last_this_next.length === 3) {
      first0 = last_this_next[0];
      first1 = last_this_next[1];
      first2 = last_this_next[2];
      last = first0;
      this_ = first1;
      next = first2;
      tmp = life.shift(0, last);
      tmp1 = life.shift(0, this_);
      tmp2 = life.shift(0, next);
      return life.zipWith3(life.elt, tmp, tmp1, tmp2)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static gen(n1, board) {
    let tmp, tmp1;
    tmp = NofibPrelude.replicate(n1, 0);
    tmp1 = life.shift(tmp, board);
    return NofibPrelude.map(life.row, tmp1)
  } 
  static star(x4) {
    let scrut, scrut1;
    scrut1 = x4 === 0;
    if (scrut1 === true) {
      return NofibPrelude.nofibStringToList("  ")
    } else {
      scrut = x4 === 1;
      if (scrut === true) {
        return NofibPrelude.nofibStringToList(" o")
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  static glue(s, xs6, ys3) {
    let tmp;
    tmp = NofibPrelude.append(s, ys3);
    return NofibPrelude.append(xs6, tmp)
  } 
  static limit(ls2) {
    let scrut, param0, param1, x5, ys4, scrut1, param01, param11, y, xs7, scrut2, tmp, tmp1, lambda$this;
    scrut = NofibPrelude.force(ls2);
    if (scrut instanceof NofibPrelude.LzCons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      x5 = param0;
      ys4 = param1;
      scrut1 = NofibPrelude.force(ys4);
      if (scrut1 instanceof NofibPrelude.LzCons.class) {
        param01 = scrut1.head;
        param11 = scrut1.tail;
        y = param01;
        xs7 = param11;
        scrut2 = NofibPrelude.listEqBy(NofibPrelude.listEq, x5, y);
        if (scrut2 === true) {
          return NofibPrelude.Cons(x5, NofibPrelude.Nil)
        } else {
          lambda$this = runtime.safeCall(lambda3(y, xs7));
          tmp = NofibPrelude.lazy(lambda$this);
          tmp1 = life.limit(tmp);
          return NofibPrelude.Cons(x5, tmp1)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static disp(gen_xss) {
    let first1, first0, genn, xss, tmp;
    if (globalThis.Array.isArray(gen_xss) && gen_xss.length === 2) {
      first0 = gen_xss[0];
      first1 = gen_xss[1];
      genn = first0;
      xss = first1;
      tmp = runtime.safeCall(lambda4(genn, xss));
      return NofibPrelude.lazy(tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static generations(sz) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, lambda$this;
    tmp = NofibPrelude.enumFrom(0);
    tmp1 = NofibPrelude.map_lz(lambda7, tmp);
    tmp2 = runtime.safeCall(lambda8(sz));
    tmp3 = life.copy_lz(sz, 0);
    tmp4 = life.copy_lz(sz, tmp3);
    tmp5 = NofibPrelude.append_nl_lz(life.start, tmp4);
    tmp6 = NofibPrelude.map_lz(tmp2, tmp5);
    tmp7 = NofibPrelude.take_lz(sz, tmp6);
    lambda$this = runtime.safeCall(lambda9(sz));
    tmp8 = NofibPrelude.iterate(lambda$this, tmp7);
    tmp9 = life.limit(tmp8);
    tmp10 = NofibPrelude.zip_lz_nl(tmp1, tmp9);
    return NofibPrelude.map(life.disp, tmp10)
  } 
  static testLife_nofib(n2) {
    let tmp, tmp1, tmp2;
    tmp = life.generations(n2);
    tmp1 = life.last(tmp);
    tmp2 = NofibPrelude.force(tmp1);
    return NofibPrelude.listLen(tmp2)
  }
  static toString() { return "life"; }
};
let life = life1; export default life;
