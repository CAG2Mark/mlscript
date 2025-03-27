import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let go, plus, linc, plus1, start, breakk, unknownEq, bf, old_width_hd, width_hd, myAdd, single, trim, new_, cost, drop_nofit, para1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda14, lambda15, lambda16, lambda17, lambda18, lambda19, lambda$, lambda$1, lambda$2, lambda$3, lambda$4, lambda$5, lambda$6, lambda$7, lambda$8, myAdd$, bf$, drop_nofit$, trim$, new_$, old_width_hd$, cost$, width_hd$;
lambda19 = (undefined, function (x) {
  let tmp, tmp1;
  tmp = para1.fst3(x);
  tmp1 = para1.last_(tmp);
  return para1.len_tl(tmp1)
});
single = function single(p) {
  let tmp;
  tmp = para1.len_tl(p);
  return tmp === 0
};
width_hd$ = function width_hd$(tot_width, p) {
  let scrut, tmp, tmp1;
  scrut = single(p);
  if (scrut === true) {
    return tot_width
  } else {
    tmp = para1.width_tl(p);
    tmp1 = tot_width - tmp;
    return tmp1 - 1
  }
};
width_hd = function width_hd(tot_width) {
  return (p) => {
    return width_hd$(tot_width, p)
  }
};
cost$ = function cost$(tot_width, p) {
  let a, scrut, tmp, tmp1, tmp2, tmp3;
  scrut = single(p);
  if (scrut === true) {
    return 0
  } else {
    tmp = para1.cost_tl(p);
    tmp1 = width_hd$(tot_width, p);
    tmp2 = para1.optw - tmp1;
    a = tmp2;
    tmp3 = a * a;
    return tmp + tmp3
  }
};
cost = function cost(tot_width) {
  return (p) => {
    return cost$(tot_width, p)
  }
};
old_width_hd$ = function old_width_hd$(tw, p) {
  let scrut, tmp, tmp1;
  scrut = single(p);
  if (scrut === true) {
    return tw
  } else {
    tmp = para1.width_tl(p);
    tmp1 = tw - tmp;
    return tmp1 - 1
  }
};
old_width_hd = function old_width_hd(tw) {
  return (p) => {
    return old_width_hd$(tw, p)
  }
};
new_$ = function new_$(tw, tl, p) {
  let x, scrut, tmp, tmp1, tmp2, tmp3, tmp4;
  scrut = single(p);
  if (scrut === true) {
    return [
      tw,
      0,
      tl
    ]
  } else {
    tmp = para1.cost_tl(p);
    tmp1 = old_width_hd$(tw, p);
    tmp2 = para1.optw - tmp1;
    x = tmp2;
    tmp3 = x * x;
    tmp4 = tmp + tmp3;
    return [
      tw,
      tmp4,
      tl
    ]
  }
};
new_ = function new_(tw, tl) {
  return (p) => {
    return new_$(tw, tl, p)
  }
};
trim$ = function trim$(tot_width, ps_pq) {
  let ps_p, q, p, scrut, scrut1, scrut2, tmp, tmp1;
  scrut2 = para1.null__(ps_pq);
  if (scrut2 === true) {
    return ps_pq
  } else {
    scrut1 = para1.single_(ps_pq);
    if (scrut1 === true) {
      return ps_pq
    } else {
      ps_p = para1.init_(ps_pq);
      q = para1.last_(ps_pq);
      p = para1.last_(ps_p);
      tmp = cost$(tot_width, p);
      tmp1 = cost$(tot_width, q);
      scrut = tmp <= tmp1;
      if (scrut === true) {
        return trim$(tot_width, ps_p)
      } else {
        return ps_pq
      }
    }
  }
};
trim = function trim(tot_width) {
  return (ps_pq) => {
    return trim$(tot_width, ps_pq)
  }
};
drop_nofit$ = function drop_nofit$(tot_width, ps_p) {
  let scrut, scrut1, tmp, tmp1, tmp2;
  scrut1 = para1.null__(ps_p);
  if (scrut1 === true) {
    return ps_p
  } else {
    tmp = para1.last_(ps_p);
    tmp1 = width_hd$(tot_width, tmp);
    scrut = tmp1 > para1.maxw;
    if (scrut === true) {
      tmp2 = para1.init_(ps_p);
      return drop_nofit$(tot_width, tmp2)
    } else {
      return ps_p
    }
  }
};
drop_nofit = function drop_nofit(tot_width) {
  return (ps_p) => {
    return drop_nofit$(tot_width, ps_p)
  }
};
bf$ = function bf$(tot_width, p, q) {
  let wqh, rqh, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
  tmp = width_hd$(tot_width, q);
  wqh = tmp;
  tmp1 = para1.maxw - wqh;
  tmp2 = tmp1 + 1;
  rqh = tmp2;
  tmp3 = single(q);
  tmp4 = para1.cost_tl(p);
  tmp5 = tmp4 === 0;
  scrut1 = tmp3 && tmp5;
  if (scrut1 === true) {
    tmp6 = width_hd$(tot_width, p);
    tmp7 = para1.optw - tmp6;
    return NofibPrelude.min(tmp7, rqh)
  } else {
    scrut = single(q);
    if (scrut === true) {
      return rqh
    } else {
      tmp8 = cost$(tot_width, p);
      tmp9 = cost$(tot_width, q);
      tmp10 = tmp8 - tmp9;
      tmp11 = width_hd$(tot_width, p);
      tmp12 = wqh - tmp11;
      tmp13 = 2 * tmp12;
      tmp14 = para1.ceildiv(tmp10, tmp13);
      return NofibPrelude.min(tmp14, rqh)
    }
  }
};
bf = function bf(tot_width) {
  return (p, q) => {
    return bf$(tot_width, p, q)
  }
};
myAdd$ = function myAdd$(tot_width, p, qr_rs) {
  let q, r_rs, r, scrut, scrut1, tmp, tmp1, tmp2, tmp3;
  tmp = para1.single_(qr_rs);
  tmp1 = para1.null__(qr_rs);
  scrut1 = tmp || tmp1;
  if (scrut1 === true) {
    return para1.cons_(p, qr_rs)
  } else {
    q = para1.head_(qr_rs);
    r_rs = para1.tail_(qr_rs);
    r = para1.head_(r_rs);
    tmp2 = bf$(tot_width, p, q);
    tmp3 = bf$(tot_width, q, r);
    scrut = tmp2 <= tmp3;
    if (scrut === true) {
      return myAdd$(tot_width, p, r_rs)
    } else {
      return para1.cons_(p, qr_rs)
    }
  }
};
myAdd = function myAdd(tot_width) {
  return (p, qr_rs) => {
    return myAdd$(tot_width, p, qr_rs)
  }
};
lambda$8 = function lambda$(par, x) {
  let tmp;
  tmp = NofibPrelude.concat(x);
  return runtime.safeCall(par(tmp))
};
lambda18 = (undefined, function (par) {
  return (x) => {
    return lambda$8(par, x)
  }
});
lambda17 = (undefined, function (x) {
  return NofibPrelude.listNeq(NofibPrelude.Nil, x)
});
unknownEq = function unknownEq(a, b) {
  return a === b
};
breakk = function breakk(a, b, xs) {
  let scrut, tmp, tmp1, tmp2;
  scrut = unknownEq(a, b);
  if (scrut === true) {
    return NofibPrelude.Cons(NofibPrelude.Nil, xs)
  } else {
    tmp = NofibPrelude.head(xs);
    tmp1 = NofibPrelude.Cons(b, tmp);
    tmp2 = NofibPrelude.tail(xs);
    return NofibPrelude.Cons(tmp1, tmp2)
  }
};
start = function start(a, b) {
  let tmp;
  tmp = NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil);
  return breakk(a, b, tmp)
};
lambda$7 = function lambda$(a, x, y) {
  return breakk(a, x, y)
};
lambda15 = (undefined, function (a) {
  return (x, y) => {
    return lambda$7(a, x, y)
  }
});
lambda$6 = function lambda$(a, y) {
  return start(a, y)
};
lambda16 = (undefined, function (a) {
  return (y) => {
    return lambda$6(a, y)
  }
});
lambda$5 = function lambda$(a, xs, ys) {
  let tmp, tmp1;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = NofibPrelude.append(tmp, ys);
  return NofibPrelude.append(xs, tmp1)
};
lambda13 = (undefined, function (a) {
  return (xs, ys) => {
    return lambda$5(a, xs, ys)
  }
});
lambda14 = (undefined, function (x) {
  return x
});
linc = function linc(l) {
  let a, tmp, tmp1;
  tmp = para1.width(l);
  tmp1 = para1.optw - tmp;
  a = tmp1;
  return a * a
};
plus1 = function plus(l, n) {
  let tmp;
  tmp = linc(l);
  return tmp + n
};
lambda12 = (undefined, function (x) {
  return 0
});
plus = function plus(w, n) {
  let tmp, tmp1;
  tmp = NofibPrelude.listLen(w);
  tmp1 = tmp + 1;
  return tmp1 + n
};
lambda$4 = function lambda$(w, p) {
  return para1.new_(w, p)
};
lambda9 = (undefined, function (w) {
  return (p) => {
    return lambda$4(w, p)
  }
});
lambda$3 = function lambda$(w, p) {
  return para1.glue(w, p)
};
lambda10 = (undefined, function (w) {
  return (p) => {
    return lambda$3(w, p)
  }
});
lambda8 = (undefined, function (w, ps) {
  let tmp, tmp1, lambda$this, lambda$this1;
  lambda$this = runtime.safeCall(lambda9(w));
  tmp = NofibPrelude.map(lambda$this, ps);
  lambda$this1 = runtime.safeCall(lambda10(w));
  tmp1 = NofibPrelude.map(lambda$this1, ps);
  return NofibPrelude.append(tmp, tmp1)
});
lambda11 = (undefined, function (x) {
  let tmp, tmp1;
  tmp = NofibPrelude.Cons(x, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(tmp, NofibPrelude.Nil);
  return NofibPrelude.Cons(tmp1, NofibPrelude.Nil)
});
lambda$2 = function lambda$(f, a, b) {
  let scrut, tmp, tmp1;
  tmp = runtime.safeCall(f(a));
  tmp1 = runtime.safeCall(f(b));
  scrut = tmp < tmp1;
  if (scrut === true) {
    return a
  } else {
    return b
  }
};
lambda6 = (undefined, function (f) {
  return (a, b) => {
    return lambda$2(f, a, b)
  }
});
lambda7 = (undefined, function (x) {
  return x
});
lambda4 = (undefined, function (a, s) {
  return NofibPrelude.Cons(a, s)
});
lambda5 = (undefined, function (a) {
  return NofibPrelude.Cons(a, NofibPrelude.Nil)
});
lambda$1 = function lambda$(f, a, s) {
  let tmp, tmp1;
  tmp = NofibPrelude.head(s);
  tmp1 = runtime.safeCall(f(a, tmp));
  return NofibPrelude.Cons(tmp1, s)
};
lambda2 = (undefined, function (f) {
  return (a, s) => {
    return lambda$1(f, a, s)
  }
});
lambda$ = function lambda$(g, a) {
  let tmp;
  tmp = runtime.safeCall(g(a));
  return NofibPrelude.Cons(tmp, NofibPrelude.Nil)
};
lambda3 = (undefined, function (g) {
  return (a) => {
    return lambda$(g, a)
  }
});
lambda1 = (undefined, function (l) {
  let tmp;
  tmp = NofibPrelude.nofibStringToList("\n");
  return NofibPrelude.append(l, tmp)
});
lambda = (undefined, function (x) {
  return x === "\n"
});
go = function go(vs) {
  let param0, param1, v, vs1, tmp, tmp1;
  if (vs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (vs instanceof NofibPrelude.Cons.class) {
    param0 = vs.head;
    param1 = vs.tail;
    v = param0;
    vs1 = param1;
    tmp = go(vs1);
    tmp1 = NofibPrelude.append(v, tmp);
    return NofibPrelude.Cons(" ", tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
para1 = class para {
  static {
    para1 = para;
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, lambda20;
    this.maxw = 70;
    this.optw = 63;
    this.nil_ = [
      NofibPrelude.Nil,
      NofibPrelude.Nil
    ];
    tmp = NofibPrelude.nofibStringToList("In the constructive programming community it is commonplace to see ");
    tmp1 = NofibPrelude.nofibStringToList("formal developments of textbook algorithms. In the algorithm design ");
    tmp2 = NofibPrelude.nofibStringToList("community, on the other hand, it may be well known that the textbook ");
    tmp3 = NofibPrelude.nofibStringToList("solution to a problem is not the most efficient possible. However, in ");
    tmp4 = NofibPrelude.nofibStringToList("presenting the more efficient solution, the algorithm designer will ");
    tmp5 = NofibPrelude.nofibStringToList("usually omit some of the implementation details, this creating an ");
    tmp6 = NofibPrelude.nofibStringToList("algorithm gap between the abstract algorithm and its concrete ");
    tmp7 = NofibPrelude.nofibStringToList("implementation. This is in contrast to the formal development, which ");
    tmp8 = NofibPrelude.nofibStringToList("usually presents the complete concrete implementation of the less ");
    tmp9 = NofibPrelude.nofibStringToList("efficient solution.\n\n");
    tmp10 = NofibPrelude.Cons(tmp9, NofibPrelude.Nil);
    tmp11 = NofibPrelude.Cons(tmp8, tmp10);
    tmp12 = NofibPrelude.Cons(tmp7, tmp11);
    tmp13 = NofibPrelude.Cons(tmp6, tmp12);
    tmp14 = NofibPrelude.Cons(tmp5, tmp13);
    tmp15 = NofibPrelude.Cons(tmp4, tmp14);
    tmp16 = NofibPrelude.Cons(tmp3, tmp15);
    tmp17 = NofibPrelude.Cons(tmp2, tmp16);
    tmp18 = NofibPrelude.Cons(tmp1, tmp17);
    tmp19 = NofibPrelude.Cons(tmp, tmp18);
    tmp20 = NofibPrelude.concat(tmp19);
    this.test = tmp20;
    lambda20 = (undefined, function () {
      let tmp21;
      tmp21 = para.testPara_nofib();
      return NofibPrelude.nofibListToString(tmp21)
    });
    BenchmarkPrelude.benchmark(lambda20)
  }
  static unwords(ws) {
    let param0, param1, w, ws1, tmp;
    if (ws instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ws instanceof NofibPrelude.Cons.class) {
      param0 = ws.head;
      param1 = ws.tail;
      w = param0;
      ws1 = param1;
      tmp = go(ws1);
      return NofibPrelude.append(w, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static break_(p, xs) {
    let param0, param1, x, xs1, scrut, first1, first0, ys, zs, scrut1, tmp, tmp1;
    if (xs instanceof NofibPrelude.Nil.class) {
      return [
        NofibPrelude.Nil,
        NofibPrelude.Nil
      ]
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param0 = xs.head;
      param1 = xs.tail;
      x = param0;
      xs1 = param1;
      scrut1 = runtime.safeCall(p(x));
      if (scrut1 === true) {
        tmp = NofibPrelude.Cons(x, xs1);
        return [
          NofibPrelude.Nil,
          tmp
        ]
      } else {
        scrut = para.break_(p, xs1);
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first0 = scrut[0];
          first1 = scrut[1];
          ys = first0;
          zs = first1;
          tmp1 = NofibPrelude.Cons(x, ys);
          return [
            tmp1,
            zs
          ]
        } else {
          throw new globalThis.Error("match error");
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static isSpace(c) {
    return c === " "
  } 
  static words(s) {
    let scrut, param0, param1, h, t, scrut1, first1, first0, w, s_, tmp, tmp1;
    scrut = NofibPrelude.dropWhile(para.isSpace, s);
    if (scrut instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (scrut instanceof NofibPrelude.Cons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      h = param0;
      t = param1;
      tmp = NofibPrelude.Cons(h, t);
      scrut1 = para.break_(para.isSpace, tmp);
      if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
        first0 = scrut1[0];
        first1 = scrut1[1];
        w = first0;
        s_ = first1;
        tmp1 = para.words(s_);
        return NofibPrelude.Cons(w, tmp1)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static lines(s1) {
    let scrut, first1, first0, l, s_, param0, param1, s__, tmp;
    scrut = para.break_(lambda, s1);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      l = first0;
      s_ = first1;
      if (s_ instanceof NofibPrelude.Nil.class) {
        tmp = NofibPrelude.Nil;
      } else if (s_ instanceof NofibPrelude.Cons.class) {
        param0 = s_.head;
        param1 = s_.tail;
        s__ = param1;
        tmp = para.lines(s__);
      } else {
        throw new globalThis.Error("match error");
      }
      return NofibPrelude.Cons(l, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static unlines(ls) {
    let tmp;
    tmp = NofibPrelude.map(lambda1, ls);
    return NofibPrelude.concat(tmp)
  } 
  static all(p1, xs1) {
    let param0, param1, x, xs2, tmp, tmp1;
    if (xs1 instanceof NofibPrelude.Nil.class) {
      return true
    } else if (xs1 instanceof NofibPrelude.Cons.class) {
      param0 = xs1.head;
      param1 = xs1.tail;
      x = param0;
      xs2 = param1;
      tmp = runtime.safeCall(p1(x));
      tmp1 = para.all(p1, xs2);
      return tmp && tmp1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static fold1(f, g, xs2) {
    let param0, param1, a, x, a1, tmp;
    if (xs2 instanceof NofibPrelude.Cons.class) {
      param0 = xs2.head;
      param1 = xs2.tail;
      a1 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return runtime.safeCall(g(a1))
      } else {
        a = param0;
        x = param1;
        tmp = para.fold1(f, g, x);
        return runtime.safeCall(f(a, tmp))
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static scan1(f1, g1, xs3) {
    let tmp, lambda$this;
    tmp = runtime.safeCall(lambda2(f1));
    lambda$this = runtime.safeCall(lambda3(g1));
    return para.fold1(tmp, lambda$this, xs3)
  } 
  static tails(xs4) {
    return para.scan1(lambda4, lambda5, xs4)
  } 
  static single(xs5) {
    let param0, param1, a;
    if (xs5 instanceof NofibPrelude.Cons.class) {
      param0 = xs5.head;
      param1 = xs5.tail;
      a = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return true
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static minWith(f2, xs6) {
    let tmp;
    tmp = runtime.safeCall(lambda6(f2));
    return para.fold1(tmp, lambda7, xs6)
  } 
  static new_(w, ls1) {
    let tmp;
    tmp = NofibPrelude.Cons(w, NofibPrelude.Nil);
    return NofibPrelude.Cons(tmp, ls1)
  } 
  static glue(w1, ls2) {
    let param0, param1, l, ls_, tmp;
    if (ls2 instanceof NofibPrelude.Cons.class) {
      param0 = ls2.head;
      param1 = ls2.tail;
      l = param0;
      ls_ = param1;
      tmp = NofibPrelude.Cons(w1, l);
      return NofibPrelude.Cons(tmp, ls_)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static formats(txt) {
    let tmp, tmp1;
    tmp = lambda8;
    tmp1 = lambda11;
    return para.fold1(tmp, tmp1, txt)
  } 
  static width(ls3) {
    return para.fold1(plus, NofibPrelude.listLen, ls3)
  } 
  static fits(xs7) {
    let tmp;
    tmp = para.width(xs7);
    return tmp <= para.maxw
  } 
  static feasible(a) {
    return para.all(para.fits, a)
  } 
  static cost(ls4) {
    return para.fold1(plus1, lambda12, ls4)
  } 
  static par0(x) {
    let tmp, tmp1;
    tmp = para.formats(x);
    tmp1 = NofibPrelude.filter(para.feasible, tmp);
    return para.minWith(para.cost, tmp1)
  } 
  static fitH(ls5) {
    let tmp;
    tmp = NofibPrelude.head(ls5);
    return para.fits(tmp)
  } 
  static fst3(a_b_c) {
    let first2, first1, first0, a1, b, c1;
    if (globalThis.Array.isArray(a_b_c) && a_b_c.length === 3) {
      first0 = a_b_c[0];
      first1 = a_b_c[1];
      first2 = a_b_c[2];
      a1 = first0;
      b = first1;
      c1 = first2;
      return a1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static snd3(a_b_c1) {
    let first2, first1, first0, a1, b, c1;
    if (globalThis.Array.isArray(a_b_c1) && a_b_c1.length === 3) {
      first0 = a_b_c1[0];
      first1 = a_b_c1[1];
      first2 = a_b_c1[2];
      a1 = first0;
      b = first1;
      c1 = first2;
      return b
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static thd3(a_b_c2) {
    let first2, first1, first0, a1, b, c1;
    if (globalThis.Array.isArray(a_b_c2) && a_b_c2.length === 3) {
      first0 = a_b_c2[0];
      first1 = a_b_c2[1];
      first2 = a_b_c2[2];
      a1 = first0;
      b = first1;
      c1 = first2;
      return c1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static width_tl(a_b_c3) {
    return para.fst3(a_b_c3)
  } 
  static cost_tl(a_b_c4) {
    return para.snd3(a_b_c4)
  } 
  static len_tl(a_b_c5) {
    return para.thd3(a_b_c5)
  } 
  static tile(ws1, a_b) {
    let first1, first0, param0, param1, m, ms, n, l, scrut, first11, first01, ws11, ws2, n1, tmp, tmp1, tmp2, tmp3;
    if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
      first0 = a_b[0];
      first1 = a_b[1];
      if (first0 instanceof NofibPrelude.Nil.class) {
        n1 = first1;
        return NofibPrelude.Nil
      } else if (first0 instanceof NofibPrelude.Cons.class) {
        param0 = first0.head;
        param1 = first0.tail;
        m = param0;
        ms = param1;
        n = first1;
        tmp = n - m;
        l = tmp;
        scrut = NofibPrelude.splitAt(l, ws1);
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first01 = scrut[0];
          first11 = scrut[1];
          ws11 = first01;
          ws2 = first11;
          tmp1 = NofibPrelude.Cons(m, ms);
          tmp2 = NofibPrelude.drop(l, tmp1);
          tmp3 = para.tile(ws2, [
            tmp2,
            m
          ]);
          return NofibPrelude.Cons(ws11, tmp3)
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
  static null__(a_b1) {
    let first1, first0;
    if (globalThis.Array.isArray(a_b1) && a_b1.length === 2) {
      first0 = a_b1[0];
      first1 = a_b1[1];
      if (first0 instanceof NofibPrelude.Nil.class) {
        if (first1 instanceof NofibPrelude.Nil.class) {
          return true
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
  static single_(a_b2) {
    let first1, first0, x1, y, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    if (globalThis.Array.isArray(a_b2) && a_b2.length === 2) {
      first0 = a_b2[0];
      first1 = a_b2[1];
      x1 = first0;
      y = first1;
      tmp = NofibPrelude.null_(x1);
      tmp1 = para.single(y);
      tmp2 = tmp && tmp1;
      tmp3 = para.single(x1);
      tmp4 = NofibPrelude.null_(y);
      tmp5 = tmp3 && tmp4;
      return tmp2 || tmp5
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static head_(a_b3) {
    let first1, first0, x1, y, scrut, tmp;
    if (globalThis.Array.isArray(a_b3) && a_b3.length === 2) {
      first0 = a_b3[0];
      first1 = a_b3[1];
      x1 = first0;
      y = first1;
      tmp = NofibPrelude.null_(x1);
      scrut = BenchmarkPrelude.not(tmp);
      if (scrut === true) {
        return NofibPrelude.head(x1)
      } else {
        return NofibPrelude.head(y)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static last_(a_b4) {
    let first1, first0, y, x1, scrut, tmp;
    if (globalThis.Array.isArray(a_b4) && a_b4.length === 2) {
      first0 = a_b4[0];
      first1 = a_b4[1];
      y = first0;
      x1 = first1;
      tmp = NofibPrelude.null_(x1);
      scrut = BenchmarkPrelude.not(tmp);
      if (scrut === true) {
        return NofibPrelude.head(x1)
      } else {
        return NofibPrelude.head(y)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static cons_(a1, a_b5) {
    let first1, first0, x1, y, scrut, tmp, tmp1, tmp2;
    if (globalThis.Array.isArray(a_b5) && a_b5.length === 2) {
      first0 = a_b5[0];
      first1 = a_b5[1];
      x1 = first0;
      y = first1;
      tmp = NofibPrelude.null_(y);
      scrut = BenchmarkPrelude.not(tmp);
      if (scrut === true) {
        tmp1 = NofibPrelude.Cons(a1, x1);
        return [
          tmp1,
          y
        ]
      } else {
        tmp2 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
        return [
          tmp2,
          x1
        ]
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static snoc_(a2, a_b6) {
    let first1, first0, y, x1, scrut, tmp, tmp1, tmp2;
    if (globalThis.Array.isArray(a_b6) && a_b6.length === 2) {
      first0 = a_b6[0];
      first1 = a_b6[1];
      y = first0;
      x1 = first1;
      tmp = NofibPrelude.null_(y);
      scrut = BenchmarkPrelude.not(tmp);
      if (scrut === true) {
        tmp1 = NofibPrelude.Cons(a2, x1);
        return [
          y,
          tmp1
        ]
      } else {
        tmp2 = NofibPrelude.Cons(a2, NofibPrelude.Nil);
        return [
          x1,
          tmp2
        ]
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static tail_(a_b7) {
    let first1, first0, x1, y, scrut, scrut1, first11, first01, y0, y1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4;
    if (globalThis.Array.isArray(a_b7) && a_b7.length === 2) {
      first0 = a_b7[0];
      first1 = a_b7[1];
      x1 = first0;
      y = first1;
      scrut2 = NofibPrelude.null_(x1);
      if (scrut2 === true) {
        return [
          NofibPrelude.Nil,
          NofibPrelude.Nil
        ]
      } else {
        scrut = para.single(x1);
        if (scrut === true) {
          tmp = NofibPrelude.listLen(y);
          tmp1 = NofibPrelude.intDiv(tmp, 2);
          scrut1 = NofibPrelude.splitAt(tmp1, y);
          if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
            first01 = scrut1[0];
            first11 = scrut1[1];
            y0 = first01;
            y1 = first11;
            tmp2 = NofibPrelude.reverse(y1);
            return [
              tmp2,
              y0
            ]
          } else {
            tmp3 = NofibPrelude.tail(x1);
            return [
              tmp3,
              y
            ]
          }
        } else {
          tmp4 = NofibPrelude.tail(x1);
          return [
            tmp4,
            y
          ]
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static init_(a_b8) {
    let first1, first0, y, x1, scrut, scrut1, first11, first01, y0, y1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4;
    if (globalThis.Array.isArray(a_b8) && a_b8.length === 2) {
      first0 = a_b8[0];
      first1 = a_b8[1];
      y = first0;
      x1 = first1;
      scrut2 = NofibPrelude.null_(x1);
      if (scrut2 === true) {
        return [
          NofibPrelude.Nil,
          NofibPrelude.Nil
        ]
      } else {
        scrut = para.single(x1);
        if (scrut === true) {
          tmp = NofibPrelude.listLen(y);
          tmp1 = NofibPrelude.intDiv(tmp, 2);
          scrut1 = NofibPrelude.splitAt(tmp1, y);
          if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
            first01 = scrut1[0];
            first11 = scrut1[1];
            y0 = first01;
            y1 = first11;
            tmp2 = NofibPrelude.reverse(y1);
            return [
              y0,
              tmp2
            ]
          } else {
            tmp3 = NofibPrelude.tail(x1);
            return [
              y,
              tmp3
            ]
          }
        } else {
          tmp4 = NofibPrelude.tail(x1);
          return [
            y,
            tmp4
          ]
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static unformat(a3, l) {
    let tmp;
    tmp = runtime.safeCall(lambda13(a3));
    return para.fold1(tmp, lambda14, l)
  } 
  static format(a4, x1) {
    let lambda$this, lambda$this1;
    if (x1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil)
    } else {
      lambda$this = runtime.safeCall(lambda15(a4));
      lambda$this1 = runtime.safeCall(lambda16(a4));
      return para.fold1(lambda$this, lambda$this1, x1)
    }
  } 
  static unparas(ls6) {
    return para.unformat(NofibPrelude.Nil, ls6)
  } 
  static paras(ls7) {
    let tmp;
    tmp = para.format(NofibPrelude.Nil, ls7);
    return NofibPrelude.filter(lambda17, tmp)
  } 
  static parse(ls8) {
    let tmp, tmp1;
    tmp = para.lines(ls8);
    tmp1 = NofibPrelude.map(para.words, tmp);
    return para.paras(tmp1)
  } 
  static unparse(ls9) {
    let tmp, tmp1;
    tmp = para.unparas(ls9);
    tmp1 = NofibPrelude.map(para.unwords, tmp);
    return para.unlines(tmp1)
  } 
  static startr(a5) {
    let scrut, tmp;
    scrut = a5 <= para.maxw;
    if (scrut === true) {
      tmp = para.cons_([
        0,
        0,
        0
      ], para.nil_);
      return [
        tmp,
        a5,
        1
      ]
    } else {
      throw globalThis.Error("startr param error");
    }
  } 
  static ceildiv(n, m) {
    let tmp, tmp1;
    tmp = n + m;
    tmp1 = tmp - 1;
    return NofibPrelude.intDiv(tmp1, m)
  } 
  static fmtWith(par) {
    let tmp, tmp1, lambda$this;
    tmp = para.parse(par);
    lambda$this = runtime.safeCall(lambda18(par));
    tmp1 = NofibPrelude.map(lambda$this, tmp);
    return para.unparse(tmp1)
  } 
  static stepr(w2, ps_tw_tl) {
    let first2, first1, first0, ps, tw, tl, tot_width, tot_len, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    if (globalThis.Array.isArray(ps_tw_tl) && ps_tw_tl.length === 3) {
      first0 = ps_tw_tl[0];
      first1 = ps_tw_tl[1];
      first2 = ps_tw_tl[2];
      ps = first0;
      tw = first1;
      tl = first2;
      tmp = w2 + 1;
      tmp1 = tmp + tw;
      tot_width = tmp1;
      tmp2 = 1 + tl;
      tot_len = tmp2;
      tmp3 = para.last_(ps);
      tmp4 = new_$(tw, tl, tmp3);
      tmp5 = myAdd$(tot_width, tmp4, ps);
      tmp6 = drop_nofit$(tot_width, tmp5);
      tmp7 = trim$(tot_width, tmp6);
      return [
        tmp7,
        tot_width,
        tot_len
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static par3(ws2) {
    let zs, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = NofibPrelude.map(NofibPrelude.listLen, ws2);
    tmp1 = para.scan1(para.stepr, para.startr, tmp);
    zs = tmp1;
    tmp2 = lambda19;
    tmp3 = NofibPrelude.map(tmp2, zs);
    tmp4 = NofibPrelude.head(zs);
    tmp5 = para.thd3(tmp4);
    return para.tile(ws2, [
      tmp3,
      tmp5
    ])
  } 
  static fmt(x2) {
    let tmp, tmp1, tmp2;
    tmp = para.parse(x2);
    tmp1 = NofibPrelude.concat(tmp);
    tmp2 = NofibPrelude.map(para.par3, tmp1);
    return para.unparse(tmp2)
  } 
  static testPara_nofib() {
    let scrut;
    scrut = NofibPrelude.null_(para.test);
    if (scrut === true) {
      return NofibPrelude.Nil
    } else {
      return para.fmt(para.test)
    }
  }
  static toString() { return "para"; }
};
let para = para1; export default para;
