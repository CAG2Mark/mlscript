import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let label, labelOf, lscomp, sim, cse1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda14, lambda15, lambda16, lambda17, lambda18, lambda19, lambda20, lambda$, lambda$1, lambda$2, lambda$3, lambda$4, lambda$5, lambda$6, lambda$7, lambda$8, lambda$9, lambda$10, lambda$11, lambda$12, lambda$13, lambda$14, lambda$15, lambda$16, lambda$17, lscomp$;
lambda20 = (undefined, function (i) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  tmp = NofibPrelude.intMod(i, 6);
  tmp1 = NofibPrelude.Cons(cse1.example5, NofibPrelude.Nil);
  tmp2 = NofibPrelude.Cons(cse1.example4, tmp1);
  tmp3 = NofibPrelude.Cons(cse1.example3, tmp2);
  tmp4 = NofibPrelude.Cons(cse1.example2, tmp3);
  tmp5 = NofibPrelude.Cons(cse1.example1, tmp4);
  tmp6 = NofibPrelude.Cons(cse1.example0, tmp5);
  tmp7 = NofibPrelude.take(tmp, tmp6);
  return NofibPrelude.map(cse1.cse, tmp7)
});
lscomp$ = function lscomp$(s, rcs, ls) {
  let param0, param1, first2, first1, first0, m, s_, cs_, t, scrut, scrut1, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 3) {
      first0 = param0[0];
      first1 = param0[1];
      first2 = param0[2];
      m = first0;
      s_ = first1;
      cs_ = first2;
      t = param1;
      scrut = s === s_;
      if (scrut === true) {
        scrut1 = NofibPrelude.listEq(cs_, rcs);
        if (scrut1 === true) {
          tmp = lscomp$(s, rcs, t);
          return NofibPrelude.Cons(m, tmp)
        } else {
          return lscomp$(s, rcs, t)
        }
      } else {
        return lscomp$(s, rcs, t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp = function lscomp(s, rcs) {
  return (ls) => {
    return lscomp$(s, rcs, ls)
  }
};
lambda$17 = function lambda$(n, r, ms, x) {
  let tmp;
  tmp = NofibPrelude.head(ms);
  return cse1.newlyDefined(n, tmp, r, x)
};
lambda18 = (undefined, function (n, r, ms) {
  return (x) => {
    return lambda$17(n, r, ms, x)
  }
});
sim = function sim(n_s_cs, r_lg) {
  let first2, first1, first0, n, s, cs, first11, first01, r, lg, rcs, ms, scrut, tmp, tmp1, tmp2, lambda$this;
  if (globalThis.Array.isArray(n_s_cs) && n_s_cs.length === 3) {
    first0 = n_s_cs[0];
    first1 = n_s_cs[1];
    first2 = n_s_cs[2];
    n = first0;
    s = first1;
    cs = first2;
    if (globalThis.Array.isArray(r_lg) && r_lg.length === 2) {
      first01 = r_lg[0];
      first11 = r_lg[1];
      r = first01;
      lg = first11;
      tmp = NofibPrelude.map(r, cs);
      rcs = tmp;
      tmp1 = lscomp$(s, rcs, lg);
      ms = tmp1;
      scrut = NofibPrelude.null_(ms);
      if (scrut === true) {
        tmp2 = NofibPrelude.Cons([
          n,
          s,
          rcs
        ], lg);
        return [
          r,
          tmp2
        ]
      } else {
        lambda$this = runtime.safeCall(lambda18(n, r, ms));
        return [
          lambda$this,
          lg
        ]
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda19 = (undefined, function (x) {
  return x
});
lambda17 = (undefined, function (_p) {
  return cse1.retURN(false)
});
lambda$16 = function lambda$(n, us) {
  let scrut, tmp, tmp1;
  scrut = NofibPrelude.inList(n, us);
  if (scrut === true) {
    return cse1.retURN(true)
  } else {
    tmp = NofibPrelude.Cons(n, us);
    tmp1 = cse1.set_(tmp);
    return cse1.bind(tmp1, lambda17)
  }
};
lambda16 = (undefined, function (n) {
  return (us) => {
    return lambda$16(n, us)
  }
});
labelOf = function labelOf(t) {
  let param0, param1, first1, first0, n, x, xs;
  if (t instanceof cse1.Node.class) {
    param0 = t.a;
    param1 = t.b;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      n = first0;
      x = first1;
      xs = param1;
      return n
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$15 = function lambda$(x, n, ts) {
  let tmp;
  tmp = cse1.Node([
    n,
    x
  ], ts);
  return cse1.retURN(tmp)
};
lambda15 = (undefined, function (x, n) {
  return (ts) => {
    return lambda$15(x, n, ts)
  }
});
lambda$14 = function lambda$(x, xs, n) {
  let tmp, lambda$this;
  tmp = cse1.mmapl(label, xs);
  lambda$this = runtime.safeCall(lambda15(x, n));
  return cse1.bind(tmp, lambda$this)
};
lambda14 = (undefined, function (x, xs) {
  return (n) => {
    return lambda$14(x, xs, n)
  }
});
label = function label(t) {
  let param0, param1, x, xs, lambda$this;
  if (t instanceof cse1.Node.class) {
    param0 = t.a;
    param1 = t.b;
    x = param0;
    xs = param1;
    lambda$this = runtime.safeCall(lambda14(x, xs));
    return cse1.bind(cse1.incr, lambda$this)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$13 = function lambda$(s_, s) {
  return [
    s_,
    s
  ]
};
lambda13 = (undefined, function (s_) {
  return (s) => {
    return lambda$13(s_, s)
  }
});
lambda$12 = function lambda$(f, s) {
  let tmp;
  tmp = runtime.safeCall(f(s));
  return [
    tmp,
    s
  ]
};
lambda12 = (undefined, function (f) {
  return (s) => {
    return lambda$12(f, s)
  }
});
lambda$11 = function lambda$(f, s) {
  let tmp;
  tmp = runtime.safeCall(f(s));
  return [
    s,
    tmp
  ]
};
lambda11 = (undefined, function (f) {
  return (s) => {
    return lambda$11(f, s)
  }
});
lambda$10 = function lambda$(t, f, cond) {
  if (cond === true) {
    return t
  } else {
    return f
  }
};
lambda10 = (undefined, function (t, f) {
  return (cond) => {
    return lambda$10(t, f, cond)
  }
});
lambda$9 = function lambda$(f, x, y) {
  return runtime.safeCall(f(x, y))
};
lambda9 = (undefined, function (f, x) {
  return (y) => {
    return lambda$9(f, x, y)
  }
});
lambda$8 = function lambda$(f, xs, fax) {
  return cse1.mfoldl(f, fax, xs)
};
lambda8 = (undefined, function (f, xs) {
  return (fax) => {
    return lambda$8(f, xs, fax)
  }
});
lambda$7 = function lambda$(ys, y) {
  let tmp;
  tmp = NofibPrelude.Cons(y, ys);
  return cse1.retURN(tmp)
};
lambda7 = (undefined, function (ys) {
  return (y) => {
    return lambda$7(ys, y)
  }
});
lambda$6 = function lambda$(f, x, ys) {
  let tmp, lambda$this;
  tmp = runtime.safeCall(f(x));
  lambda$this = runtime.safeCall(lambda7(ys));
  return cse1.bind(tmp, lambda$this)
};
lambda6 = (undefined, function (f, x) {
  return (ys) => {
    return lambda$6(f, x, ys)
  }
});
lambda$5 = function lambda$(b, bs) {
  let tmp;
  tmp = NofibPrelude.Cons(b, bs);
  return cse1.retURN(tmp)
};
lambda5 = (undefined, function (b) {
  return (bs) => {
    return lambda$5(b, bs)
  }
});
lambda$4 = function lambda$(f, as_, b) {
  let tmp, lambda$this;
  tmp = cse1.mmapl(f, as_);
  lambda$this = runtime.safeCall(lambda5(b));
  return cse1.bind(tmp, lambda$this)
};
lambda4 = (undefined, function (f, as_) {
  return (b) => {
    return lambda$4(f, as_, b)
  }
});
lambda$3 = function lambda$(f, m, s) {
  let scrut, first1, first0, s_, a, tmp;
  scrut = runtime.safeCall(m(s));
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    s_ = first0;
    a = first1;
    tmp = runtime.safeCall(f(a));
    return [
      s_,
      tmp
    ]
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda3 = (undefined, function (f, m) {
  return (s) => {
    return lambda$3(f, m, s)
  }
});
lambda$2 = function lambda$(m, s) {
  let scrut, first1, first0, s_, ma;
  scrut = runtime.safeCall(m(s));
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    s_ = first0;
    ma = first1;
    return runtime.safeCall(ma(s_))
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda2 = (undefined, function (m) {
  return (s) => {
    return lambda$2(m, s)
  }
});
lambda$1 = function lambda$(m, f, s) {
  let scrut, first1, first0, s_, a, tmp;
  scrut = runtime.safeCall(m(s));
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    s_ = first0;
    a = first1;
    tmp = runtime.safeCall(f(a));
    return runtime.safeCall(tmp(s_))
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda1 = (undefined, function (m, f) {
  return (s) => {
    return lambda$1(m, f, s)
  }
});
lambda$ = function lambda$(a, s) {
  return [
    s,
    a
  ]
};
lambda = (undefined, function (a) {
  return (s) => {
    return lambda$(a, s)
  }
});
cse1 = class cse {
  static {
    cse1 = cse;
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, lambda21, lambda22;
    lambda21 = (undefined, function (x) {
      return x + 1
    });
    tmp = cse.update(lambda21);
    this.incr = tmp;
    this.Node = function Node(a1, b1) {
      return new Node.class(a1, b1);
    };
    this.Node.class = class Node {
      constructor(a, b) {
        this.a = a;
        this.b = b;
      }
      toString() { return "Node(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    tmp1 = cse.Node("0", NofibPrelude.Nil);
    this.zerO = tmp1;
    tmp2 = cse.Node("a", NofibPrelude.Nil);
    this.a = tmp2;
    tmp3 = cse.Node("b", NofibPrelude.Nil);
    this.b = tmp3;
    tmp4 = cse.Node("c", NofibPrelude.Nil);
    this.c = tmp4;
    tmp5 = cse.Node("d", NofibPrelude.Nil);
    this.d = tmp5;
    this.example0 = cse.a;
    tmp6 = cse.plus_(cse.a, cse.a);
    this.example1 = tmp6;
    tmp7 = cse.mult_(cse.a, cse.b);
    tmp8 = cse.mult_(cse.a, cse.b);
    tmp9 = cse.plus_(tmp7, tmp8);
    this.example2 = tmp9;
    tmp10 = cse.plus_(cse.a, cse.b);
    tmp11 = cse.mult_(tmp10, cse.c);
    tmp12 = cse.plus_(cse.a, cse.b);
    tmp13 = cse.plus_(tmp11, tmp12);
    this.example3 = tmp13;
    tmp14 = NofibPrelude.Cons(cse.d, NofibPrelude.Nil);
    tmp15 = NofibPrelude.Cons(cse.c, tmp14);
    tmp16 = NofibPrelude.Cons(cse.b, tmp15);
    tmp17 = NofibPrelude.Cons(cse.a, tmp16);
    tmp18 = NofibPrelude.scanl(cse.plus_, cse.zerO, tmp17);
    tmp19 = cse.prod(tmp18);
    this.example4 = tmp19;
    tmp20 = NofibPrelude.Cons(cse.d, NofibPrelude.Nil);
    tmp21 = NofibPrelude.Cons(cse.c, tmp20);
    tmp22 = NofibPrelude.Cons(cse.b, tmp21);
    tmp23 = NofibPrelude.Cons(cse.a, tmp22);
    tmp24 = NofibPrelude.scanr(cse.plus_, cse.zerO, tmp23);
    tmp25 = cse.prod(tmp24);
    this.example5 = tmp25;
    lambda22 = (undefined, function () {
      let tmp26;
      tmp26 = cse.testCse_nofib(6);
      return runtime.safeCall(tmp26.toString())
    });
    BenchmarkPrelude.benchmark(lambda22)
  }
  static retURN(a) {
    return runtime.safeCall(lambda(a))
  } 
  static bind(m, f) {
    return runtime.safeCall(lambda1(m, f))
  } 
  static join(m1) {
    return runtime.safeCall(lambda2(m1))
  } 
  static mmap(f1, m2) {
    return runtime.safeCall(lambda3(f1, m2))
  } 
  static mmapl(f2, aas) {
    let param0, param1, a1, as_, tmp, lambda$this;
    if (aas instanceof NofibPrelude.Nil.class) {
      return cse.retURN(NofibPrelude.Nil)
    } else if (aas instanceof NofibPrelude.Cons.class) {
      param0 = aas.head;
      param1 = aas.tail;
      a1 = param0;
      as_ = param1;
      tmp = runtime.safeCall(f2(a1));
      lambda$this = runtime.safeCall(lambda4(f2, as_));
      return cse.bind(tmp, lambda$this)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static mmapr(f3, xs) {
    let param0, param1, x, xs1, tmp, lambda$this;
    if (xs instanceof NofibPrelude.Nil.class) {
      return cse.retURN(NofibPrelude.Nil)
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param0 = xs.head;
      param1 = xs.tail;
      x = param0;
      xs1 = param1;
      tmp = cse.mmapr(f3, xs1);
      lambda$this = runtime.safeCall(lambda6(f3, x));
      return cse.bind(tmp, lambda$this)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static mfoldl(f4, a1, xs1) {
    let param0, param1, x, xs2, tmp, lambda$this;
    if (xs1 instanceof NofibPrelude.Nil.class) {
      return cse.retURN(a1)
    } else if (xs1 instanceof NofibPrelude.Cons.class) {
      param0 = xs1.head;
      param1 = xs1.tail;
      x = param0;
      xs2 = param1;
      tmp = runtime.safeCall(f4(a1, x));
      lambda$this = runtime.safeCall(lambda8(f4, xs2));
      return cse.bind(tmp, lambda$this)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static mfoldr(f5, a2, xs2) {
    let param0, param1, x, xs3, tmp, lambda$this;
    if (xs2 instanceof NofibPrelude.Nil.class) {
      return cse.retURN(a2)
    } else if (xs2 instanceof NofibPrelude.Cons.class) {
      param0 = xs2.head;
      param1 = xs2.tail;
      x = param0;
      xs3 = param1;
      tmp = cse.mfoldr(f5, a2, xs3);
      lambda$this = runtime.safeCall(lambda9(f5, x));
      return cse.bind(tmp, lambda$this)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static mif(c, t, f6) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda10(t, f6));
    return cse.bind(c, lambda$this)
  } 
  static startingWith(m3, v) {
    let scrut, first1, first0, final1, answer;
    scrut = runtime.safeCall(m3(v));
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      final1 = first0;
      answer = first1;
      return answer
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static fetch(s) {
    return [
      s,
      s
    ]
  } 
  static fetchWith(f7) {
    return runtime.safeCall(lambda11(f7))
  } 
  static update(f8) {
    return runtime.safeCall(lambda12(f8))
  } 
  static set_(s_) {
    return runtime.safeCall(lambda13(s_))
  } 
  static labelTree(t1) {
    let tmp;
    tmp = label(t1);
    return cse.startingWith(tmp, 0)
  } 
  static ltGraph(t2) {
    let param0, param1, first1, first0, n, x, xs3, tmp, tmp1, tmp2;
    if (t2 instanceof cse.Node.class) {
      param0 = t2.a;
      param1 = t2.b;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        n = first0;
        x = first1;
        xs3 = param1;
        tmp = NofibPrelude.map(labelOf, xs3);
        tmp1 = NofibPrelude.map(cse.ltGraph, xs3);
        tmp2 = NofibPrelude.concat(tmp1);
        return NofibPrelude.Cons([
          n,
          x,
          tmp
        ], tmp2)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static visited(n) {
    let tmp;
    tmp = runtime.safeCall(lambda16(n));
    return cse.bind(cse.fetch, tmp)
  } 
  static newlyDefined(x, fx, f9, y) {
    let scrut;
    scrut = x === y;
    if (scrut === true) {
      return fx
    } else {
      return runtime.safeCall(f9(y))
    }
  } 
  static findCommon(ls) {
    let scrut, first1, first0, a3, b, tmp;
    scrut = NofibPrelude.foldr(sim, [
      lambda19,
      NofibPrelude.Nil
    ], ls);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      a3 = first0;
      b = first1;
      return b
    } else {
      tmp = runtime.safeCall(ls.toString());
      throw globalThis.Error(tmp);
    }
  } 
  static cse(t3) {
    let tmp, tmp1;
    tmp = cse.labelTree(t3);
    tmp1 = cse.ltGraph(tmp);
    return cse.findCommon(tmp1)
  } 
  static plus_(x1, y1) {
    let tmp, tmp1;
    tmp = NofibPrelude.Cons(y1, NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons(x1, tmp);
    return cse.Node("+", tmp1)
  } 
  static mult_(x2, y2) {
    let tmp, tmp1;
    tmp = NofibPrelude.Cons(y2, NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons(x2, tmp);
    return cse.Node("*", tmp1)
  } 
  static prod(xs3) {
    return cse.Node("X", xs3)
  } 
  static testCse_nofib(n1) {
    let tmp, tmp1;
    tmp = lambda20;
    tmp1 = NofibPrelude.enumFromTo(1, n1);
    return NofibPrelude.map(tmp, tmp1)
  }
  static toString() { return "cse"; }
};
let cse = cse1; export default cse;
