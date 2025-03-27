import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let go, lscomp, lscomp2, lscomp1, tryy, cichelli1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda$, lambda$1, lscomp$, lambda$2, lambda$3, lambda$4, lambda$5, lambda$6, lambda$7, lscomp2$, lambda$8, lambda$9, tryy$;
tryy$ = function tryy$(keyHashSet, charAssocs, s, a, z, n, ks, newAssocs) {
  let newCharAssocs, scrut, param0, newKeyHashSet, tmp, tmp1, tmp2;
  tmp = NofibPrelude.append(newAssocs, charAssocs);
  newCharAssocs = tmp;
  tmp1 = cichelli1.K(s, a, z, n);
  tmp2 = cichelli1.hash(newCharAssocs, tmp1);
  scrut = cichelli1.hinsert(tmp2, keyHashSet);
  if (scrut instanceof NofibPrelude.None.class) {
    return cichelli1.NotEver(1)
  } else if (scrut instanceof NofibPrelude.Some.class) {
    param0 = scrut.x;
    newKeyHashSet = param0;
    return cichelli1.findhash_(newKeyHashSet, newCharAssocs, ks)
  } else {
    throw new globalThis.Error("match error");
  }
};
tryy = function tryy(keyHashSet, charAssocs, s, a, z, n, ks) {
  return (newAssocs) => {
    return tryy$(keyHashSet, charAssocs, s, a, z, n, ks, newAssocs)
  }
};
lambda$9 = function lambda$(keyHashSet, charAssocs, s, a, z, n, ks, m) {
  let tmp;
  tmp = NofibPrelude.Cons([
    a,
    m
  ], NofibPrelude.Nil);
  return tryy$(keyHashSet, charAssocs, s, a, z, n, ks, tmp)
};
lambda5 = (undefined, function (keyHashSet, charAssocs, s, a, z, n, ks) {
  return (m) => {
    return lambda$9(keyHashSet, charAssocs, s, a, z, n, ks, m)
  }
});
lambda$8 = function lambda$(ls1, m, ms, n, ns) {
  let tmp;
  tmp = lscomp2$(ls1, m, ms, ns);
  return NofibPrelude.LzCons([
    m,
    n
  ], tmp)
};
lambda7 = (undefined, function (ls1, m, ms, n, ns) {
  return () => {
    return lambda$8(ls1, m, ms, n, ns)
  }
});
lscomp2$ = function lscomp2$(ls1, m, ms, ls2) {
  let scrut, param0, param1, n, ns, lambda$this;
  scrut = NofibPrelude.force(ls2);
  if (scrut instanceof NofibPrelude.LzNil.class) {
    return lscomp1(ms)
  } else if (scrut instanceof NofibPrelude.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    n = param0;
    ns = param1;
    lambda$this = runtime.safeCall(lambda7(ls1, m, ms, n, ns));
    return NofibPrelude.lazy(lambda$this)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp2 = function lscomp2(ls1, m, ms) {
  return (ls2) => {
    return lscomp2$(ls1, m, ms, ls2)
  }
};
lambda$7 = function lambda$(ls1) {
  let scrut, param0, param1, m, ms, tmp, tmp1;
  scrut = NofibPrelude.force(ls1);
  if (scrut instanceof NofibPrelude.LzNil.class) {
    return NofibPrelude.LzNil
  } else if (scrut instanceof NofibPrelude.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    m = param0;
    ms = param1;
    tmp = cichelli1.enumFromTo_lz(0, cichelli1.maxval);
    tmp1 = lscomp2$(ls1, m, ms, tmp);
    return NofibPrelude.force(tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda6 = (undefined, function (ls1) {
  return () => {
    return lambda$7(ls1)
  }
});
lscomp1 = function lscomp1(ls1) {
  let tmp;
  tmp = runtime.safeCall(lambda6(ls1));
  return NofibPrelude.lazy(tmp)
};
lambda$6 = function lambda$(keyHashSet, charAssocs, s, a, z, n, ks, caseScrut) {
  let first1, first0, m, n1, tmp, tmp1;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    m = first0;
    n1 = first1;
    tmp = NofibPrelude.Cons([
      z,
      n1
    ], NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons([
      a,
      m
    ], tmp);
    return tryy$(keyHashSet, charAssocs, s, a, z, n, ks, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda8 = (undefined, function (keyHashSet, charAssocs, s, a, z, n, ks) {
  return (caseScrut) => {
    return lambda$6(keyHashSet, charAssocs, s, a, z, n, ks, caseScrut)
  }
});
lambda$5 = function lambda$(keyHashSet, charAssocs, s, a, z, n, ks, m) {
  let tmp;
  tmp = NofibPrelude.Cons([
    a,
    m
  ], NofibPrelude.Nil);
  return tryy$(keyHashSet, charAssocs, s, a, z, n, ks, tmp)
};
lambda9 = (undefined, function (keyHashSet, charAssocs, s, a, z, n, ks) {
  return (m) => {
    return lambda$5(keyHashSet, charAssocs, s, a, z, n, ks, m)
  }
});
lambda$4 = function lambda$(keyHashSet, charAssocs, s, a, z, n, ks, n1) {
  let tmp;
  tmp = NofibPrelude.Cons([
    z,
    n1
  ], NofibPrelude.Nil);
  return tryy$(keyHashSet, charAssocs, s, a, z, n, ks, tmp)
};
lambda10 = (undefined, function (keyHashSet, charAssocs, s, a, z, n, ks) {
  return (n1) => {
    return lambda$4(keyHashSet, charAssocs, s, a, z, n, ks, n1)
  }
});
lambda$3 = function lambda$(ds_, x) {
  let tmp;
  tmp = cichelli1.ends(x);
  return cichelli1.subset(tmp, ds_)
};
lambda4 = (undefined, function (ds_) {
  return (x) => {
    return lambda$3(ds_, x)
  }
});
lambda$2 = function lambda$(p, x, y) {
  return cichelli1.select(p, x, y)
};
lambda3 = (undefined, function (p) {
  return (x, y) => {
    return lambda$2(p, x, y)
  }
});
lambda2 = (undefined, function (k) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.head(k);
  tmp1 = cichelli1.last(k);
  tmp2 = NofibPrelude.listLen(k);
  return cichelli1.K(k, tmp, tmp1, tmp2)
});
lscomp$ = function lscomp$(xs, ls) {
  let param0, param1, h, t, scrut, tmp, tmp1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    tmp = NofibPrelude.inList(h, xs);
    scrut = BenchmarkPrelude.not(tmp);
    if (scrut === true) {
      tmp1 = lscomp$(xs, t);
      return NofibPrelude.Cons(h, tmp1)
    } else {
      return lscomp$(xs, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp = function lscomp(xs) {
  return (ls) => {
    return lscomp$(xs, ls)
  }
};
lambda$1 = function lambda$(ys, x) {
  return NofibPrelude.inList(x, ys)
};
lambda1 = (undefined, function (ys) {
  return (x) => {
    return lambda$1(ys, x)
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
lambda$ = function lambda$(a, b) {
  let scrut, tmp, tmp1;
  scrut = a <= b;
  if (scrut === true) {
    tmp = a + 1;
    tmp1 = cichelli1.enumFromTo_lz(tmp, b);
    return NofibPrelude.LzCons(a, tmp1)
  } else {
    return NofibPrelude.LzNil
  }
};
lambda = (undefined, function (a, b) {
  return () => {
    return lambda$(a, b)
  }
});
cichelli1 = class cichelli {
  static {
    cichelli1 = cichelli;
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, lambda11;
    tmp = NofibPrelude.nofibStringToList("case");
    tmp1 = NofibPrelude.nofibStringToList("class");
    tmp2 = NofibPrelude.nofibStringToList("data");
    tmp3 = NofibPrelude.nofibStringToList("default");
    tmp4 = NofibPrelude.nofibStringToList("deriving");
    tmp5 = NofibPrelude.nofibStringToList("else");
    tmp6 = NofibPrelude.nofibStringToList("hiding");
    tmp7 = NofibPrelude.nofibStringToList("if");
    tmp8 = NofibPrelude.nofibStringToList("import");
    tmp9 = NofibPrelude.nofibStringToList("in");
    tmp10 = NofibPrelude.nofibStringToList("infix");
    tmp11 = NofibPrelude.nofibStringToList("infixl");
    tmp12 = NofibPrelude.nofibStringToList("instance");
    tmp13 = NofibPrelude.nofibStringToList("interface");
    tmp14 = NofibPrelude.nofibStringToList("let");
    tmp15 = NofibPrelude.nofibStringToList("module");
    tmp16 = NofibPrelude.nofibStringToList("of");
    tmp17 = NofibPrelude.nofibStringToList("renaming");
    tmp18 = NofibPrelude.nofibStringToList("then");
    tmp19 = NofibPrelude.nofibStringToList("to");
    tmp20 = NofibPrelude.nofibStringToList("type");
    tmp21 = NofibPrelude.nofibStringToList("where");
    tmp22 = NofibPrelude.Cons(tmp21, NofibPrelude.Nil);
    tmp23 = NofibPrelude.Cons(tmp20, tmp22);
    tmp24 = NofibPrelude.Cons(tmp19, tmp23);
    tmp25 = NofibPrelude.Cons(tmp18, tmp24);
    tmp26 = NofibPrelude.Cons(tmp17, tmp25);
    tmp27 = NofibPrelude.Cons(tmp16, tmp26);
    tmp28 = NofibPrelude.Cons(tmp15, tmp27);
    tmp29 = NofibPrelude.Cons(tmp14, tmp28);
    tmp30 = NofibPrelude.Cons(tmp13, tmp29);
    tmp31 = NofibPrelude.Cons(tmp12, tmp30);
    tmp32 = NofibPrelude.Cons(tmp11, tmp31);
    tmp33 = NofibPrelude.Cons(tmp10, tmp32);
    tmp34 = NofibPrelude.Cons(tmp9, tmp33);
    tmp35 = NofibPrelude.Cons(tmp8, tmp34);
    tmp36 = NofibPrelude.Cons(tmp7, tmp35);
    tmp37 = NofibPrelude.Cons(tmp6, tmp36);
    tmp38 = NofibPrelude.Cons(tmp5, tmp37);
    tmp39 = NofibPrelude.Cons(tmp4, tmp38);
    tmp40 = NofibPrelude.Cons(tmp3, tmp39);
    tmp41 = NofibPrelude.Cons(tmp2, tmp40);
    tmp42 = NofibPrelude.Cons(tmp1, tmp41);
    tmp43 = NofibPrelude.Cons(tmp, tmp42);
    this.keys = tmp43;
    this.K = function K(s1, c11, c21, i1) {
      return new K.class(s1, c11, c21, i1);
    };
    this.K.class = class K {
      constructor(s, c1, c2, i) {
        this.s = s;
        this.c1 = c1;
        this.c2 = c2;
        this.i = i;
      }
      toString() { return "K(" + globalThis.Predef.render(this.s) + ", " + globalThis.Predef.render(this.c1) + ", " + globalThis.Predef.render(this.c2) + ", " + globalThis.Predef.render(this.i) + ")"; }
    };
    this.H = function H(f1, s1, ls1) {
      return new H.class(f1, s1, ls1);
    };
    this.H.class = class H {
      constructor(f, s, ls) {
        this.f = f;
        this.s = s;
        this.ls = ls;
      }
      toString() { return "H(" + globalThis.Predef.render(this.f) + ", " + globalThis.Predef.render(this.s) + ", " + globalThis.Predef.render(this.ls) + ")"; }
    };
    tmp44 = NofibPrelude.listLen(cichelli.keys);
    this.numberofkeys = tmp44;
    tmp45 = cichelli.attribkeys(cichelli.keys);
    tmp46 = NofibPrelude.map(cichelli.ends, tmp45);
    tmp47 = NofibPrelude.concat(tmp46);
    tmp48 = cichelli.histo(tmp47);
    this.freqtab = tmp48;
    tmp49 = NofibPrelude.listLen(cichelli.freqtab);
    this.maxval = tmp49;
    this.Status = class Status {
      constructor() {}
      toString() { return "Status"; }
    };
    this.NotEver = function NotEver(i1) {
      return new NotEver.class(i1);
    };
    this.NotEver.class = class NotEver extends cichelli.Status {
      constructor(i) {
        super();
        this.i = i;
      }
      toString() { return "NotEver(" + globalThis.Predef.render(this.i) + ")"; }
    };
    this.YesIts = function YesIts(i1, t1) {
      return new YesIts.class(i1, t1);
    };
    this.YesIts.class = class YesIts extends cichelli.Status {
      constructor(i, t) {
        super();
        this.i = i;
        this.t = t;
      }
      toString() { return "YesIts(" + globalThis.Predef.render(this.i) + ", " + globalThis.Predef.render(this.t) + ")"; }
    };
    lambda11 = (undefined, function () {
      let tmp50;
      tmp50 = cichelli.prog(6);
      return runtime.safeCall(tmp50.toString())
    });
    BenchmarkPrelude.benchmark(lambda11)
  }
  static enumFromTo_lz(a, b) {
    let tmp;
    tmp = runtime.safeCall(lambda(a, b));
    return NofibPrelude.lazy(tmp)
  } 
  static last(ls) {
    let param0, param1, h, t;
    if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      h = param0;
      t = param1;
      return go(h, t)
    } else {
      throw globalThis.Error("last: empty list");
    }
  } 
  static ends(k) {
    let param0, param1, param2, param3, a1, z, tmp;
    if (k instanceof cichelli.K.class) {
      param0 = k.s;
      param1 = k.c1;
      param2 = k.c2;
      param3 = k.i;
      a1 = param1;
      z = param2;
      tmp = NofibPrelude.Cons(z, NofibPrelude.Nil);
      return NofibPrelude.Cons(a1, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static assoc(x, yz) {
    let param0, param1, first1, first0, y, z, yzs, scrut;
    if (yz instanceof NofibPrelude.Cons.class) {
      param0 = yz.head;
      param1 = yz.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        y = first0;
        z = first1;
        yzs = param1;
        scrut = x === y;
        if (scrut === true) {
          return z
        } else {
          return cichelli.assoc(x, yzs)
        }
      } else {
        throw globalThis.Error("assoc: not found");
      }
    } else {
      throw globalThis.Error("assoc: not found");
    }
  } 
  static assocm(x1, yz1) {
    let param0, param1, first1, first0, y, z, yzs, scrut;
    if (yz1 instanceof NofibPrelude.Cons.class) {
      param0 = yz1.head;
      param1 = yz1.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        y = first0;
        z = first1;
        yzs = param1;
        scrut = x1 === y;
        if (scrut === true) {
          return NofibPrelude.Some(z)
        } else {
          return cichelli.assocm(x1, yzs)
        }
      } else {
        return NofibPrelude.None
      }
    } else {
      return NofibPrelude.None
    }
  } 
  static histins(x2, yns) {
    let param0, param1, first1, first0, y, n, yns1, scrut, tmp, tmp1;
    if (yns instanceof NofibPrelude.Cons.class) {
      param0 = yns.head;
      param1 = yns.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        y = first0;
        n = first1;
        yns1 = param1;
        scrut = x2 === y;
        if (scrut === true) {
          tmp = n + 1;
          return NofibPrelude.Cons([
            y,
            tmp
          ], yns1)
        } else {
          tmp1 = cichelli.histins(x2, yns1);
          return NofibPrelude.Cons([
            y,
            n
          ], tmp1)
        }
      } else {
        return NofibPrelude.Cons([
          x2,
          1
        ], NofibPrelude.Nil)
      }
    } else {
      return NofibPrelude.Cons([
        x2,
        1
      ], NofibPrelude.Nil)
    }
  } 
  static histo(ls1) {
    return NofibPrelude.foldr(cichelli.histins, NofibPrelude.Nil, ls1)
  } 
  static subset(xs, ys) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda1(ys));
    return NofibPrelude.all(lambda$this, xs)
  } 
  static union(xs1, ys1) {
    let tmp;
    tmp = lscomp$(xs1, ys1);
    return NofibPrelude.append(xs1, tmp)
  } 
  static attribkeys(ks) {
    let tmp;
    tmp = lambda2;
    return NofibPrelude.map(tmp, ks)
  } 
  static minm(x3, y) {
    let param0, x4;
    if (x3 instanceof NofibPrelude.None.class) {
      return y
    } else if (x3 instanceof NofibPrelude.Some.class) {
      param0 = x3.x;
      x4 = param0;
      return NofibPrelude.min(x4, y)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static maxm(x4, y1) {
    let param0, x5;
    if (x4 instanceof NofibPrelude.None.class) {
      return y1
    } else if (x4 instanceof NofibPrelude.Some.class) {
      param0 = x4.x;
      x5 = param0;
      return NofibPrelude.max(x5, y1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static hash(cvs, k1) {
    let param0, param1, param2, param3, a1, z, n, tmp, tmp1, tmp2;
    if (k1 instanceof cichelli.K.class) {
      param0 = k1.s;
      param1 = k1.c1;
      param2 = k1.c2;
      param3 = k1.i;
      a1 = param1;
      z = param2;
      n = param3;
      tmp = cichelli.assoc(a1, cvs);
      tmp1 = n + tmp;
      tmp2 = cichelli.assoc(z, cvs);
      return tmp1 + tmp2
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static select(p, x5, ts_fs) {
    let first1, first0, ts, fs1, scrut, tmp, tmp1;
    if (globalThis.Array.isArray(ts_fs) && ts_fs.length === 2) {
      first0 = ts_fs[0];
      first1 = ts_fs[1];
      ts = first0;
      fs1 = first1;
      scrut = runtime.safeCall(p(x5));
      if (scrut === true) {
        tmp = NofibPrelude.Cons(x5, ts);
        return [
          tmp,
          fs1
        ]
      } else {
        tmp1 = NofibPrelude.Cons(x5, fs1);
        return [
          ts,
          tmp1
        ]
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static partition_(p1, ls2) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda3(p1));
    return NofibPrelude.foldr(lambda$this, [
      NofibPrelude.Nil,
      NofibPrelude.Nil
    ], ls2)
  } 
  static freqsorted(x6) {
    return x6
  } 
  static blocked_(ds, ls3) {
    let param0, param1, k2, ks1, ds_, scrut, first1, first0, det, rest, tmp, tmp1, tmp2, tmp3, lambda$this;
    if (ls3 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls3 instanceof NofibPrelude.Cons.class) {
      param0 = ls3.head;
      param1 = ls3.tail;
      k2 = param0;
      ks1 = param1;
      tmp = cichelli.ends(k2);
      tmp1 = cichelli.union(ds, tmp);
      ds_ = tmp1;
      lambda$this = runtime.safeCall(lambda4(ds_));
      scrut = cichelli.partition_(lambda$this, ks1);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        det = first0;
        rest = first1;
        tmp2 = cichelli.blocked_(ds_, rest);
        tmp3 = NofibPrelude.append(det, tmp2);
        return NofibPrelude.Cons(k2, tmp3)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static blocked(ls4) {
    return cichelli.blocked_(NofibPrelude.Nil, ls4)
  } 
  static hinsert(h, hh) {
    let param0, param1, param2, lo, hi, hs, lo_, hi_, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    if (hh instanceof cichelli.H.class) {
      param0 = hh.f;
      param1 = hh.s;
      param2 = hh.ls;
      lo = param0;
      hi = param1;
      hs = param2;
      tmp = cichelli.minm(lo, h);
      lo_ = tmp;
      tmp1 = cichelli.maxm(hi, h);
      hi_ = tmp1;
      tmp2 = NofibPrelude.inList(h, hs);
      tmp3 = 1 + hi_;
      tmp4 = tmp3 - lo_;
      tmp5 = tmp4 > cichelli.numberofkeys;
      scrut = tmp2 || tmp5;
      if (scrut === true) {
        return NofibPrelude.None
      } else {
        tmp6 = NofibPrelude.Some(lo_);
        tmp7 = NofibPrelude.Some(hi_);
        tmp8 = NofibPrelude.Cons(h, hs);
        tmp9 = cichelli.H(tmp6, tmp7, tmp8);
        return NofibPrelude.Some(tmp9)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static first(k2, ls5) {
    let scrut, param0, param1, a1, l, param01, leaves, param02, param11, leaves1, y2, tmp, tmp1;
    scrut = NofibPrelude.force(ls5);
    if (scrut instanceof NofibPrelude.LzNil.class) {
      return cichelli.NotEver(k2)
    } else if (scrut instanceof NofibPrelude.LzCons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      a1 = param0;
      l = param1;
      if (a1 instanceof cichelli.YesIts.class) {
        param02 = a1.i;
        param11 = a1.t;
        leaves1 = param02;
        y2 = param11;
        tmp = k2 + leaves1;
        return cichelli.YesIts(tmp, y2)
      } else if (a1 instanceof cichelli.NotEver.class) {
        param01 = a1.i;
        leaves = param01;
        tmp1 = k2 + leaves;
        return cichelli.first(tmp1, l)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static firstSuccess(f, possibles) {
    let tmp;
    tmp = NofibPrelude.map_lz(f, possibles);
    return cichelli.first(0, tmp)
  } 
  static findhash_(keyHashSet, charAssocs, ks1) {
    let param0, param1, param01, param11, param2, param3, s, a1, z, n, ks2, scrut, first1, first0, param02, ac, param03, zc, ac1, zc1, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, lambda$this, lambda$this1, lambda$this2;
    if (ks1 instanceof NofibPrelude.Nil.class) {
      return cichelli.YesIts(1, charAssocs)
    } else if (ks1 instanceof NofibPrelude.Cons.class) {
      param0 = ks1.head;
      param1 = ks1.tail;
      if (param0 instanceof cichelli.K.class) {
        param01 = param0.s;
        param11 = param0.c1;
        param2 = param0.c2;
        param3 = param0.i;
        s = param01;
        a1 = param11;
        z = param2;
        n = param3;
        ks2 = param1;
        tmp = cichelli.assocm(a1, charAssocs);
        tmp1 = cichelli.assocm(z, charAssocs);
        scrut = [
          tmp,
          tmp1
        ];
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first0 = scrut[0];
          first1 = scrut[1];
          if (first0 instanceof NofibPrelude.None.class) {
            if (first1 instanceof NofibPrelude.None.class) {
              scrut1 = a1 === z;
              if (scrut1 === true) {
                tmp2 = cichelli.enumFromTo_lz(0, cichelli.maxval);
                lambda$this = runtime.safeCall(lambda5(keyHashSet, charAssocs, s, a1, z, n, ks2));
                return cichelli.firstSuccess(lambda$this, tmp2)
              } else {
                tmp3 = runtime.safeCall(lambda8(keyHashSet, charAssocs, s, a1, z, n, ks2));
                tmp4 = cichelli.enumFromTo_lz(0, cichelli.maxval);
                tmp5 = lscomp1(tmp4);
                return cichelli.firstSuccess(tmp3, tmp5)
              }
            } else if (first1 instanceof NofibPrelude.Some.class) {
              param03 = first1.x;
              zc1 = param03;
              tmp6 = cichelli.enumFromTo_lz(0, cichelli.maxval);
              lambda$this1 = runtime.safeCall(lambda9(keyHashSet, charAssocs, s, a1, z, n, ks2));
              return cichelli.firstSuccess(lambda$this1, tmp6)
            } else {
              throw new globalThis.Error("match error");
            }
          } else if (first0 instanceof NofibPrelude.Some.class) {
            param02 = first0.x;
            ac1 = param02;
            ac = param02;
            if (first1 instanceof NofibPrelude.None.class) {
              tmp7 = cichelli.enumFromTo_lz(0, cichelli.maxval);
              lambda$this2 = runtime.safeCall(lambda10(keyHashSet, charAssocs, s, a1, z, n, ks2));
              return cichelli.firstSuccess(lambda$this2, tmp7)
            } else if (first1 instanceof NofibPrelude.Some.class) {
              param03 = first1.x;
              zc = param03;
              return tryy$(keyHashSet, charAssocs, s, a1, z, n, ks2, NofibPrelude.Nil)
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
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static findhash(keys) {
    let tmp;
    tmp = cichelli.H(NofibPrelude.None, NofibPrelude.None, NofibPrelude.Nil);
    return cichelli.findhash_(tmp, NofibPrelude.Nil, keys)
  } 
  static freq(c) {
    return cichelli.assoc(c, cichelli.freqtab)
  } 
  static morefreq(k11, k21) {
    let param0, param1, param2, param3, a1, x7, param01, param11, param21, param31, b1, y2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    if (k11 instanceof cichelli.K.class) {
      param0 = k11.s;
      param1 = k11.c1;
      param2 = k11.c2;
      param3 = k11.i;
      a1 = param1;
      x7 = param2;
      if (k21 instanceof cichelli.K.class) {
        param01 = k21.s;
        param11 = k21.c1;
        param21 = k21.c2;
        param31 = k21.i;
        b1 = param11;
        y2 = param21;
        tmp = cichelli.freq(a1);
        tmp1 = cichelli.freq(x7);
        tmp2 = tmp + tmp1;
        tmp3 = cichelli.freq(b1);
        tmp4 = cichelli.freq(y2);
        tmp5 = tmp3 + tmp4;
        return tmp2 > tmp5
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static cichelli(n) {
    let attribkeys_, hashkeys, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = NofibPrelude.intMod(n, 2);
    tmp1 = NofibPrelude.take(tmp, cichelli.keys);
    tmp2 = NofibPrelude.append(cichelli.keys, tmp1);
    tmp3 = cichelli.attribkeys(tmp2);
    attribkeys_ = tmp3;
    tmp4 = cichelli.freqsorted(attribkeys_);
    tmp5 = cichelli.blocked(tmp4);
    hashkeys = tmp5;
    return cichelli.findhash(hashkeys)
  } 
  static prog(n1) {
    return cichelli.cichelli(n1)
  }
  static toString() { return "cichelli"; }
};
let cichelli = cichelli1; export default cichelli;
