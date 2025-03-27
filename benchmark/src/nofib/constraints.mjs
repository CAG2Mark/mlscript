import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let lscomp2, lscomp1, g, lscomp21, lscomp11, f1, lscomp12, next, f2, f3, lscomp22, lscomp13, lscomp23, f4, lscomp14, f5, f7, f6, lscomp15, f8, constraints1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lscomp1$, lscomp2$, lscomp1$1, lscomp2$1, lambda$, lambda$1, f1$, lambda$2, lambda$3, lambda$4, next$, lscomp1$2, lambda$5, f2$, lambda$6, f3$, lscomp1$3, lambda$7, lscomp1$4, lscomp2$2, f4$, lambda$8, lambda$9, lambda$10;
lambda$10 = function lambda$(n, x) {
  return constraints1.try_(n, x)
};
lambda13 = (undefined, function (n) {
  return (x) => {
    return lambda$10(n, x)
  }
});
lscomp15 = function lscomp1(ls) {
  let param0, param1, vs, t1, scrut, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    vs = param0;
    t1 = param1;
    scrut = NofibPrelude.all(constraints1.knownConflict, vs);
    if (scrut === true) {
      tmp = lscomp15(t1);
      return NofibPrelude.Cons(vs, tmp)
    } else {
      return lscomp15(t1)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
f8 = function f8(tp2) {
  let first1, first0, first11, first01, as_, cs, tbl, wipedDomains, cs_, scrut, tmp, tmp1, tmp2, tmp3;
  if (globalThis.Array.isArray(tp2) && tp2.length === 2) {
    first0 = tp2[0];
    first1 = tp2[1];
    if (globalThis.Array.isArray(first0) && first0.length === 2) {
      first01 = first0[0];
      first11 = first0[1];
      as_ = first01;
      cs = first11;
      tbl = first1;
      tmp = lscomp15(tbl);
      wipedDomains = tmp;
      scrut = NofibPrelude.null_(wipedDomains);
      if (scrut === true) {
        tmp1 = cs;
      } else {
        tmp2 = NofibPrelude.head(wipedDomains);
        tmp3 = constraints1.collect(tmp2);
        tmp1 = constraints1.Known(tmp3);
      }
      cs_ = tmp1;
      return [
        as_,
        cs_
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
f6 = function f6(tp2, chs) {
  let first1, first0, a, a1, param0, cs, tmp, tmp1, tmp2, tmp3;
  if (globalThis.Array.isArray(tp2) && tp2.length === 2) {
    first0 = tp2[0];
    first1 = tp2[1];
    a1 = first0;
    a = first0;
    if (first1 instanceof constraints1.Known.class) {
      param0 = first1.vs;
      cs = param0;
      tmp = constraints1.Known(cs);
      return constraints1.Node([
        a1,
        tmp
      ], chs)
    } else if (first1 instanceof constraints1.Unknown.class) {
      tmp1 = NofibPrelude.map(constraints1.label, chs);
      tmp2 = constraints1.combine(tmp1, NofibPrelude.Nil);
      tmp3 = constraints1.Known(tmp2);
      return constraints1.Node([
        a,
        tmp3
      ], chs)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
f7 = function f7(tp2, chs) {
  let first1, first0, a, cs_, scrut, a1, param0, cs, tmp, tmp1, tmp2;
  if (globalThis.Array.isArray(tp2) && tp2.length === 2) {
    first0 = tp2[0];
    first1 = tp2[1];
    a1 = first0;
    a = first0;
    if (first1 instanceof constraints1.Known.class) {
      param0 = first1.vs;
      cs = param0;
      tmp = constraints1.Known(cs);
      return constraints1.Node([
        a1,
        tmp
      ], chs)
    } else if (first1 instanceof constraints1.Unknown.class) {
      tmp1 = NofibPrelude.map(constraints1.label, chs);
      tmp2 = constraints1.combine(tmp1, NofibPrelude.Nil);
      cs_ = constraints1.Known(tmp2);
      scrut = constraints1.knownConflict(cs_);
      if (scrut === true) {
        return constraints1.Node([
          a,
          cs_
        ], NofibPrelude.Nil)
      } else {
        return constraints1.Node([
          a,
          cs_
        ], chs)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$9 = function lambda$(csp, tbl, s, x) {
  let tmp, tmp1;
  tmp = NofibPrelude.tail(tbl);
  tmp1 = constraints1.fillTable(s, csp, tmp);
  return constraints1.cacheChecks(csp, tmp1, x)
};
lambda12 = (undefined, function (csp, tbl, s) {
  return (x) => {
    return lambda$9(csp, tbl, s, x)
  }
});
f5 = function f5(csp, tp) {
  let first1, first0, param0, param1, a, as_, tbl, tableEntry, cs, scrut, tbl1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
  if (globalThis.Array.isArray(tp) && tp.length === 2) {
    first0 = tp[0];
    first1 = tp[1];
    if (first0 instanceof NofibPrelude.Nil.class) {
      tbl1 = first1;
      return [
        [
          NofibPrelude.Nil,
          constraints1.Unknown
        ],
        tbl1
      ]
    } else if (first0 instanceof NofibPrelude.Cons.class) {
      param0 = first0.head;
      param1 = first0.tail;
      a = param0;
      as_ = param1;
      tbl = first1;
      tmp = constraints1.value(a);
      tmp1 = tmp - 1;
      tmp2 = NofibPrelude.head(tbl);
      tmp3 = NofibPrelude.atIndex(tmp1, tmp2);
      tableEntry = tmp3;
      scrut = tableEntry === constraints1.Unknown;
      if (scrut === true) {
        tmp4 = NofibPrelude.Cons(a, as_);
        tmp5 = constraints1.checkComplete(csp, tmp4);
      } else {
        tmp5 = tableEntry;
      }
      cs = tmp5;
      tmp6 = NofibPrelude.Cons(a, as_);
      return [
        [
          tmp6,
          cs
        ],
        tbl
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$8 = function lambda$(csp, x) {
  return f5(csp, x)
};
lambda11 = (undefined, function (csp) {
  return (x) => {
    return lambda$8(csp, x)
  }
});
f4$ = function f4$(var_, val_, rel, cs, varval) {
  let first1, first0, varr, vall, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4;
  if (globalThis.Array.isArray(varval) && varval.length === 2) {
    first0 = varval[0];
    first1 = varval[1];
    varr = first0;
    vall = first1;
    scrut = cs === constraints1.Unknown;
    if (scrut === true) {
      tmp = constraints1.Assign(var_, val_);
      tmp1 = constraints1.Assign(varr, vall);
      tmp2 = runtime.safeCall(rel(tmp, tmp1));
      scrut1 = BenchmarkPrelude.not(tmp2);
      if (scrut1 === true) {
        tmp3 = NofibPrelude.Cons(varr, NofibPrelude.Nil);
        tmp4 = NofibPrelude.Cons(var_, tmp3);
        return constraints1.Known(tmp4)
      } else {
        return cs
      }
    } else {
      return cs
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
f4 = function f4(var_, val_, rel) {
  return (cs, varval) => {
    return f4$(var_, val_, rel, cs, varval)
  }
};
lscomp2$2 = function lscomp2$(varrr, ls) {
  let param0, param1, valll, t2, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    valll = param0;
    t2 = param1;
    tmp = lscomp2$2(varrr, t2);
    return NofibPrelude.Cons([
      varrr,
      valll
    ], tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp23 = function lscomp2(varrr) {
  return (ls) => {
    return lscomp2$2(varrr, ls)
  }
};
lscomp1$4 = function lscomp1$(vals, ls) {
  let param0, param1, varrr, t1, tmp, tmp1, tmp2;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    varrr = param0;
    t1 = param1;
    tmp = NofibPrelude.enumFromTo(1, vals);
    tmp1 = lscomp2$2(varrr, tmp);
    tmp2 = lscomp1$4(vals, t1);
    return NofibPrelude.Cons(tmp1, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp14 = function lscomp1(vals) {
  return (ls) => {
    return lscomp1$4(vals, ls)
  }
};
lambda$7 = function lambda$(var_, val_, rel, x, y) {
  let f4$this;
  f4$this = runtime.safeCall(f4(var_, val_, rel));
  return NofibPrelude.zipWith(f4$this, x, y)
};
lambda10 = (undefined, function (var_, val_, rel) {
  return (x, y) => {
    return lambda$7(var_, val_, rel, x, y)
  }
});
lscomp22 = function lscomp2(ls) {
  let param0, param1, m, t2, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    m = param0;
    t2 = param1;
    tmp = lscomp22(t2);
    return NofibPrelude.Cons(constraints1.Unknown, tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp1$3 = function lscomp1$(vals, ls) {
  let param0, param1, n, t1, tmp, tmp1, tmp2;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    n = param0;
    t1 = param1;
    tmp = NofibPrelude.enumFromTo(1, vals);
    tmp1 = lscomp22(tmp);
    tmp2 = lscomp1$3(vals, t1);
    return NofibPrelude.Cons(tmp1, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp13 = function lscomp1(vals) {
  return (ls) => {
    return lscomp1$3(vals, ls)
  }
};
f3$ = function f3$(csp, s) {
  let scrut, param0, first1, first0, a, b, tmp, tmp1, tmp2;
  scrut = constraints1.earliestInconsistency(csp, s);
  if (scrut instanceof NofibPrelude.Some.class) {
    param0 = scrut.x;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      a = first0;
      b = first1;
      tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
      tmp1 = NofibPrelude.Cons(a, tmp);
      tmp2 = constraints1.Known(tmp1);
    } else {
      tmp2 = constraints1.checkComplete(csp, s);
    }
  } else {
    tmp2 = constraints1.checkComplete(csp, s);
  }
  return [
    s,
    tmp2
  ]
};
f3 = function f3(csp) {
  return (s) => {
    return f3$(csp, s)
  }
};
lambda8 = (undefined, function (x) {
  let tmp;
  tmp = NofibPrelude.snd(x);
  return constraints1.knownConflict(tmp)
});
lambda9 = (undefined, function (x) {
  let tmp;
  tmp = NofibPrelude.snd(x);
  return constraints1.knownSolution(tmp)
});
lambda6 = (undefined, function (x) {
  let tmp, tmp1;
  tmp = NofibPrelude.snd(x);
  tmp1 = tmp === NofibPrelude.None;
  return BenchmarkPrelude.not(tmp1)
});
lambda$6 = function lambda$(csp, x) {
  return constraints1.complete(csp, x)
};
lambda7 = (undefined, function (csp) {
  return (x) => {
    return lambda$6(csp, x)
  }
});
f2$ = function f2$(csp, s) {
  let tmp;
  tmp = constraints1.earliestInconsistency(csp, s);
  return [
    s,
    tmp
  ]
};
f2 = function f2(csp) {
  return (s) => {
    return f2$(csp, s)
  }
};
lambda$5 = function lambda$(rel, a, x) {
  let tmp;
  tmp = runtime.safeCall(rel(a, x));
  return BenchmarkPrelude.not(tmp)
};
lambda5 = (undefined, function (rel, a) {
  return (x) => {
    return lambda$5(rel, a, x)
  }
});
lscomp1$2 = function lscomp1$(ss, ls) {
  let param0, param1, j, t1, tmp, tmp1, tmp2, tmp3, tmp4;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    j = param0;
    t1 = param1;
    tmp = constraints1.maxLevel(ss);
    tmp1 = tmp + 1;
    tmp2 = constraints1.Assign(tmp1, j);
    tmp3 = NofibPrelude.Cons(tmp2, ss);
    tmp4 = lscomp1$2(ss, t1);
    return NofibPrelude.Cons(tmp3, tmp4)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp12 = function lscomp1(ss) {
  return (ls) => {
    return lscomp1$2(ss, ls)
  }
};
next$ = function next$(vars, vals, ss) {
  let scrut, tmp, tmp1;
  tmp = constraints1.maxLevel(ss);
  scrut = tmp < vars;
  if (scrut === true) {
    tmp1 = NofibPrelude.enumFromTo(1, vals);
    return lscomp1$2(ss, tmp1)
  } else {
    return NofibPrelude.Nil
  }
};
next = function next(vars, vals) {
  return (ss) => {
    return next$(vars, vals, ss)
  }
};
lambda$4 = function lambda$(f, y) {
  return constraints1.initTree(f, y)
};
lambda4 = (undefined, function (f) {
  return (y) => {
    return lambda$4(f, y)
  }
});
lambda$3 = function lambda$(p, x) {
  let tmp;
  tmp = runtime.safeCall(p(x));
  return BenchmarkPrelude.not(tmp)
};
lambda3 = (undefined, function (p) {
  return (x) => {
    return lambda$3(p, x)
  }
});
lambda$2 = function lambda$(p, x) {
  let tmp;
  tmp = constraints1.label(x);
  return runtime.safeCall(p(tmp))
};
lambda2 = (undefined, function (p) {
  return (x) => {
    return lambda$2(p, x)
  }
});
f1$ = function f1$(p, a, cs) {
  let tmp, lambda$this;
  lambda$this = runtime.safeCall(lambda2(p));
  tmp = NofibPrelude.filter(lambda$this, cs);
  return constraints1.Node(a, tmp)
};
f1 = function f1(p) {
  return (a, cs) => {
    return f1$(p, a, cs)
  }
};
lambda$1 = function lambda$(f, x) {
  return constraints1.foldTree(f, x)
};
lambda1 = (undefined, function (f) {
  return (x) => {
    return lambda$1(f, x)
  }
});
lambda$ = function lambda$(f, x) {
  return constraints1.mapTree(f, x)
};
lambda = (undefined, function (f) {
  return (x) => {
    return lambda$(f, x)
  }
});
lscomp2$1 = function lscomp2$(as_, rel, a, t1, ls) {
  let param0, param1, b, t2, scrut, scrut1, tmp, tmp1, tmp2;
  if (ls instanceof NofibPrelude.Nil.class) {
    return lscomp1$1(as_, rel, t1)
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    b = param0;
    t2 = param1;
    scrut = a > b;
    if (scrut === true) {
      tmp = runtime.safeCall(rel(a, b));
      scrut1 = BenchmarkPrelude.not(tmp);
      if (scrut1 === true) {
        tmp1 = constraints1.level(a);
        tmp2 = lscomp2$1(as_, rel, a, t1, t2);
        return NofibPrelude.Cons([
          tmp1,
          b
        ], tmp2)
      } else {
        return lscomp2$1(as_, rel, a, t1, t2)
      }
    } else {
      return lscomp2$1(as_, rel, a, t1, t2)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp21 = function lscomp2(as_, rel, a, t1) {
  return (ls) => {
    return lscomp2$1(as_, rel, a, t1, ls)
  }
};
lscomp1$1 = function lscomp1$(as_, rel, ls) {
  let param0, param1, a, t1, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    a = param0;
    t1 = param1;
    tmp = NofibPrelude.reverse(as_);
    return lscomp2$1(as_, rel, a, t1, tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp11 = function lscomp1(as_, rel) {
  return (ls) => {
    return lscomp1$1(as_, rel, ls)
  }
};
lscomp2$ = function lscomp2$(vals, var_, val_, t1, ls) {
  let param0, param1, st, t2, tmp, tmp1, tmp2;
  if (ls instanceof NofibPrelude.Nil.class) {
    return lscomp1$(vals, var_, t1)
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    st = param0;
    t2 = param1;
    tmp = constraints1.Assign(var_, val_);
    tmp1 = NofibPrelude.Cons(tmp, st);
    tmp2 = lscomp2$(vals, var_, val_, t1, t2);
    return NofibPrelude.Cons(tmp1, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp2 = function lscomp2(vals, var_, val_, t1) {
  return (ls) => {
    return lscomp2$(vals, var_, val_, t1, ls)
  }
};
lscomp1$ = function lscomp1$(vals, var_, ls) {
  let param0, param1, val_, t1, tmp, tmp1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    val_ = param0;
    t1 = param1;
    tmp = var_ - 1;
    tmp1 = g(vals, tmp);
    return lscomp2$(vals, var_, val_, t1, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp1 = function lscomp1(vals, var_) {
  return (ls) => {
    return lscomp1$(vals, var_, ls)
  }
};
g = function g(vals, var_) {
  let scrut, tmp;
  scrut = var_ == 0;
  if (scrut === true) {
    return NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil)
  } else {
    tmp = NofibPrelude.enumFromTo(1, vals);
    return lscomp1$(vals, var_, tmp)
  }
};
constraints1 = class constraints {
  static {
    constraints1 = constraints;
    let lambda14;
    this.Assign = function Assign(varr1, value1) {
      return new Assign.class(varr1, value1);
    };
    this.Assign.class = class Assign {
      constructor(varr, value) {
        this.varr = varr;
        this.value = value;
      }
      toString() { return "Assign(" + globalThis.Predef.render(this.varr) + ", " + globalThis.Predef.render(this.value) + ")"; }
    };
    this.CSP = function CSP(vars1, vals1, rel1) {
      return new CSP.class(vars1, vals1, rel1);
    };
    this.CSP.class = class CSP {
      constructor(vars, vals, rel) {
        this.vars = vars;
        this.vals = vals;
        this.rel = rel;
      }
      toString() { return "CSP(" + globalThis.Predef.render(this.vars) + ", " + globalThis.Predef.render(this.vals) + ", " + globalThis.Predef.render(this.rel) + ")"; }
    };
    this.Node = function Node(lab1, children1) {
      return new Node.class(lab1, children1);
    };
    this.Node.class = class Node {
      constructor(lab, children) {
        this.lab = lab;
        this.children = children;
      }
      toString() { return "Node(" + globalThis.Predef.render(this.lab) + ", " + globalThis.Predef.render(this.children) + ")"; }
    };
    this.ConflictSet = class ConflictSet {
      constructor() {}
      toString() { return "ConflictSet"; }
    };
    this.Known = function Known(vs1) {
      return new Known.class(vs1);
    };
    this.Known.class = class Known extends constraints.ConflictSet {
      constructor(vs) {
        super();
        this.vs = vs;
      }
      toString() { return "Known(" + globalThis.Predef.render(this.vs) + ")"; }
    };
    const Unknown$class = class Unknown extends constraints.ConflictSet {
      constructor() {
        super();
      }
      toString() { return "Unknown"; }
    };
    this.Unknown = new Unknown$class;
    this.Unknown.class = Unknown$class;
    lambda14 = (undefined, function () {
      let tmp;
      tmp = constraints.testConstraints_nofib(6);
      return runtime.safeCall(tmp.toString())
    });
    BenchmarkPrelude.benchmark(lambda14)
  }
  static qsort(le, ls, r) {
    let param0, param1, x, xs, x1;
    if (ls instanceof NofibPrelude.Nil.class) {
      return r
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x1 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Cons(x1, r)
      } else {
        x = param0;
        xs = param1;
        return constraints.qpart(le, x, xs, NofibPrelude.Nil, NofibPrelude.Nil, r)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static qpart(le1, x, ls1, rlt, rge, r1) {
    let param0, param1, y, ys, scrut, tmp, tmp1, tmp2, tmp3;
    if (ls1 instanceof NofibPrelude.Nil.class) {
      tmp = constraints.rqsort(le1, rge, r1);
      tmp1 = NofibPrelude.Cons(x, tmp);
      return constraints.rqsort(le1, rlt, tmp1)
    } else if (ls1 instanceof NofibPrelude.Cons.class) {
      param0 = ls1.head;
      param1 = ls1.tail;
      y = param0;
      ys = param1;
      scrut = runtime.safeCall(le1(x, y));
      if (scrut === true) {
        tmp2 = NofibPrelude.Cons(y, rge);
        return constraints.qpart(le1, x, ys, rlt, tmp2, r1)
      } else {
        tmp3 = NofibPrelude.Cons(y, rlt);
        return constraints.qpart(le1, x, ys, tmp3, rge, r1)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static rqsort(le2, ls2, r2) {
    let param0, param1, x1, xs, x2;
    if (ls2 instanceof NofibPrelude.Nil.class) {
      return r2
    } else if (ls2 instanceof NofibPrelude.Cons.class) {
      param0 = ls2.head;
      param1 = ls2.tail;
      x2 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Cons(x2, r2)
      } else {
        x1 = param0;
        xs = param1;
        return constraints.rqpart(le2, x1, xs, NofibPrelude.Nil, NofibPrelude.Nil, r2)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static rqpart(le3, x1, ls3, rle, rgt, r3) {
    let param0, param1, y, ys, scrut, tmp, tmp1, tmp2, tmp3;
    if (ls3 instanceof NofibPrelude.Nil.class) {
      tmp = constraints.qsort(le3, rgt, r3);
      tmp1 = NofibPrelude.Cons(x1, tmp);
      return constraints.rqsort(le3, rle, tmp1)
    } else if (ls3 instanceof NofibPrelude.Cons.class) {
      param0 = ls3.head;
      param1 = ls3.tail;
      y = param0;
      ys = param1;
      scrut = runtime.safeCall(le3(y, x1));
      if (scrut === true) {
        tmp2 = NofibPrelude.Cons(y, rle);
        return constraints.rqpart(le3, x1, ys, tmp2, rgt, r3)
      } else {
        tmp3 = NofibPrelude.Cons(y, rgt);
        return constraints.rqpart(le3, x1, ys, rle, tmp3, r3)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static level(a) {
    let param0, param1, v;
    if (a instanceof constraints.Assign.class) {
      param0 = a.varr;
      param1 = a.value;
      v = param0;
      return v
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static value(a1) {
    let param0, param1, v;
    if (a1 instanceof constraints.Assign.class) {
      param0 = a1.varr;
      param1 = a1.value;
      v = param1;
      return v
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static maxLevel(ls4) {
    let param0, param1, param01, param11, v, t;
    if (ls4 instanceof NofibPrelude.Nil.class) {
      return 0
    } else if (ls4 instanceof NofibPrelude.Cons.class) {
      param0 = ls4.head;
      param1 = ls4.tail;
      if (param0 instanceof constraints.Assign.class) {
        param01 = param0.varr;
        param11 = param0.value;
        v = param01;
        t = param1;
        return v
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static complete(csp, s) {
    let param0, param1, param2, v, tmp;
    if (csp instanceof constraints.CSP.class) {
      param0 = csp.vars;
      param1 = csp.vals;
      param2 = csp.rel;
      v = param0;
      tmp = constraints.maxLevel(s);
      return tmp == v
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static generate(csp1) {
    let param0, param1, param2, vars, vals, rel;
    if (csp1 instanceof constraints.CSP.class) {
      param0 = csp1.vars;
      param1 = csp1.vals;
      param2 = csp1.rel;
      vars = param0;
      vals = param1;
      rel = param2;
      return g(vals, vars)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static inconsistencies(csp2, as_) {
    let param0, param1, param2, vars, vals, rel;
    if (csp2 instanceof constraints.CSP.class) {
      param0 = csp2.vars;
      param1 = csp2.vals;
      param2 = csp2.rel;
      vars = param0;
      vals = param1;
      rel = param2;
      return lscomp1$1(as_, rel, as_)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static consistent(csp3, x2) {
    let tmp;
    tmp = constraints.inconsistencies(csp3, x2);
    return NofibPrelude.null_(tmp)
  } 
  static test(csp4) {
    let tmp;
    tmp = constraints.consistent(csp4);
    return NofibPrelude.filter(tmp)
  } 
  static solver(csp5) {
    let tmp;
    tmp = constraints.generate(csp5);
    return constraints.test(csp5, tmp)
  } 
  static safe(as1, as2) {
    let param0, param1, i, m, param01, param11, j, n, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    if (as1 instanceof constraints.Assign.class) {
      param0 = as1.varr;
      param1 = as1.value;
      i = param0;
      m = param1;
      if (as2 instanceof constraints.Assign.class) {
        param01 = as2.varr;
        param11 = as2.value;
        j = param01;
        n = param11;
        tmp = m == n;
        scrut = BenchmarkPrelude.not(tmp);
        if (scrut === true) {
          tmp1 = i - j;
          tmp2 = NofibPrelude.abs(tmp1);
          tmp3 = m - n;
          tmp4 = NofibPrelude.abs(tmp3);
          tmp5 = tmp2 == tmp4;
          scrut1 = BenchmarkPrelude.not(tmp5);
          if (scrut1 === true) {
            return true
          } else {
            return false
          }
        } else {
          return false
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static queens(n) {
    return constraints.CSP(n, n, constraints.safe)
  } 
  static label(n1) {
    let param0, param1, l;
    if (n1 instanceof constraints.Node.class) {
      param0 = n1.lab;
      param1 = n1.children;
      l = param0;
      return l
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static mapTree(f, n2) {
    let param0, param1, l, c, tmp, tmp1, lambda$this;
    if (n2 instanceof constraints.Node.class) {
      param0 = n2.lab;
      param1 = n2.children;
      l = param0;
      c = param1;
      tmp = runtime.safeCall(f(l));
      lambda$this = runtime.safeCall(lambda(f));
      tmp1 = NofibPrelude.map(lambda$this, c);
      return constraints.Node(tmp, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static foldTree(f9, n3) {
    let param0, param1, l, c, tmp, lambda$this;
    if (n3 instanceof constraints.Node.class) {
      param0 = n3.lab;
      param1 = n3.children;
      l = param0;
      c = param1;
      lambda$this = runtime.safeCall(lambda1(f9));
      tmp = NofibPrelude.map(lambda$this, c);
      return runtime.safeCall(f9(l, tmp))
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static filterTree(p, t) {
    let f1$this;
    f1$this = runtime.safeCall(f1(p));
    return constraints.foldTree(f1$this, t)
  } 
  static prune(p1, t1) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda3(p1));
    return constraints.filterTree(lambda$this, t1)
  } 
  static leaves(t2) {
    let param0, param1, cs, leaf, tmp;
    if (t2 instanceof constraints.Node.class) {
      param0 = t2.lab;
      param1 = t2.children;
      leaf = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Cons(leaf, NofibPrelude.Nil)
      } else {
        cs = param1;
        tmp = NofibPrelude.map(constraints.leaves, cs);
        return NofibPrelude.concat(tmp)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static initTree(f10, x3) {
    let tmp, tmp1, lambda$this;
    tmp = runtime.safeCall(f10(x3));
    lambda$this = runtime.safeCall(lambda4(f10));
    tmp1 = NofibPrelude.map(lambda$this, tmp);
    return constraints.Node(x3, tmp1)
  } 
  static mkTree(csp6) {
    let param0, param1, param2, vars, vals, rel, next$this;
    if (csp6 instanceof constraints.CSP.class) {
      param0 = csp6.vars;
      param1 = csp6.vals;
      param2 = csp6.rel;
      vars = param0;
      vals = param1;
      rel = param2;
      next$this = runtime.safeCall(next(vars, vals));
      return constraints.initTree(next$this, NofibPrelude.Nil)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static earliestInconsistency(csp7, aas) {
    let param0, param1, param2, vars, vals, rel, param01, param11, a2, as_1, scrut, param02, param12, b, tmp, tmp1, tmp2, lambda$this;
    if (csp7 instanceof constraints.CSP.class) {
      param0 = csp7.vars;
      param1 = csp7.vals;
      param2 = csp7.rel;
      vars = param0;
      vals = param1;
      rel = param2;
      if (aas instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.None
      } else if (aas instanceof NofibPrelude.Cons.class) {
        param01 = aas.head;
        param11 = aas.tail;
        a2 = param01;
        as_1 = param11;
        tmp = NofibPrelude.reverse(as_1);
        lambda$this = runtime.safeCall(lambda5(rel, a2));
        scrut = NofibPrelude.filter(lambda$this, tmp);
        if (scrut instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.None
        } else if (scrut instanceof NofibPrelude.Cons.class) {
          param02 = scrut.head;
          param12 = scrut.tail;
          b = param02;
          tmp1 = constraints.level(a2);
          tmp2 = constraints.level(b);
          return NofibPrelude.Some([
            tmp1,
            tmp2
          ])
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
  static labelInconsistencies(csp8, t3) {
    let f2$this;
    f2$this = runtime.safeCall(f2(csp8));
    return constraints.mapTree(f2$this, t3)
  } 
  static btsolver0(csp9) {
    let tmp, tmp1, tmp2, tmp3, tmp4, lambda$this;
    tmp = constraints.mkTree(csp9);
    tmp1 = constraints.labelInconsistencies(csp9, tmp);
    tmp2 = constraints.prune(lambda6, tmp1);
    tmp3 = constraints.mapTree(NofibPrelude.fst, tmp2);
    tmp4 = constraints.leaves(tmp3);
    lambda$this = runtime.safeCall(lambda7(csp9));
    return NofibPrelude.filter(lambda$this, tmp4)
  } 
  static knownConflict(c) {
    let param0, param01, param1, a2, as_1;
    if (c instanceof constraints.Known.class) {
      param0 = c.vs;
      if (param0 instanceof NofibPrelude.Cons.class) {
        param01 = param0.head;
        param1 = param0.tail;
        a2 = param01;
        as_1 = param1;
        return true
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static knownSolution(c1) {
    let param0;
    if (c1 instanceof constraints.Known.class) {
      param0 = c1.vs;
      if (param0 instanceof NofibPrelude.Nil.class) {
        return true
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static checkComplete(csp10, s1) {
    let scrut;
    scrut = constraints.complete(csp10, s1);
    if (scrut === true) {
      return constraints.Known(NofibPrelude.Nil)
    } else {
      return constraints.Unknown
    }
  } 
  static search(labeler, csp11) {
    let tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = constraints.mkTree(csp11);
    tmp1 = runtime.safeCall(labeler(csp11, tmp));
    tmp2 = constraints.prune(lambda8, tmp1);
    tmp3 = constraints.leaves(tmp2);
    tmp4 = NofibPrelude.filter(lambda9, tmp3);
    return NofibPrelude.map(NofibPrelude.fst, tmp4)
  } 
  static bt(csp12, t4) {
    let f3$this;
    f3$this = runtime.safeCall(f3(csp12));
    return constraints.mapTree(f3$this, t4)
  } 
  static emptyTable(csp13) {
    let param0, param1, param2, vars, vals, rel, tmp, tmp1;
    if (csp13 instanceof constraints.CSP.class) {
      param0 = csp13.vars;
      param1 = csp13.vals;
      param2 = csp13.rel;
      vars = param0;
      vals = param1;
      rel = param2;
      tmp = NofibPrelude.enumFromTo(1, vars);
      tmp1 = lscomp1$3(vals, tmp);
      return NofibPrelude.Cons(NofibPrelude.Nil, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static fillTable(s2, csp14, tbl) {
    let param0, param1, param01, param11, var_, val_, as_1, param02, param12, param2, vars, vals, rel, tmp, tmp1, tmp2, lambda$this;
    if (s2 instanceof NofibPrelude.Nil.class) {
      return tbl
    } else if (s2 instanceof NofibPrelude.Cons.class) {
      param0 = s2.head;
      param1 = s2.tail;
      if (param0 instanceof constraints.Assign.class) {
        param01 = param0.varr;
        param11 = param0.value;
        var_ = param01;
        val_ = param11;
        as_1 = param1;
        if (csp14 instanceof constraints.CSP.class) {
          param02 = csp14.vars;
          param12 = csp14.vals;
          param2 = csp14.rel;
          vars = param02;
          vals = param12;
          rel = param2;
          tmp = var_ + 1;
          tmp1 = NofibPrelude.enumFromTo(tmp, vars);
          tmp2 = lscomp1$4(vals, tmp1);
          lambda$this = runtime.safeCall(lambda10(var_, val_, rel));
          return NofibPrelude.zipWith(lambda$this, tbl, tmp2)
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
  static lookupCache(csp15, t5) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda11(csp15));
    return constraints.mapTree(lambda$this, t5)
  } 
  static cacheChecks(csp16, tbl1, n4) {
    let param0, param1, s3, cs, tmp, tmp1;
    if (n4 instanceof constraints.Node.class) {
      param0 = n4.lab;
      param1 = n4.children;
      s3 = param0;
      cs = param1;
      tmp = runtime.safeCall(lambda12(csp16, tbl1, s3));
      tmp1 = NofibPrelude.map(tmp, cs);
      return constraints.Node([
        s3,
        tbl1
      ], tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static bm(csp17, t6) {
    let tmp, tmp1, tmp2;
    tmp = constraints.emptyTable(csp17);
    tmp1 = constraints.cacheChecks(csp17, tmp, t6);
    tmp2 = constraints.lookupCache(csp17, tmp1);
    return constraints.mapTree(NofibPrelude.fst, tmp2)
  } 
  static combine(ls5, acc) {
    let param0, param1, first1, first0, s3, param01, cs, css, scrut, tmp, tmp1;
    if (ls5 instanceof NofibPrelude.Nil.class) {
      return acc
    } else if (ls5 instanceof NofibPrelude.Cons.class) {
      param0 = ls5.head;
      param1 = ls5.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        s3 = first0;
        if (first1 instanceof constraints.Known.class) {
          param01 = first1.vs;
          cs = param01;
          css = param1;
          tmp = constraints.maxLevel(s3);
          scrut = NofibPrelude.notElem(tmp, cs);
          if (scrut === true) {
            return cs
          } else {
            tmp1 = NofibPrelude.union(cs, acc);
            return constraints.combine(css, tmp1)
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
  static bj_(csp18, t7) {
    return constraints.foldTree(f7, t7)
  } 
  static bj(csp19, t8) {
    return constraints.foldTree(f6, t8)
  } 
  static bjbt(csp20, t9) {
    let tmp;
    tmp = constraints.bt(csp20, t9);
    return constraints.bj(csp20, tmp)
  } 
  static bjbt_(csp21, t10) {
    let tmp;
    tmp = constraints.bt(csp21, t10);
    return constraints.bj_(csp21, tmp)
  } 
  static collect(ls6) {
    let param0, param1, param01, cs, css, tmp;
    if (ls6 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls6 instanceof NofibPrelude.Cons.class) {
      param0 = ls6.head;
      param1 = ls6.tail;
      if (param0 instanceof constraints.Known.class) {
        param01 = param0.vs;
        cs = param01;
        css = param1;
        tmp = constraints.collect(css);
        return NofibPrelude.union(cs, tmp)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static domainWipeout(csp22, t11) {
    let param0, param1, param2, vars, vals, rel;
    if (csp22 instanceof constraints.CSP.class) {
      param0 = csp22.vars;
      param1 = csp22.vals;
      param2 = csp22.rel;
      vars = param0;
      vals = param1;
      rel = param2;
      return constraints.mapTree(f8, t11)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static fc(csp23, t12) {
    let tmp, tmp1, tmp2;
    tmp = constraints.emptyTable(csp23);
    tmp1 = constraints.cacheChecks(csp23, tmp, t12);
    tmp2 = constraints.lookupCache(csp23, tmp1);
    return constraints.domainWipeout(csp23, tmp2)
  } 
  static try_(n5, algorithm) {
    let tmp, tmp1;
    tmp = constraints.queens(n5);
    tmp1 = constraints.search(algorithm, tmp);
    return NofibPrelude.listLen(tmp1)
  } 
  static testConstraints_nofib(n6) {
    let tmp, tmp1, tmp2, tmp3, tmp4, lambda$this;
    tmp = NofibPrelude.Cons(constraints.fc, NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons(constraints.bjbt_, tmp);
    tmp2 = NofibPrelude.Cons(constraints.bjbt, tmp1);
    tmp3 = NofibPrelude.Cons(constraints.bm, tmp2);
    tmp4 = NofibPrelude.Cons(constraints.bt, tmp3);
    lambda$this = runtime.safeCall(lambda13(n6));
    return NofibPrelude.map(lambda$this, tmp4)
  }
  static toString() { return "constraints"; }
};
let constraints = constraints1; export default constraints;
