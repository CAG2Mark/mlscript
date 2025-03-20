import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let constraints1;
constraints1 = class constraints {
  static {
    let lambda;
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
    lambda = (undefined, function () {
      let tmp;
      tmp = constraints.testConstraints_nofib(6);
      return runtime.safeCall(tmp.toString())
    });
    BenchmarkPrelude.benchmark(lambda)
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
    let g, param0, param1, param2, vars, vals, rel;
    g = function g(vals1, var_) {
      let lscomp1, scrut, tmp;
      lscomp1 = function lscomp1(ls5) {
        let lscomp2, param01, param11, val_, t1, tmp1, tmp2;
        if (ls5 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (ls5 instanceof NofibPrelude.Cons.class) {
          param01 = ls5.head;
          param11 = ls5.tail;
          val_ = param01;
          t1 = param11;
          lscomp2 = function lscomp2(ls6) {
            let param02, param12, st, t2, tmp3, tmp4, tmp5;
            if (ls6 instanceof NofibPrelude.Nil.class) {
              return lscomp1(t1)
            } else if (ls6 instanceof NofibPrelude.Cons.class) {
              param02 = ls6.head;
              param12 = ls6.tail;
              st = param02;
              t2 = param12;
              tmp3 = constraints.Assign(var_, val_);
              tmp4 = NofibPrelude.Cons(tmp3, st);
              tmp5 = lscomp2(t2);
              return NofibPrelude.Cons(tmp4, tmp5)
            } else {
              throw new globalThis.Error("match error");
            }
          };
          tmp1 = var_ - 1;
          tmp2 = g(vals1, tmp1);
          return lscomp2(tmp2)
        } else {
          throw new globalThis.Error("match error");
        }
      };
      scrut = var_ == 0;
      if (scrut === true) {
        return NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil)
      } else {
        tmp = NofibPrelude.enumFromTo(1, vals1);
        return lscomp1(tmp)
      }
    };
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
    let lscomp1, param0, param1, param2, vars, vals, rel;
    if (csp2 instanceof constraints.CSP.class) {
      param0 = csp2.vars;
      param1 = csp2.vals;
      param2 = csp2.rel;
      vars = param0;
      vals = param1;
      rel = param2;
      lscomp1 = function lscomp1(ls5) {
        let lscomp2, param01, param11, a2, t1, tmp;
        if (ls5 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (ls5 instanceof NofibPrelude.Cons.class) {
          param01 = ls5.head;
          param11 = ls5.tail;
          a2 = param01;
          t1 = param11;
          lscomp2 = function lscomp2(ls6) {
            let param02, param12, b, t2, scrut, scrut1, tmp1, tmp2, tmp3;
            if (ls6 instanceof NofibPrelude.Nil.class) {
              return lscomp1(t1)
            } else if (ls6 instanceof NofibPrelude.Cons.class) {
              param02 = ls6.head;
              param12 = ls6.tail;
              b = param02;
              t2 = param12;
              scrut = a2 > b;
              if (scrut === true) {
                tmp1 = runtime.safeCall(rel(a2, b));
                scrut1 = BenchmarkPrelude.not(tmp1);
                if (scrut1 === true) {
                  tmp2 = constraints.level(a2);
                  tmp3 = lscomp2(t2);
                  return NofibPrelude.Cons([
                    tmp2,
                    b
                  ], tmp3)
                } else {
                  return lscomp2(t2)
                }
              } else {
                return lscomp2(t2)
              }
            } else {
              throw new globalThis.Error("match error");
            }
          };
          tmp = NofibPrelude.reverse(as_);
          return lscomp2(tmp)
        } else {
          throw new globalThis.Error("match error");
        }
      };
      return lscomp1(as_)
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
    let param0, param1, l, c, tmp, tmp1, lambda;
    if (n2 instanceof constraints.Node.class) {
      param0 = n2.lab;
      param1 = n2.children;
      l = param0;
      c = param1;
      tmp = runtime.safeCall(f(l));
      lambda = (undefined, function (x3) {
        return constraints.mapTree(f, x3)
      });
      tmp1 = NofibPrelude.map(lambda, c);
      return constraints.Node(tmp, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static foldTree(f1, n3) {
    let param0, param1, l, c, tmp, lambda;
    if (n3 instanceof constraints.Node.class) {
      param0 = n3.lab;
      param1 = n3.children;
      l = param0;
      c = param1;
      lambda = (undefined, function (x3) {
        return constraints.foldTree(f1, x3)
      });
      tmp = NofibPrelude.map(lambda, c);
      return runtime.safeCall(f1(l, tmp))
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static filterTree(p, t) {
    let f11;
    f11 = function f1(a2, cs) {
      let tmp, lambda;
      lambda = (undefined, function (x3) {
        let tmp1;
        tmp1 = constraints.label(x3);
        return runtime.safeCall(p(tmp1))
      });
      tmp = NofibPrelude.filter(lambda, cs);
      return constraints.Node(a2, tmp)
    };
    return constraints.foldTree(f11, t)
  } 
  static prune(p1, t1) {
    let lambda;
    lambda = (undefined, function (x3) {
      let tmp;
      tmp = runtime.safeCall(p1(x3));
      return BenchmarkPrelude.not(tmp)
    });
    return constraints.filterTree(lambda, t1)
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
  static initTree(f2, x3) {
    let tmp, tmp1, lambda;
    tmp = runtime.safeCall(f2(x3));
    lambda = (undefined, function (y) {
      return constraints.initTree(f2, y)
    });
    tmp1 = NofibPrelude.map(lambda, tmp);
    return constraints.Node(x3, tmp1)
  } 
  static mkTree(csp6) {
    let next, param0, param1, param2, vars, vals, rel;
    if (csp6 instanceof constraints.CSP.class) {
      param0 = csp6.vars;
      param1 = csp6.vals;
      param2 = csp6.rel;
      vars = param0;
      vals = param1;
      rel = param2;
      next = function next(ss) {
        let lscomp1, scrut, tmp, tmp1;
        tmp = constraints.maxLevel(ss);
        scrut = tmp < vars;
        if (scrut === true) {
          lscomp1 = function lscomp1(ls5) {
            let param01, param11, j, t11, tmp2, tmp3, tmp4, tmp5, tmp6;
            if (ls5 instanceof NofibPrelude.Nil.class) {
              return NofibPrelude.Nil
            } else if (ls5 instanceof NofibPrelude.Cons.class) {
              param01 = ls5.head;
              param11 = ls5.tail;
              j = param01;
              t11 = param11;
              tmp2 = constraints.maxLevel(ss);
              tmp3 = tmp2 + 1;
              tmp4 = constraints.Assign(tmp3, j);
              tmp5 = NofibPrelude.Cons(tmp4, ss);
              tmp6 = lscomp1(t11);
              return NofibPrelude.Cons(tmp5, tmp6)
            } else {
              throw new globalThis.Error("match error");
            }
          };
          tmp1 = NofibPrelude.enumFromTo(1, vals);
          return lscomp1(tmp1)
        } else {
          return NofibPrelude.Nil
        }
      };
      return constraints.initTree(next, NofibPrelude.Nil)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static earliestInconsistency(csp7, aas) {
    let param0, param1, param2, vars, vals, rel, param01, param11, a2, as_1, scrut, param02, param12, b, tmp, tmp1, tmp2, lambda;
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
        lambda = (undefined, function (x4) {
          let tmp3;
          tmp3 = runtime.safeCall(rel(a2, x4));
          return BenchmarkPrelude.not(tmp3)
        });
        scrut = NofibPrelude.filter(lambda, tmp);
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
    let f21;
    f21 = function f2(s1) {
      let tmp;
      tmp = constraints.earliestInconsistency(csp8, s1);
      return [
        s1,
        tmp
      ]
    };
    return constraints.mapTree(f21, t3)
  } 
  static btsolver0(csp9) {
    let tmp, tmp1, tmp2, tmp3, tmp4, lambda, lambda1;
    tmp = constraints.mkTree(csp9);
    tmp1 = constraints.labelInconsistencies(csp9, tmp);
    lambda = (undefined, function (x4) {
      let tmp5, tmp6;
      tmp5 = NofibPrelude.snd(x4);
      tmp6 = tmp5 === NofibPrelude.None;
      return BenchmarkPrelude.not(tmp6)
    });
    tmp2 = constraints.prune(lambda, tmp1);
    tmp3 = constraints.mapTree(NofibPrelude.fst, tmp2);
    tmp4 = constraints.leaves(tmp3);
    lambda1 = (undefined, function (x4) {
      return constraints.complete(csp9, x4)
    });
    return NofibPrelude.filter(lambda1, tmp4)
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
    let tmp, tmp1, tmp2, tmp3, tmp4, lambda, lambda1;
    tmp = constraints.mkTree(csp11);
    tmp1 = runtime.safeCall(labeler(csp11, tmp));
    lambda = (undefined, function (x4) {
      let tmp5;
      tmp5 = NofibPrelude.snd(x4);
      return constraints.knownConflict(tmp5)
    });
    tmp2 = constraints.prune(lambda, tmp1);
    tmp3 = constraints.leaves(tmp2);
    lambda1 = (undefined, function (x4) {
      let tmp5;
      tmp5 = NofibPrelude.snd(x4);
      return constraints.knownSolution(tmp5)
    });
    tmp4 = NofibPrelude.filter(lambda1, tmp3);
    return NofibPrelude.map(NofibPrelude.fst, tmp4)
  } 
  static bt(csp12, t4) {
    let f3;
    f3 = function f3(s2) {
      let scrut, param0, first1, first0, a2, b, tmp, tmp1, tmp2;
      scrut = constraints.earliestInconsistency(csp12, s2);
      if (scrut instanceof NofibPrelude.Some.class) {
        param0 = scrut.x;
        if (globalThis.Array.isArray(param0) && param0.length === 2) {
          first0 = param0[0];
          first1 = param0[1];
          a2 = first0;
          b = first1;
          tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
          tmp1 = NofibPrelude.Cons(a2, tmp);
          tmp2 = constraints.Known(tmp1);
        } else {
          tmp2 = constraints.checkComplete(csp12, s2);
        }
      } else {
        tmp2 = constraints.checkComplete(csp12, s2);
      }
      return [
        s2,
        tmp2
      ]
    };
    return constraints.mapTree(f3, t4)
  } 
  static emptyTable(csp13) {
    let lscomp1, param0, param1, param2, vars, vals, rel, tmp, tmp1;
    if (csp13 instanceof constraints.CSP.class) {
      param0 = csp13.vars;
      param1 = csp13.vals;
      param2 = csp13.rel;
      vars = param0;
      vals = param1;
      rel = param2;
      lscomp1 = function lscomp1(ls5) {
        let lscomp2, param01, param11, n4, t11, tmp2, tmp3, tmp4;
        if (ls5 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (ls5 instanceof NofibPrelude.Cons.class) {
          param01 = ls5.head;
          param11 = ls5.tail;
          n4 = param01;
          t11 = param11;
          lscomp2 = function lscomp2(ls6) {
            let param02, param12, m, t21, tmp5;
            if (ls6 instanceof NofibPrelude.Nil.class) {
              return NofibPrelude.Nil
            } else if (ls6 instanceof NofibPrelude.Cons.class) {
              param02 = ls6.head;
              param12 = ls6.tail;
              m = param02;
              t21 = param12;
              tmp5 = lscomp2(t21);
              return NofibPrelude.Cons(constraints.Unknown, tmp5)
            } else {
              throw new globalThis.Error("match error");
            }
          };
          tmp2 = NofibPrelude.enumFromTo(1, vals);
          tmp3 = lscomp2(tmp2);
          tmp4 = lscomp1(t11);
          return NofibPrelude.Cons(tmp3, tmp4)
        } else {
          throw new globalThis.Error("match error");
        }
      };
      tmp = NofibPrelude.enumFromTo(1, vars);
      tmp1 = lscomp1(tmp);
      return NofibPrelude.Cons(NofibPrelude.Nil, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static fillTable(s2, csp14, tbl) {
    let f4, lscomp1, param0, param1, param01, param11, var_, val_, as_1, param02, param12, param2, vars, vals, rel, tmp, tmp1, tmp2, lambda;
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
          f4 = function f4(cs, varval) {
            let first1, first0, varr, vall, scrut, scrut1, tmp3, tmp4, tmp5, tmp6, tmp7;
            if (globalThis.Array.isArray(varval) && varval.length === 2) {
              first0 = varval[0];
              first1 = varval[1];
              varr = first0;
              vall = first1;
              scrut = cs === constraints.Unknown;
              if (scrut === true) {
                tmp3 = constraints.Assign(var_, val_);
                tmp4 = constraints.Assign(varr, vall);
                tmp5 = runtime.safeCall(rel(tmp3, tmp4));
                scrut1 = BenchmarkPrelude.not(tmp5);
                if (scrut1 === true) {
                  tmp6 = NofibPrelude.Cons(varr, NofibPrelude.Nil);
                  tmp7 = NofibPrelude.Cons(var_, tmp6);
                  return constraints.Known(tmp7)
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
          lscomp1 = function lscomp1(ls5) {
            let lscomp2, param03, param13, varrr, t11, tmp3, tmp4, tmp5;
            if (ls5 instanceof NofibPrelude.Nil.class) {
              return NofibPrelude.Nil
            } else if (ls5 instanceof NofibPrelude.Cons.class) {
              param03 = ls5.head;
              param13 = ls5.tail;
              varrr = param03;
              t11 = param13;
              lscomp2 = function lscomp2(ls6) {
                let param04, param14, valll, t21, tmp6;
                if (ls6 instanceof NofibPrelude.Nil.class) {
                  return NofibPrelude.Nil
                } else if (ls6 instanceof NofibPrelude.Cons.class) {
                  param04 = ls6.head;
                  param14 = ls6.tail;
                  valll = param04;
                  t21 = param14;
                  tmp6 = lscomp2(t21);
                  return NofibPrelude.Cons([
                    varrr,
                    valll
                  ], tmp6)
                } else {
                  throw new globalThis.Error("match error");
                }
              };
              tmp3 = NofibPrelude.enumFromTo(1, vals);
              tmp4 = lscomp2(tmp3);
              tmp5 = lscomp1(t11);
              return NofibPrelude.Cons(tmp4, tmp5)
            } else {
              throw new globalThis.Error("match error");
            }
          };
          tmp = var_ + 1;
          tmp1 = NofibPrelude.enumFromTo(tmp, vars);
          tmp2 = lscomp1(tmp1);
          lambda = (undefined, function (x4, y) {
            return NofibPrelude.zipWith(f4, x4, y)
          });
          return NofibPrelude.zipWith(lambda, tbl, tmp2)
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
    let f5, lambda;
    f5 = function f5(csp16, tp) {
      let first1, first0, param0, param1, a2, as_1, tbl1, tableEntry, cs, scrut, tbl2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
      if (globalThis.Array.isArray(tp) && tp.length === 2) {
        first0 = tp[0];
        first1 = tp[1];
        if (first0 instanceof NofibPrelude.Nil.class) {
          tbl2 = first1;
          return [
            [
              NofibPrelude.Nil,
              constraints.Unknown
            ],
            tbl2
          ]
        } else if (first0 instanceof NofibPrelude.Cons.class) {
          param0 = first0.head;
          param1 = first0.tail;
          a2 = param0;
          as_1 = param1;
          tbl1 = first1;
          tmp = constraints.value(a2);
          tmp1 = tmp - 1;
          tmp2 = NofibPrelude.head(tbl1);
          tmp3 = NofibPrelude.atIndex(tmp1, tmp2);
          tableEntry = tmp3;
          scrut = tableEntry === constraints.Unknown;
          if (scrut === true) {
            tmp4 = NofibPrelude.Cons(a2, as_1);
            tmp5 = constraints.checkComplete(csp16, tmp4);
          } else {
            tmp5 = tableEntry;
          }
          cs = tmp5;
          tmp6 = NofibPrelude.Cons(a2, as_1);
          return [
            [
              tmp6,
              cs
            ],
            tbl1
          ]
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    lambda = (undefined, function (x4) {
      return f5(csp15, x4)
    });
    return constraints.mapTree(lambda, t5)
  } 
  static cacheChecks(csp16, tbl1, n4) {
    let param0, param1, s3, cs, tmp, tmp1, lambda;
    if (n4 instanceof constraints.Node.class) {
      param0 = n4.lab;
      param1 = n4.children;
      s3 = param0;
      cs = param1;
      lambda = (undefined, function (x4) {
        let tmp2, tmp3;
        tmp2 = NofibPrelude.tail(tbl1);
        tmp3 = constraints.fillTable(s3, csp16, tmp2);
        return constraints.cacheChecks(csp16, tmp3, x4)
      });
      tmp = lambda;
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
    let f7;
    f7 = function f7(tp2, chs) {
      let first1, first0, a2, cs_, scrut, a3, param0, cs, tmp, tmp1, tmp2;
      if (globalThis.Array.isArray(tp2) && tp2.length === 2) {
        first0 = tp2[0];
        first1 = tp2[1];
        a3 = first0;
        a2 = first0;
        if (first1 instanceof constraints.Known.class) {
          param0 = first1.vs;
          cs = param0;
          tmp = constraints.Known(cs);
          return constraints.Node([
            a3,
            tmp
          ], chs)
        } else if (first1 instanceof constraints.Unknown.class) {
          tmp1 = NofibPrelude.map(constraints.label, chs);
          tmp2 = constraints.combine(tmp1, NofibPrelude.Nil);
          cs_ = constraints.Known(tmp2);
          scrut = constraints.knownConflict(cs_);
          if (scrut === true) {
            return constraints.Node([
              a2,
              cs_
            ], NofibPrelude.Nil)
          } else {
            return constraints.Node([
              a2,
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
    return constraints.foldTree(f7, t7)
  } 
  static bj(csp19, t8) {
    let f6;
    f6 = function f6(tp2, chs) {
      let first1, first0, a2, a3, param0, cs, tmp, tmp1, tmp2, tmp3;
      if (globalThis.Array.isArray(tp2) && tp2.length === 2) {
        first0 = tp2[0];
        first1 = tp2[1];
        a3 = first0;
        a2 = first0;
        if (first1 instanceof constraints.Known.class) {
          param0 = first1.vs;
          cs = param0;
          tmp = constraints.Known(cs);
          return constraints.Node([
            a3,
            tmp
          ], chs)
        } else if (first1 instanceof constraints.Unknown.class) {
          tmp1 = NofibPrelude.map(constraints.label, chs);
          tmp2 = constraints.combine(tmp1, NofibPrelude.Nil);
          tmp3 = constraints.Known(tmp2);
          return constraints.Node([
            a2,
            tmp3
          ], chs)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
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
    let f8, param0, param1, param2, vars, vals, rel;
    if (csp22 instanceof constraints.CSP.class) {
      param0 = csp22.vars;
      param1 = csp22.vals;
      param2 = csp22.rel;
      vars = param0;
      vals = param1;
      rel = param2;
      f8 = function f8(tp2) {
        let lscomp1, first1, first0, first11, first01, as_1, cs, tbl2, wipedDomains, cs_, scrut, tmp, tmp1, tmp2, tmp3;
        if (globalThis.Array.isArray(tp2) && tp2.length === 2) {
          first0 = tp2[0];
          first1 = tp2[1];
          if (globalThis.Array.isArray(first0) && first0.length === 2) {
            first01 = first0[0];
            first11 = first0[1];
            as_1 = first01;
            cs = first11;
            tbl2 = first1;
            lscomp1 = function lscomp1(ls7) {
              let param01, param11, vs, t12, scrut1, tmp4;
              if (ls7 instanceof NofibPrelude.Nil.class) {
                return NofibPrelude.Nil
              } else if (ls7 instanceof NofibPrelude.Cons.class) {
                param01 = ls7.head;
                param11 = ls7.tail;
                vs = param01;
                t12 = param11;
                scrut1 = NofibPrelude.all(constraints.knownConflict, vs);
                if (scrut1 === true) {
                  tmp4 = lscomp1(t12);
                  return NofibPrelude.Cons(vs, tmp4)
                } else {
                  return lscomp1(t12)
                }
              } else {
                throw new globalThis.Error("match error");
              }
            };
            tmp = lscomp1(tbl2);
            wipedDomains = tmp;
            scrut = NofibPrelude.null_(wipedDomains);
            if (scrut === true) {
              tmp1 = cs;
            } else {
              tmp2 = NofibPrelude.head(wipedDomains);
              tmp3 = constraints.collect(tmp2);
              tmp1 = constraints.Known(tmp3);
            }
            cs_ = tmp1;
            return [
              as_1,
              cs_
            ]
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      };
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
    let tmp, tmp1, tmp2, tmp3, tmp4, lambda;
    tmp = NofibPrelude.Cons(constraints.fc, NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons(constraints.bjbt_, tmp);
    tmp2 = NofibPrelude.Cons(constraints.bjbt, tmp1);
    tmp3 = NofibPrelude.Cons(constraints.bm, tmp2);
    tmp4 = NofibPrelude.Cons(constraints.bt, tmp3);
    lambda = (undefined, function (x4) {
      return constraints.try_(n6, x4)
    });
    return NofibPrelude.map(lambda, tmp4)
  }
  static toString() { return "constraints"; }
};
let constraints = constraints1; export default constraints;
