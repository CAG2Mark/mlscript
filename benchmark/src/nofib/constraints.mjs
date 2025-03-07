import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let cacheChecks, safe, bm, maxLevel, solver, prune, bjbt_, rqsort, collect, Unknown1, knownConflict, knownSolution, test, bj_, qpart, leaves, inconsistencies, ConflictSet1, qsort, domainWipeout, emptyTable, Known1, generate, rqpart, bjbt, fc, bt, label, earliestInconsistency, testConstraints_nofib, bj, Node1, btsolver0, foldTree, queens, labelInconsistencies, consistent, complete, combine, mkTree, Assign1, checkComplete, value, filterTree, mapTree, initTree, CSP1, fillTable, lookupCache, level, search, try_, lambda;
qsort = function qsort(le, ls, r) {
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
      return qpart(le, x, xs, NofibPrelude.Nil, NofibPrelude.Nil, r)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
qpart = function qpart(le, x, ls, rlt, rge, r) {
  let param0, param1, y, ys, scrut, tmp, tmp1, tmp2, tmp3;
  if (ls instanceof NofibPrelude.Nil.class) {
    tmp = rqsort(le, rge, r);
    tmp1 = NofibPrelude.Cons(x, tmp);
    return rqsort(le, rlt, tmp1)
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    y = param0;
    ys = param1;
    scrut = runtime.safeCall(le(x, y));
    if (scrut === true) {
      tmp2 = NofibPrelude.Cons(y, rge);
      return qpart(le, x, ys, rlt, tmp2, r)
    } else {
      tmp3 = NofibPrelude.Cons(y, rlt);
      return qpart(le, x, ys, tmp3, rge, r)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
rqsort = function rqsort(le, ls, r) {
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
      return rqpart(le, x, xs, NofibPrelude.Nil, NofibPrelude.Nil, r)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
rqpart = function rqpart(le, x, ls, rle, rgt, r) {
  let param0, param1, y, ys, scrut, tmp, tmp1, tmp2, tmp3;
  if (ls instanceof NofibPrelude.Nil.class) {
    tmp = qsort(le, rgt, r);
    tmp1 = NofibPrelude.Cons(x, tmp);
    return rqsort(le, rle, tmp1)
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    y = param0;
    ys = param1;
    scrut = runtime.safeCall(le(y, x));
    if (scrut === true) {
      tmp2 = NofibPrelude.Cons(y, rle);
      return rqpart(le, x, ys, tmp2, rgt, r)
    } else {
      tmp3 = NofibPrelude.Cons(y, rgt);
      return rqpart(le, x, ys, rle, tmp3, r)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
level = function level(a) {
  let param0, param1, v;
  if (a instanceof Assign1.class) {
    param0 = a.varr;
    param1 = a.value;
    v = param0;
    return v
  } else {
    throw new globalThis.Error("match error");
  }
};
value = function value(a) {
  let param0, param1, v;
  if (a instanceof Assign1.class) {
    param0 = a.varr;
    param1 = a.value;
    v = param1;
    return v
  } else {
    throw new globalThis.Error("match error");
  }
};
maxLevel = function maxLevel(ls) {
  let param0, param1, param01, param11, v, t;
  if (ls instanceof NofibPrelude.Nil.class) {
    return 0
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    if (param0 instanceof Assign1.class) {
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
};
complete = function complete(csp, s) {
  let param0, param1, param2, v, tmp;
  if (csp instanceof CSP1.class) {
    param0 = csp.vars;
    param1 = csp.vals;
    param2 = csp.rel;
    v = param0;
    tmp = maxLevel(s);
    return tmp == v
  } else {
    throw new globalThis.Error("match error");
  }
};
generate = function generate(csp) {
  let g, param0, param1, param2, vars, vals, rel;
  g = function g(vals1, var_) {
    let lscomp1, scrut, tmp;
    lscomp1 = function lscomp1(ls) {
      let lscomp2, param01, param11, val_, t1, tmp1, tmp2;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param01 = ls.head;
        param11 = ls.tail;
        val_ = param01;
        t1 = param11;
        lscomp2 = function lscomp2(ls1) {
          let param02, param12, st, t2, tmp3, tmp4, tmp5;
          if (ls1 instanceof NofibPrelude.Nil.class) {
            return lscomp1(t1)
          } else if (ls1 instanceof NofibPrelude.Cons.class) {
            param02 = ls1.head;
            param12 = ls1.tail;
            st = param02;
            t2 = param12;
            tmp3 = Assign1(var_, val_);
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
  if (csp instanceof CSP1.class) {
    param0 = csp.vars;
    param1 = csp.vals;
    param2 = csp.rel;
    vars = param0;
    vals = param1;
    rel = param2;
    return g(vals, vars)
  } else {
    throw new globalThis.Error("match error");
  }
};
inconsistencies = function inconsistencies(csp, as_) {
  let lscomp1, param0, param1, param2, vars, vals, rel;
  if (csp instanceof CSP1.class) {
    param0 = csp.vars;
    param1 = csp.vals;
    param2 = csp.rel;
    vars = param0;
    vals = param1;
    rel = param2;
    lscomp1 = function lscomp1(ls) {
      let lscomp2, param01, param11, a, t1, tmp;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param01 = ls.head;
        param11 = ls.tail;
        a = param01;
        t1 = param11;
        lscomp2 = function lscomp2(ls1) {
          let param02, param12, b, t2, scrut, scrut1, tmp1, tmp2, tmp3;
          if (ls1 instanceof NofibPrelude.Nil.class) {
            return lscomp1(t1)
          } else if (ls1 instanceof NofibPrelude.Cons.class) {
            param02 = ls1.head;
            param12 = ls1.tail;
            b = param02;
            t2 = param12;
            scrut = a > b;
            if (scrut === true) {
              tmp1 = runtime.safeCall(rel(a, b));
              scrut1 = BenchmarkPrelude.not(tmp1);
              if (scrut1 === true) {
                tmp2 = level(a);
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
};
consistent = function consistent(csp, x) {
  let tmp;
  tmp = inconsistencies(csp, x);
  return NofibPrelude.null_(tmp)
};
test = function test(csp) {
  let tmp;
  tmp = consistent(csp);
  return NofibPrelude.filter(tmp)
};
solver = function solver(csp) {
  let tmp;
  tmp = generate(csp);
  return test(csp, tmp)
};
safe = function safe(as1, as2) {
  let param0, param1, i, m, param01, param11, j, n, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
  if (as1 instanceof Assign1.class) {
    param0 = as1.varr;
    param1 = as1.value;
    i = param0;
    m = param1;
    if (as2 instanceof Assign1.class) {
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
};
queens = function queens(n) {
  return CSP1(n, n, safe)
};
label = function label(n) {
  let param0, param1, l;
  if (n instanceof Node1.class) {
    param0 = n.lab;
    param1 = n.children;
    l = param0;
    return l
  } else {
    throw new globalThis.Error("match error");
  }
};
mapTree = function mapTree(f, n) {
  let param0, param1, l, c, tmp, tmp1, lambda1;
  if (n instanceof Node1.class) {
    param0 = n.lab;
    param1 = n.children;
    l = param0;
    c = param1;
    tmp = runtime.safeCall(f(l));
    lambda1 = (undefined, function (x) {
      return mapTree(f, x)
    });
    tmp1 = NofibPrelude.map(lambda1, c);
    return Node1(tmp, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
foldTree = function foldTree(f, n) {
  let param0, param1, l, c, tmp, lambda1;
  if (n instanceof Node1.class) {
    param0 = n.lab;
    param1 = n.children;
    l = param0;
    c = param1;
    lambda1 = (undefined, function (x) {
      return foldTree(f, x)
    });
    tmp = NofibPrelude.map(lambda1, c);
    return runtime.safeCall(f(l, tmp))
  } else {
    throw new globalThis.Error("match error");
  }
};
filterTree = function filterTree(p, t) {
  let f1;
  f1 = function f1(a, cs) {
    let tmp, lambda1;
    lambda1 = (undefined, function (x) {
      let tmp1;
      tmp1 = label(x);
      return runtime.safeCall(p(tmp1))
    });
    tmp = NofibPrelude.filter(lambda1, cs);
    return Node1(a, tmp)
  };
  return foldTree(f1, t)
};
prune = function prune(p, t) {
  let lambda1;
  lambda1 = (undefined, function (x) {
    let tmp;
    tmp = runtime.safeCall(p(x));
    return BenchmarkPrelude.not(tmp)
  });
  return filterTree(lambda1, t)
};
leaves = function leaves(t) {
  let param0, param1, cs, leaf, tmp;
  if (t instanceof Node1.class) {
    param0 = t.lab;
    param1 = t.children;
    leaf = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(leaf, NofibPrelude.Nil)
    } else {
      cs = param1;
      tmp = NofibPrelude.map(leaves, cs);
      return NofibPrelude.concat(tmp)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
initTree = function initTree(f, x) {
  let tmp, tmp1, lambda1;
  tmp = runtime.safeCall(f(x));
  lambda1 = (undefined, function (y) {
    return initTree(f, y)
  });
  tmp1 = NofibPrelude.map(lambda1, tmp);
  return Node1(x, tmp1)
};
mkTree = function mkTree(csp) {
  let next, param0, param1, param2, vars, vals, rel;
  if (csp instanceof CSP1.class) {
    param0 = csp.vars;
    param1 = csp.vals;
    param2 = csp.rel;
    vars = param0;
    vals = param1;
    rel = param2;
    next = function next(ss) {
      let lscomp1, scrut, tmp, tmp1;
      tmp = maxLevel(ss);
      scrut = tmp < vars;
      if (scrut === true) {
        lscomp1 = function lscomp1(ls) {
          let param01, param11, j, t1, tmp2, tmp3, tmp4, tmp5, tmp6;
          if (ls instanceof NofibPrelude.Nil.class) {
            return NofibPrelude.Nil
          } else if (ls instanceof NofibPrelude.Cons.class) {
            param01 = ls.head;
            param11 = ls.tail;
            j = param01;
            t1 = param11;
            tmp2 = maxLevel(ss);
            tmp3 = tmp2 + 1;
            tmp4 = Assign1(tmp3, j);
            tmp5 = NofibPrelude.Cons(tmp4, ss);
            tmp6 = lscomp1(t1);
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
    return initTree(next, NofibPrelude.Nil)
  } else {
    throw new globalThis.Error("match error");
  }
};
earliestInconsistency = function earliestInconsistency(csp, aas) {
  let param0, param1, param2, vars, vals, rel, param01, param11, a, as_, scrut, param02, param12, b, tmp, tmp1, tmp2, lambda1;
  if (csp instanceof CSP1.class) {
    param0 = csp.vars;
    param1 = csp.vals;
    param2 = csp.rel;
    vars = param0;
    vals = param1;
    rel = param2;
    if (aas instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.None
    } else if (aas instanceof NofibPrelude.Cons.class) {
      param01 = aas.head;
      param11 = aas.tail;
      a = param01;
      as_ = param11;
      tmp = NofibPrelude.reverse(as_);
      lambda1 = (undefined, function (x) {
        let tmp3;
        tmp3 = runtime.safeCall(rel(a, x));
        return BenchmarkPrelude.not(tmp3)
      });
      scrut = NofibPrelude.filter(lambda1, tmp);
      if (scrut instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.None
      } else if (scrut instanceof NofibPrelude.Cons.class) {
        param02 = scrut.head;
        param12 = scrut.tail;
        b = param02;
        tmp1 = level(a);
        tmp2 = level(b);
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
};
labelInconsistencies = function labelInconsistencies(csp, t) {
  let f2;
  f2 = function f2(s) {
    let tmp;
    tmp = earliestInconsistency(csp, s);
    return [
      s,
      tmp
    ]
  };
  return mapTree(f2, t)
};
btsolver0 = function btsolver0(csp) {
  let tmp, tmp1, tmp2, tmp3, tmp4, lambda1, lambda2;
  tmp = mkTree(csp);
  tmp1 = labelInconsistencies(csp, tmp);
  lambda1 = (undefined, function (x) {
    let tmp5, tmp6;
    tmp5 = NofibPrelude.snd(x);
    tmp6 = tmp5 === NofibPrelude.None;
    return BenchmarkPrelude.not(tmp6)
  });
  tmp2 = prune(lambda1, tmp1);
  tmp3 = mapTree(NofibPrelude.fst, tmp2);
  tmp4 = leaves(tmp3);
  lambda2 = (undefined, function (x) {
    return complete(csp, x)
  });
  return NofibPrelude.filter(lambda2, tmp4)
};
knownConflict = function knownConflict(c) {
  let param0, param01, param1, a, as_;
  if (c instanceof Known1.class) {
    param0 = c.vs;
    if (param0 instanceof NofibPrelude.Cons.class) {
      param01 = param0.head;
      param1 = param0.tail;
      a = param01;
      as_ = param1;
      return true
    } else {
      return false
    }
  } else {
    return false
  }
};
knownSolution = function knownSolution(c) {
  let param0;
  if (c instanceof Known1.class) {
    param0 = c.vs;
    if (param0 instanceof NofibPrelude.Nil.class) {
      return true
    } else {
      return false
    }
  } else {
    return false
  }
};
checkComplete = function checkComplete(csp, s) {
  let scrut;
  scrut = complete(csp, s);
  if (scrut === true) {
    return Known1(NofibPrelude.Nil)
  } else {
    return Unknown1
  }
};
search = function search(labeler, csp) {
  let tmp, tmp1, tmp2, tmp3, tmp4, lambda1, lambda2;
  tmp = mkTree(csp);
  tmp1 = runtime.safeCall(labeler(csp, tmp));
  lambda1 = (undefined, function (x) {
    let tmp5;
    tmp5 = NofibPrelude.snd(x);
    return knownConflict(tmp5)
  });
  tmp2 = prune(lambda1, tmp1);
  tmp3 = leaves(tmp2);
  lambda2 = (undefined, function (x) {
    let tmp5;
    tmp5 = NofibPrelude.snd(x);
    return knownSolution(tmp5)
  });
  tmp4 = NofibPrelude.filter(lambda2, tmp3);
  return NofibPrelude.map(NofibPrelude.fst, tmp4)
};
bt = function bt(csp, t) {
  let f3;
  f3 = function f3(s) {
    let scrut, param0, first1, first0, a, b, tmp, tmp1, tmp2;
    scrut = earliestInconsistency(csp, s);
    if (scrut instanceof NofibPrelude.Some.class) {
      param0 = scrut.x;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        a = first0;
        b = first1;
        tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
        tmp1 = NofibPrelude.Cons(a, tmp);
        tmp2 = Known1(tmp1);
      } else {
        tmp2 = checkComplete(csp, s);
      }
    } else {
      tmp2 = checkComplete(csp, s);
    }
    return [
      s,
      tmp2
    ]
  };
  return mapTree(f3, t)
};
emptyTable = function emptyTable(csp) {
  let lscomp1, param0, param1, param2, vars, vals, rel, tmp, tmp1;
  if (csp instanceof CSP1.class) {
    param0 = csp.vars;
    param1 = csp.vals;
    param2 = csp.rel;
    vars = param0;
    vals = param1;
    rel = param2;
    lscomp1 = function lscomp1(ls) {
      let lscomp2, param01, param11, n, t1, tmp2, tmp3, tmp4;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param01 = ls.head;
        param11 = ls.tail;
        n = param01;
        t1 = param11;
        lscomp2 = function lscomp2(ls1) {
          let param02, param12, m, t2, tmp5;
          if (ls1 instanceof NofibPrelude.Nil.class) {
            return NofibPrelude.Nil
          } else if (ls1 instanceof NofibPrelude.Cons.class) {
            param02 = ls1.head;
            param12 = ls1.tail;
            m = param02;
            t2 = param12;
            tmp5 = lscomp2(t2);
            return NofibPrelude.Cons(Unknown1, tmp5)
          } else {
            throw new globalThis.Error("match error");
          }
        };
        tmp2 = NofibPrelude.enumFromTo(1, vals);
        tmp3 = lscomp2(tmp2);
        tmp4 = lscomp1(t1);
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
};
fillTable = function fillTable(s, csp, tbl) {
  let f4, lscomp1, param0, param1, param01, param11, var_, val_, as_, param02, param12, param2, vars, vals, rel, tmp, tmp1, tmp2, lambda1;
  if (s instanceof NofibPrelude.Nil.class) {
    return tbl
  } else if (s instanceof NofibPrelude.Cons.class) {
    param0 = s.head;
    param1 = s.tail;
    if (param0 instanceof Assign1.class) {
      param01 = param0.varr;
      param11 = param0.value;
      var_ = param01;
      val_ = param11;
      as_ = param1;
      if (csp instanceof CSP1.class) {
        param02 = csp.vars;
        param12 = csp.vals;
        param2 = csp.rel;
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
            scrut = cs === Unknown1;
            if (scrut === true) {
              tmp3 = Assign1(var_, val_);
              tmp4 = Assign1(varr, vall);
              tmp5 = runtime.safeCall(rel(tmp3, tmp4));
              scrut1 = BenchmarkPrelude.not(tmp5);
              if (scrut1 === true) {
                tmp6 = NofibPrelude.Cons(varr, NofibPrelude.Nil);
                tmp7 = NofibPrelude.Cons(var_, tmp6);
                return Known1(tmp7)
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
        lscomp1 = function lscomp1(ls) {
          let lscomp2, param03, param13, varrr, t1, tmp3, tmp4, tmp5;
          if (ls instanceof NofibPrelude.Nil.class) {
            return NofibPrelude.Nil
          } else if (ls instanceof NofibPrelude.Cons.class) {
            param03 = ls.head;
            param13 = ls.tail;
            varrr = param03;
            t1 = param13;
            lscomp2 = function lscomp2(ls1) {
              let param04, param14, valll, t2, tmp6;
              if (ls1 instanceof NofibPrelude.Nil.class) {
                return NofibPrelude.Nil
              } else if (ls1 instanceof NofibPrelude.Cons.class) {
                param04 = ls1.head;
                param14 = ls1.tail;
                valll = param04;
                t2 = param14;
                tmp6 = lscomp2(t2);
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
            tmp5 = lscomp1(t1);
            return NofibPrelude.Cons(tmp4, tmp5)
          } else {
            throw new globalThis.Error("match error");
          }
        };
        tmp = var_ + 1;
        tmp1 = NofibPrelude.enumFromTo(tmp, vars);
        tmp2 = lscomp1(tmp1);
        lambda1 = (undefined, function (x, y) {
          return NofibPrelude.zipWith(f4, x, y)
        });
        return NofibPrelude.zipWith(lambda1, tbl, tmp2)
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
lookupCache = function lookupCache(csp, t) {
  let f5, lambda1;
  f5 = function f5(csp1, tp) {
    let first1, first0, param0, param1, a, as_, tbl, tableEntry, cs, scrut, tbl1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    if (globalThis.Array.isArray(tp) && tp.length === 2) {
      first0 = tp[0];
      first1 = tp[1];
      if (first0 instanceof NofibPrelude.Nil.class) {
        tbl1 = first1;
        return [
          [
            NofibPrelude.Nil,
            Unknown1
          ],
          tbl1
        ]
      } else if (first0 instanceof NofibPrelude.Cons.class) {
        param0 = first0.head;
        param1 = first0.tail;
        a = param0;
        as_ = param1;
        tbl = first1;
        tmp = value(a);
        tmp1 = tmp - 1;
        tmp2 = NofibPrelude.head(tbl);
        tmp3 = NofibPrelude.atIndex(tmp1, tmp2);
        tableEntry = tmp3;
        scrut = tableEntry === Unknown1;
        if (scrut === true) {
          tmp4 = NofibPrelude.Cons(a, as_);
          tmp5 = checkComplete(csp1, tmp4);
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
  lambda1 = (undefined, function (x) {
    return f5(csp, x)
  });
  return mapTree(lambda1, t)
};
cacheChecks = function cacheChecks(csp, tbl, n) {
  let param0, param1, s, cs, tmp, tmp1, lambda1;
  if (n instanceof Node1.class) {
    param0 = n.lab;
    param1 = n.children;
    s = param0;
    cs = param1;
    lambda1 = (undefined, function (x) {
      let tmp2, tmp3;
      tmp2 = NofibPrelude.tail(tbl);
      tmp3 = fillTable(s, csp, tmp2);
      return cacheChecks(csp, tmp3, x)
    });
    tmp = lambda1;
    tmp1 = NofibPrelude.map(tmp, cs);
    return Node1([
      s,
      tbl
    ], tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
bm = function bm(csp, t) {
  let tmp, tmp1, tmp2;
  tmp = emptyTable(csp);
  tmp1 = cacheChecks(csp, tmp, t);
  tmp2 = lookupCache(csp, tmp1);
  return mapTree(NofibPrelude.fst, tmp2)
};
combine = function combine(ls, acc) {
  let param0, param1, first1, first0, s, param01, cs, css, scrut, tmp, tmp1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return acc
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      s = first0;
      if (first1 instanceof Known1.class) {
        param01 = first1.vs;
        cs = param01;
        css = param1;
        tmp = maxLevel(s);
        scrut = NofibPrelude.notElem(tmp, cs);
        if (scrut === true) {
          return cs
        } else {
          tmp1 = NofibPrelude.union(cs, acc);
          return combine(css, tmp1)
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
bj_ = function bj_(csp, t) {
  let f7;
  f7 = function f7(tp2, chs) {
    let first1, first0, a, cs_, scrut, a1, param0, cs, tmp, tmp1, tmp2;
    if (globalThis.Array.isArray(tp2) && tp2.length === 2) {
      first0 = tp2[0];
      first1 = tp2[1];
      a1 = first0;
      a = first0;
      if (first1 instanceof Known1.class) {
        param0 = first1.vs;
        cs = param0;
        tmp = Known1(cs);
        return Node1([
          a1,
          tmp
        ], chs)
      } else if (first1 instanceof Unknown1.class) {
        tmp1 = NofibPrelude.map(label, chs);
        tmp2 = combine(tmp1, NofibPrelude.Nil);
        cs_ = Known1(tmp2);
        scrut = knownConflict(cs_);
        if (scrut === true) {
          return Node1([
            a,
            cs_
          ], NofibPrelude.Nil)
        } else {
          return Node1([
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
  return foldTree(f7, t)
};
bj = function bj(csp, t) {
  let f6;
  f6 = function f6(tp2, chs) {
    let first1, first0, a, a1, param0, cs, tmp, tmp1, tmp2, tmp3;
    if (globalThis.Array.isArray(tp2) && tp2.length === 2) {
      first0 = tp2[0];
      first1 = tp2[1];
      a1 = first0;
      a = first0;
      if (first1 instanceof Known1.class) {
        param0 = first1.vs;
        cs = param0;
        tmp = Known1(cs);
        return Node1([
          a1,
          tmp
        ], chs)
      } else if (first1 instanceof Unknown1.class) {
        tmp1 = NofibPrelude.map(label, chs);
        tmp2 = combine(tmp1, NofibPrelude.Nil);
        tmp3 = Known1(tmp2);
        return Node1([
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
  return foldTree(f6, t)
};
bjbt = function bjbt(csp, t) {
  let tmp;
  tmp = bt(csp, t);
  return bj(csp, tmp)
};
bjbt_ = function bjbt_(csp, t) {
  let tmp;
  tmp = bt(csp, t);
  return bj_(csp, tmp)
};
collect = function collect(ls) {
  let param0, param1, param01, cs, css, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    if (param0 instanceof Known1.class) {
      param01 = param0.vs;
      cs = param01;
      css = param1;
      tmp = collect(css);
      return NofibPrelude.union(cs, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
domainWipeout = function domainWipeout(csp, t) {
  let f8, param0, param1, param2, vars, vals, rel;
  if (csp instanceof CSP1.class) {
    param0 = csp.vars;
    param1 = csp.vals;
    param2 = csp.rel;
    vars = param0;
    vals = param1;
    rel = param2;
    f8 = function f8(tp2) {
      let lscomp1, first1, first0, first11, first01, as_, cs, tbl, wipedDomains, cs_, scrut, tmp, tmp1, tmp2, tmp3;
      if (globalThis.Array.isArray(tp2) && tp2.length === 2) {
        first0 = tp2[0];
        first1 = tp2[1];
        if (globalThis.Array.isArray(first0) && first0.length === 2) {
          first01 = first0[0];
          first11 = first0[1];
          as_ = first01;
          cs = first11;
          tbl = first1;
          lscomp1 = function lscomp1(ls) {
            let param01, param11, vs, t1, scrut1, tmp4;
            if (ls instanceof NofibPrelude.Nil.class) {
              return NofibPrelude.Nil
            } else if (ls instanceof NofibPrelude.Cons.class) {
              param01 = ls.head;
              param11 = ls.tail;
              vs = param01;
              t1 = param11;
              scrut1 = NofibPrelude.all(knownConflict, vs);
              if (scrut1 === true) {
                tmp4 = lscomp1(t1);
                return NofibPrelude.Cons(vs, tmp4)
              } else {
                return lscomp1(t1)
              }
            } else {
              throw new globalThis.Error("match error");
            }
          };
          tmp = lscomp1(tbl);
          wipedDomains = tmp;
          scrut = NofibPrelude.null_(wipedDomains);
          if (scrut === true) {
            tmp1 = cs;
          } else {
            tmp2 = NofibPrelude.head(wipedDomains);
            tmp3 = collect(tmp2);
            tmp1 = Known1(tmp3);
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
    return mapTree(f8, t)
  } else {
    throw new globalThis.Error("match error");
  }
};
fc = function fc(csp, t) {
  let tmp, tmp1, tmp2;
  tmp = emptyTable(csp);
  tmp1 = cacheChecks(csp, tmp, t);
  tmp2 = lookupCache(csp, tmp1);
  return domainWipeout(csp, tmp2)
};
try_ = function try_(n, algorithm) {
  let tmp, tmp1;
  tmp = queens(n);
  tmp1 = search(algorithm, tmp);
  return NofibPrelude.listLen(tmp1)
};
testConstraints_nofib = function testConstraints_nofib(n) {
  let tmp, tmp1, tmp2, tmp3, tmp4, lambda1;
  tmp = NofibPrelude.Cons(fc, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(bjbt_, tmp);
  tmp2 = NofibPrelude.Cons(bjbt, tmp1);
  tmp3 = NofibPrelude.Cons(bm, tmp2);
  tmp4 = NofibPrelude.Cons(bt, tmp3);
  lambda1 = (undefined, function (x) {
    return try_(n, x)
  });
  return NofibPrelude.map(lambda1, tmp4)
};
Assign1 = function Assign(varr1, value2) {
  return new Assign.class(varr1, value2);
};
Assign1.class = class Assign {
  constructor(varr, value1) {
    this.varr = varr;
    this.value = value1;
  }
  toString() { return "Assign(" + globalThis.Predef.render(this.varr) + ", " + globalThis.Predef.render(this.value) + ")"; }
};
CSP1 = function CSP(vars1, vals1, rel1) {
  return new CSP.class(vars1, vals1, rel1);
};
CSP1.class = class CSP {
  constructor(vars, vals, rel) {
    this.vars = vars;
    this.vals = vals;
    this.rel = rel;
  }
  toString() { return "CSP(" + globalThis.Predef.render(this.vars) + ", " + globalThis.Predef.render(this.vals) + ", " + globalThis.Predef.render(this.rel) + ")"; }
};
Node1 = function Node(lab1, children1) {
  return new Node.class(lab1, children1);
};
Node1.class = class Node {
  constructor(lab, children) {
    this.lab = lab;
    this.children = children;
  }
  toString() { return "Node(" + globalThis.Predef.render(this.lab) + ", " + globalThis.Predef.render(this.children) + ")"; }
};
ConflictSet1 = class ConflictSet {
  constructor() {}
  toString() { return "ConflictSet"; }
};
Known1 = function Known(vs1) {
  return new Known.class(vs1);
};
Known1.class = class Known extends ConflictSet1 {
  constructor(vs) {
    super();
    this.vs = vs;
  }
  toString() { return "Known(" + globalThis.Predef.render(this.vs) + ")"; }
};
const Unknown$class = class Unknown extends ConflictSet1 {
  constructor() {
    super();
  }
  toString() { return "Unknown"; }
}; Unknown1 = new Unknown$class;
Unknown1.class = Unknown$class;
lambda = (undefined, function () {
  let tmp;
  tmp = testConstraints_nofib(6);
  return runtime.safeCall(tmp.toString())
});
BenchmarkPrelude.benchmark(lambda)