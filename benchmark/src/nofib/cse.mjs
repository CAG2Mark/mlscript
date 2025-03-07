import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let mmapr, fetchWith, join, visited, newlyDefined, labelTree, startingWith, cse_, ltGraph, update, testCse_nofib, findCommon, mmap, mfoldl, bind, Node1, mfoldr, mmapl, set_, mult_, prod, fetch, mif, plus_, retURN, incr, zerO, a, b, c, d, example0, example1, example2, example3, example4, example5, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, lambda, lambda1;
retURN = function retURN(a1) {
  let lambda2;
  lambda2 = (undefined, function (s) {
    return [
      s,
      a1
    ]
  });
  return lambda2
};
bind = function bind(m, f) {
  let lambda2;
  lambda2 = (undefined, function (s) {
    let scrut, first1, first0, s_, a1, tmp26;
    scrut = runtime.safeCall(m(s));
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      s_ = first0;
      a1 = first1;
      tmp26 = runtime.safeCall(f(a1));
      return runtime.safeCall(tmp26(s_))
    } else {
      throw new globalThis.Error("match error");
    }
  });
  return lambda2
};
join = function join(m) {
  let lambda2;
  lambda2 = (undefined, function (s) {
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
  });
  return lambda2
};
mmap = function mmap(f, m) {
  let lambda2;
  lambda2 = (undefined, function (s) {
    let scrut, first1, first0, s_, a1, tmp26;
    scrut = runtime.safeCall(m(s));
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      s_ = first0;
      a1 = first1;
      tmp26 = runtime.safeCall(f(a1));
      return [
        s_,
        tmp26
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  });
  return lambda2
};
mmapl = function mmapl(f, aas) {
  let param0, param1, a1, as_, tmp26, lambda2;
  if (aas instanceof NofibPrelude.Nil.class) {
    return retURN(NofibPrelude.Nil)
  } else if (aas instanceof NofibPrelude.Cons.class) {
    param0 = aas.head;
    param1 = aas.tail;
    a1 = param0;
    as_ = param1;
    tmp26 = runtime.safeCall(f(a1));
    lambda2 = (undefined, function (b1) {
      let tmp27, lambda3;
      tmp27 = mmapl(f, as_);
      lambda3 = (undefined, function (bs) {
        let tmp28;
        tmp28 = NofibPrelude.Cons(b1, bs);
        return retURN(tmp28)
      });
      return bind(tmp27, lambda3)
    });
    return bind(tmp26, lambda2)
  } else {
    throw new globalThis.Error("match error");
  }
};
mmapr = function mmapr(f, xs) {
  let param0, param1, x, xs1, tmp26, lambda2;
  if (xs instanceof NofibPrelude.Nil.class) {
    return retURN(NofibPrelude.Nil)
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs1 = param1;
    tmp26 = mmapr(f, xs1);
    lambda2 = (undefined, function (ys) {
      let tmp27, lambda3;
      tmp27 = runtime.safeCall(f(x));
      lambda3 = (undefined, function (y) {
        let tmp28;
        tmp28 = NofibPrelude.Cons(y, ys);
        return retURN(tmp28)
      });
      return bind(tmp27, lambda3)
    });
    return bind(tmp26, lambda2)
  } else {
    throw new globalThis.Error("match error");
  }
};
mfoldl = function mfoldl(f, a1, xs) {
  let param0, param1, x, xs1, tmp26, lambda2;
  if (xs instanceof NofibPrelude.Nil.class) {
    return retURN(a1)
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs1 = param1;
    tmp26 = runtime.safeCall(f(a1, x));
    lambda2 = (undefined, function (fax) {
      return mfoldl(f, fax, xs1)
    });
    return bind(tmp26, lambda2)
  } else {
    throw new globalThis.Error("match error");
  }
};
mfoldr = function mfoldr(f, a1, xs) {
  let param0, param1, x, xs1, tmp26, lambda2;
  if (xs instanceof NofibPrelude.Nil.class) {
    return retURN(a1)
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs1 = param1;
    tmp26 = mfoldr(f, a1, xs1);
    lambda2 = (undefined, function (y) {
      return runtime.safeCall(f(x, y))
    });
    return bind(tmp26, lambda2)
  } else {
    throw new globalThis.Error("match error");
  }
};
mif = function mif(c1, t, f) {
  let lambda2;
  lambda2 = (undefined, function (cond) {
    if (cond === true) {
      return t
    } else {
      return f
    }
  });
  return bind(c1, lambda2)
};
startingWith = function startingWith(m, v) {
  let scrut, first1, first0, final1, answer;
  scrut = runtime.safeCall(m(v));
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    final1 = first0;
    answer = first1;
    return answer
  } else {
    throw new globalThis.Error("match error");
  }
};
fetch = function fetch(s) {
  return [
    s,
    s
  ]
};
fetchWith = function fetchWith(f) {
  let lambda2;
  lambda2 = (undefined, function (s) {
    let tmp26;
    tmp26 = runtime.safeCall(f(s));
    return [
      s,
      tmp26
    ]
  });
  return lambda2
};
update = function update(f) {
  let lambda2;
  lambda2 = (undefined, function (s) {
    let tmp26;
    tmp26 = runtime.safeCall(f(s));
    return [
      tmp26,
      s
    ]
  });
  return lambda2
};
set_ = function set_(s_) {
  let lambda2;
  lambda2 = (undefined, function (s) {
    return [
      s_,
      s
    ]
  });
  return lambda2
};
labelTree = function labelTree(t) {
  let label, tmp26;
  label = function label(t1) {
    let param0, param1, x, xs, lambda2;
    if (t1 instanceof Node1.class) {
      param0 = t1.a;
      param1 = t1.b;
      x = param0;
      xs = param1;
      lambda2 = (undefined, function (n) {
        let tmp27, lambda3;
        tmp27 = mmapl(label, xs);
        lambda3 = (undefined, function (ts) {
          let tmp28;
          tmp28 = Node1([
            n,
            x
          ], ts);
          return retURN(tmp28)
        });
        return bind(tmp27, lambda3)
      });
      return bind(incr, lambda2)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp26 = label(t);
  return startingWith(tmp26, 0)
};
ltGraph = function ltGraph(t) {
  let labelOf, param0, param1, first1, first0, n, x, xs, tmp26, tmp27, tmp28;
  labelOf = function labelOf(t1) {
    let param01, param11, first11, first01, n1, x1, xs1;
    if (t1 instanceof Node1.class) {
      param01 = t1.a;
      param11 = t1.b;
      if (globalThis.Array.isArray(param01) && param01.length === 2) {
        first01 = param01[0];
        first11 = param01[1];
        n1 = first01;
        x1 = first11;
        xs1 = param11;
        return n1
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  if (t instanceof Node1.class) {
    param0 = t.a;
    param1 = t.b;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      n = first0;
      x = first1;
      xs = param1;
      tmp26 = NofibPrelude.map(labelOf, xs);
      tmp27 = NofibPrelude.map(ltGraph, xs);
      tmp28 = NofibPrelude.concat(tmp27);
      return NofibPrelude.Cons([
        n,
        x,
        tmp26
      ], tmp28)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
visited = function visited(n) {
  let tmp26, lambda2;
  lambda2 = (undefined, function (us) {
    let scrut, tmp27, tmp28, lambda3;
    scrut = NofibPrelude.inList(n, us);
    if (scrut === true) {
      return retURN(true)
    } else {
      tmp27 = NofibPrelude.Cons(n, us);
      tmp28 = set_(tmp27);
      lambda3 = (undefined, function (_p) {
        return retURN(false)
      });
      return bind(tmp28, lambda3)
    }
  });
  tmp26 = lambda2;
  return bind(fetch, tmp26)
};
newlyDefined = function newlyDefined(x, fx, f, y) {
  let scrut;
  scrut = x === y;
  if (scrut === true) {
    return fx
  } else {
    return runtime.safeCall(f(y))
  }
};
findCommon = function findCommon(ls) {
  let sim, scrut, first1, first0, a1, b1, tmp26, lambda2;
  sim = function sim(n_s_cs, r_lg) {
    let lscomp, first2, first11, first01, n, s, cs, first12, first02, r, lg, rcs, ms, scrut1, tmp27, tmp28, tmp29, lambda3;
    if (globalThis.Array.isArray(n_s_cs) && n_s_cs.length === 3) {
      first01 = n_s_cs[0];
      first11 = n_s_cs[1];
      first2 = n_s_cs[2];
      n = first01;
      s = first11;
      cs = first2;
      if (globalThis.Array.isArray(r_lg) && r_lg.length === 2) {
        first02 = r_lg[0];
        first12 = r_lg[1];
        r = first02;
        lg = first12;
        lscomp = function lscomp(ls1) {
          let param0, param1, first21, first13, first03, m, s_, cs_, t, scrut2, scrut3, tmp30;
          if (ls1 instanceof NofibPrelude.Nil.class) {
            return NofibPrelude.Nil
          } else if (ls1 instanceof NofibPrelude.Cons.class) {
            param0 = ls1.head;
            param1 = ls1.tail;
            if (globalThis.Array.isArray(param0) && param0.length === 3) {
              first03 = param0[0];
              first13 = param0[1];
              first21 = param0[2];
              m = first03;
              s_ = first13;
              cs_ = first21;
              t = param1;
              scrut2 = s === s_;
              if (scrut2 === true) {
                scrut3 = NofibPrelude.listEq(cs_, rcs);
                if (scrut3 === true) {
                  tmp30 = lscomp(t);
                  return NofibPrelude.Cons(m, tmp30)
                } else {
                  return lscomp(t)
                }
              } else {
                return lscomp(t)
              }
            } else {
              throw new globalThis.Error("match error");
            }
          } else {
            throw new globalThis.Error("match error");
          }
        };
        tmp27 = NofibPrelude.map(r, cs);
        rcs = tmp27;
        tmp28 = lscomp(lg);
        ms = tmp28;
        scrut1 = NofibPrelude.null_(ms);
        if (scrut1 === true) {
          tmp29 = NofibPrelude.Cons([
            n,
            s,
            rcs
          ], lg);
          return [
            r,
            tmp29
          ]
        } else {
          lambda3 = (undefined, function (x) {
            let tmp30;
            tmp30 = NofibPrelude.head(ms);
            return newlyDefined(n, tmp30, r, x)
          });
          return [
            lambda3,
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
  lambda2 = (undefined, function (x) {
    return x
  });
  scrut = NofibPrelude.foldr(sim, [
    lambda2,
    NofibPrelude.Nil
  ], ls);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    a1 = first0;
    b1 = first1;
    return b1
  } else {
    tmp26 = runtime.safeCall(ls.toString());
    throw globalThis.Error(tmp26);
  }
};
cse_ = function cse_(t) {
  let tmp26, tmp27;
  tmp26 = labelTree(t);
  tmp27 = ltGraph(tmp26);
  return findCommon(tmp27)
};
plus_ = function plus_(x, y) {
  let tmp26, tmp27;
  tmp26 = NofibPrelude.Cons(y, NofibPrelude.Nil);
  tmp27 = NofibPrelude.Cons(x, tmp26);
  return Node1("+", tmp27)
};
mult_ = function mult_(x, y) {
  let tmp26, tmp27;
  tmp26 = NofibPrelude.Cons(y, NofibPrelude.Nil);
  tmp27 = NofibPrelude.Cons(x, tmp26);
  return Node1("*", tmp27)
};
prod = function prod(xs) {
  return Node1("X", xs)
};
testCse_nofib = function testCse_nofib(n) {
  let tmp26, tmp27, lambda2;
  lambda2 = (undefined, function (i) {
    let tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35;
    tmp28 = NofibPrelude.intMod(i, 6);
    tmp29 = NofibPrelude.Cons(example5, NofibPrelude.Nil);
    tmp30 = NofibPrelude.Cons(example4, tmp29);
    tmp31 = NofibPrelude.Cons(example3, tmp30);
    tmp32 = NofibPrelude.Cons(example2, tmp31);
    tmp33 = NofibPrelude.Cons(example1, tmp32);
    tmp34 = NofibPrelude.Cons(example0, tmp33);
    tmp35 = NofibPrelude.take(tmp28, tmp34);
    return NofibPrelude.map(cse_, tmp35)
  });
  tmp26 = lambda2;
  tmp27 = NofibPrelude.enumFromTo(1, n);
  return NofibPrelude.map(tmp26, tmp27)
};
lambda = (undefined, function (x) {
  return x + 1
});
tmp = update(lambda);
incr = tmp;
Node1 = function Node(a2, b2) {
  return new Node.class(a2, b2);
};
Node1.class = class Node {
  constructor(a1, b1) {
    this.a = a1;
    this.b = b1;
  }
  toString() { return "Node(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
};
tmp1 = Node1("0", NofibPrelude.Nil);
zerO = tmp1;
tmp2 = Node1("a", NofibPrelude.Nil);
a = tmp2;
tmp3 = Node1("b", NofibPrelude.Nil);
b = tmp3;
tmp4 = Node1("c", NofibPrelude.Nil);
c = tmp4;
tmp5 = Node1("d", NofibPrelude.Nil);
d = tmp5;
example0 = a;
tmp6 = plus_(a, a);
example1 = tmp6;
tmp7 = mult_(a, b);
tmp8 = mult_(a, b);
tmp9 = plus_(tmp7, tmp8);
example2 = tmp9;
tmp10 = plus_(a, b);
tmp11 = mult_(tmp10, c);
tmp12 = plus_(a, b);
tmp13 = plus_(tmp11, tmp12);
example3 = tmp13;
tmp14 = NofibPrelude.Cons(d, NofibPrelude.Nil);
tmp15 = NofibPrelude.Cons(c, tmp14);
tmp16 = NofibPrelude.Cons(b, tmp15);
tmp17 = NofibPrelude.Cons(a, tmp16);
tmp18 = NofibPrelude.scanl(plus_, zerO, tmp17);
tmp19 = prod(tmp18);
example4 = tmp19;
tmp20 = NofibPrelude.Cons(d, NofibPrelude.Nil);
tmp21 = NofibPrelude.Cons(c, tmp20);
tmp22 = NofibPrelude.Cons(b, tmp21);
tmp23 = NofibPrelude.Cons(a, tmp22);
tmp24 = NofibPrelude.scanr(plus_, zerO, tmp23);
tmp25 = prod(tmp24);
example5 = tmp25;
lambda1 = (undefined, function () {
  let tmp26;
  tmp26 = testCse_nofib(6);
  return runtime.safeCall(tmp26.toString())
});
BenchmarkPrelude.benchmark(lambda1)