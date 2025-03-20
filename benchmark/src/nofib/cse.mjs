import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let cse1;
cse1 = class cse {
  static #incr;
  static #zerO;
  static #a;
  static #b;
  static #c;
  static #d;
  static #example0;
  static #example1;
  static #example2;
  static #example3;
  static #example4;
  static #example5;
  static {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, lambda, lambda1;
    lambda = (undefined, function (x) {
      return x + 1
    });
    tmp = cse.update(lambda);
    cse.#incr = tmp;
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
    cse.#zerO = tmp1;
    tmp2 = cse.Node("a", NofibPrelude.Nil);
    cse.#a = tmp2;
    tmp3 = cse.Node("b", NofibPrelude.Nil);
    cse.#b = tmp3;
    tmp4 = cse.Node("c", NofibPrelude.Nil);
    cse.#c = tmp4;
    tmp5 = cse.Node("d", NofibPrelude.Nil);
    cse.#d = tmp5;
    cse.#example0 = cse.#a;
    tmp6 = cse.plus_(cse.#a, cse.#a);
    cse.#example1 = tmp6;
    tmp7 = cse.mult_(cse.#a, cse.#b);
    tmp8 = cse.mult_(cse.#a, cse.#b);
    tmp9 = cse.plus_(tmp7, tmp8);
    cse.#example2 = tmp9;
    tmp10 = cse.plus_(cse.#a, cse.#b);
    tmp11 = cse.mult_(tmp10, cse.#c);
    tmp12 = cse.plus_(cse.#a, cse.#b);
    tmp13 = cse.plus_(tmp11, tmp12);
    cse.#example3 = tmp13;
    tmp14 = NofibPrelude.Cons(cse.#d, NofibPrelude.Nil);
    tmp15 = NofibPrelude.Cons(cse.#c, tmp14);
    tmp16 = NofibPrelude.Cons(cse.#b, tmp15);
    tmp17 = NofibPrelude.Cons(cse.#a, tmp16);
    tmp18 = NofibPrelude.scanl(cse.plus_, cse.#zerO, tmp17);
    tmp19 = cse.prod(tmp18);
    cse.#example4 = tmp19;
    tmp20 = NofibPrelude.Cons(cse.#d, NofibPrelude.Nil);
    tmp21 = NofibPrelude.Cons(cse.#c, tmp20);
    tmp22 = NofibPrelude.Cons(cse.#b, tmp21);
    tmp23 = NofibPrelude.Cons(cse.#a, tmp22);
    tmp24 = NofibPrelude.scanr(cse.plus_, cse.#zerO, tmp23);
    tmp25 = cse.prod(tmp24);
    cse.#example5 = tmp25;
    lambda1 = (undefined, function () {
      let tmp26;
      tmp26 = cse.testCse_nofib(6);
      return runtime.safeCall(tmp26.toString())
    });
    BenchmarkPrelude.benchmark(lambda1)
  }
  static retURN(a) {
    let lambda;
    lambda = (undefined, function (s) {
      return [
        s,
        a
      ]
    });
    return lambda
  } 
  static bind(m, f) {
    let lambda;
    lambda = (undefined, function (s) {
      let scrut, first1, first0, s_, a1, tmp;
      scrut = runtime.safeCall(m(s));
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        s_ = first0;
        a1 = first1;
        tmp = runtime.safeCall(f(a1));
        return runtime.safeCall(tmp(s_))
      } else {
        throw new globalThis.Error("match error");
      }
    });
    return lambda
  } 
  static join(m1) {
    let lambda;
    lambda = (undefined, function (s) {
      let scrut, first1, first0, s_, ma;
      scrut = runtime.safeCall(m1(s));
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
    return lambda
  } 
  static mmap(f1, m2) {
    let lambda;
    lambda = (undefined, function (s) {
      let scrut, first1, first0, s_, a1, tmp;
      scrut = runtime.safeCall(m2(s));
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        s_ = first0;
        a1 = first1;
        tmp = runtime.safeCall(f1(a1));
        return [
          s_,
          tmp
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    });
    return lambda
  } 
  static mmapl(f2, aas) {
    let param0, param1, a1, as_, tmp, lambda;
    if (aas instanceof NofibPrelude.Nil.class) {
      return cse.retURN(NofibPrelude.Nil)
    } else if (aas instanceof NofibPrelude.Cons.class) {
      param0 = aas.head;
      param1 = aas.tail;
      a1 = param0;
      as_ = param1;
      tmp = runtime.safeCall(f2(a1));
      lambda = (undefined, function (b) {
        let tmp1, lambda1;
        tmp1 = cse.mmapl(f2, as_);
        lambda1 = (undefined, function (bs) {
          let tmp2;
          tmp2 = NofibPrelude.Cons(b, bs);
          return cse.retURN(tmp2)
        });
        return cse.bind(tmp1, lambda1)
      });
      return cse.bind(tmp, lambda)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static mmapr(f3, xs) {
    let param0, param1, x, xs1, tmp, lambda;
    if (xs instanceof NofibPrelude.Nil.class) {
      return cse.retURN(NofibPrelude.Nil)
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param0 = xs.head;
      param1 = xs.tail;
      x = param0;
      xs1 = param1;
      tmp = cse.mmapr(f3, xs1);
      lambda = (undefined, function (ys) {
        let tmp1, lambda1;
        tmp1 = runtime.safeCall(f3(x));
        lambda1 = (undefined, function (y) {
          let tmp2;
          tmp2 = NofibPrelude.Cons(y, ys);
          return cse.retURN(tmp2)
        });
        return cse.bind(tmp1, lambda1)
      });
      return cse.bind(tmp, lambda)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static mfoldl(f4, a1, xs1) {
    let param0, param1, x, xs2, tmp, lambda;
    if (xs1 instanceof NofibPrelude.Nil.class) {
      return cse.retURN(a1)
    } else if (xs1 instanceof NofibPrelude.Cons.class) {
      param0 = xs1.head;
      param1 = xs1.tail;
      x = param0;
      xs2 = param1;
      tmp = runtime.safeCall(f4(a1, x));
      lambda = (undefined, function (fax) {
        return cse.mfoldl(f4, fax, xs2)
      });
      return cse.bind(tmp, lambda)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static mfoldr(f5, a2, xs2) {
    let param0, param1, x, xs3, tmp, lambda;
    if (xs2 instanceof NofibPrelude.Nil.class) {
      return cse.retURN(a2)
    } else if (xs2 instanceof NofibPrelude.Cons.class) {
      param0 = xs2.head;
      param1 = xs2.tail;
      x = param0;
      xs3 = param1;
      tmp = cse.mfoldr(f5, a2, xs3);
      lambda = (undefined, function (y) {
        return runtime.safeCall(f5(x, y))
      });
      return cse.bind(tmp, lambda)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static mif(c, t, f6) {
    let lambda;
    lambda = (undefined, function (cond) {
      if (cond === true) {
        return t
      } else {
        return f6
      }
    });
    return cse.bind(c, lambda)
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
    let lambda;
    lambda = (undefined, function (s1) {
      let tmp;
      tmp = runtime.safeCall(f7(s1));
      return [
        s1,
        tmp
      ]
    });
    return lambda
  } 
  static update(f8) {
    let lambda;
    lambda = (undefined, function (s1) {
      let tmp;
      tmp = runtime.safeCall(f8(s1));
      return [
        tmp,
        s1
      ]
    });
    return lambda
  } 
  static set_(s_) {
    let lambda;
    lambda = (undefined, function (s1) {
      return [
        s_,
        s1
      ]
    });
    return lambda
  } 
  static labelTree(t1) {
    let label, tmp;
    label = function label(t2) {
      let param0, param1, x, xs3, lambda;
      if (t2 instanceof cse.Node.class) {
        param0 = t2.a;
        param1 = t2.b;
        x = param0;
        xs3 = param1;
        lambda = (undefined, function (n) {
          let tmp1, lambda1;
          tmp1 = cse.mmapl(label, xs3);
          lambda1 = (undefined, function (ts) {
            let tmp2;
            tmp2 = cse.Node([
              n,
              x
            ], ts);
            return cse.retURN(tmp2)
          });
          return cse.bind(tmp1, lambda1)
        });
        return cse.bind(cse.#incr, lambda)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = label(t1);
    return cse.startingWith(tmp, 0)
  } 
  static ltGraph(t2) {
    let labelOf, param0, param1, first1, first0, n, x, xs3, tmp, tmp1, tmp2;
    labelOf = function labelOf(t3) {
      let param01, param11, first11, first01, n1, x1, xs4;
      if (t3 instanceof cse.Node.class) {
        param01 = t3.a;
        param11 = t3.b;
        if (globalThis.Array.isArray(param01) && param01.length === 2) {
          first01 = param01[0];
          first11 = param01[1];
          n1 = first01;
          x1 = first11;
          xs4 = param11;
          return n1
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
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
    let tmp, lambda;
    lambda = (undefined, function (us) {
      let scrut, tmp1, tmp2, lambda1;
      scrut = NofibPrelude.inList(n, us);
      if (scrut === true) {
        return cse.retURN(true)
      } else {
        tmp1 = NofibPrelude.Cons(n, us);
        tmp2 = cse.set_(tmp1);
        lambda1 = (undefined, function (_p) {
          return cse.retURN(false)
        });
        return cse.bind(tmp2, lambda1)
      }
    });
    tmp = lambda;
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
    let sim, scrut, first1, first0, a3, b, tmp, lambda;
    sim = function sim(n_s_cs, r_lg) {
      let lscomp, first2, first11, first01, n1, s1, cs, first12, first02, r, lg, rcs, ms, scrut1, tmp1, tmp2, tmp3, lambda1;
      if (globalThis.Array.isArray(n_s_cs) && n_s_cs.length === 3) {
        first01 = n_s_cs[0];
        first11 = n_s_cs[1];
        first2 = n_s_cs[2];
        n1 = first01;
        s1 = first11;
        cs = first2;
        if (globalThis.Array.isArray(r_lg) && r_lg.length === 2) {
          first02 = r_lg[0];
          first12 = r_lg[1];
          r = first02;
          lg = first12;
          lscomp = function lscomp(ls1) {
            let param0, param1, first21, first13, first03, m4, s_1, cs_, t3, scrut2, scrut3, tmp4;
            if (ls1 instanceof NofibPrelude.Nil.class) {
              return NofibPrelude.Nil
            } else if (ls1 instanceof NofibPrelude.Cons.class) {
              param0 = ls1.head;
              param1 = ls1.tail;
              if (globalThis.Array.isArray(param0) && param0.length === 3) {
                first03 = param0[0];
                first13 = param0[1];
                first21 = param0[2];
                m4 = first03;
                s_1 = first13;
                cs_ = first21;
                t3 = param1;
                scrut2 = s1 === s_1;
                if (scrut2 === true) {
                  scrut3 = NofibPrelude.listEq(cs_, rcs);
                  if (scrut3 === true) {
                    tmp4 = lscomp(t3);
                    return NofibPrelude.Cons(m4, tmp4)
                  } else {
                    return lscomp(t3)
                  }
                } else {
                  return lscomp(t3)
                }
              } else {
                throw new globalThis.Error("match error");
              }
            } else {
              throw new globalThis.Error("match error");
            }
          };
          tmp1 = NofibPrelude.map(r, cs);
          rcs = tmp1;
          tmp2 = lscomp(lg);
          ms = tmp2;
          scrut1 = NofibPrelude.null_(ms);
          if (scrut1 === true) {
            tmp3 = NofibPrelude.Cons([
              n1,
              s1,
              rcs
            ], lg);
            return [
              r,
              tmp3
            ]
          } else {
            lambda1 = (undefined, function (x1) {
              let tmp4;
              tmp4 = NofibPrelude.head(ms);
              return cse.newlyDefined(n1, tmp4, r, x1)
            });
            return [
              lambda1,
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
    lambda = (undefined, function (x1) {
      return x1
    });
    scrut = NofibPrelude.foldr(sim, [
      lambda,
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
    let tmp, tmp1, lambda;
    lambda = (undefined, function (i) {
      let tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
      tmp2 = NofibPrelude.intMod(i, 6);
      tmp3 = NofibPrelude.Cons(cse.#example5, NofibPrelude.Nil);
      tmp4 = NofibPrelude.Cons(cse.#example4, tmp3);
      tmp5 = NofibPrelude.Cons(cse.#example3, tmp4);
      tmp6 = NofibPrelude.Cons(cse.#example2, tmp5);
      tmp7 = NofibPrelude.Cons(cse.#example1, tmp6);
      tmp8 = NofibPrelude.Cons(cse.#example0, tmp7);
      tmp9 = NofibPrelude.take(tmp2, tmp8);
      return NofibPrelude.map(cse.cse, tmp9)
    });
    tmp = lambda;
    tmp1 = NofibPrelude.enumFromTo(1, n1);
    return NofibPrelude.map(tmp, tmp1)
  }
  static toString() { return "cse"; }
};
let cse = cse1; export default cse;
