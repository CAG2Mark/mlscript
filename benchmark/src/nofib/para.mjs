import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let para1;
para1 = class para {
  static #maxw;
  static #optw;
  static #nil_;
  static #test;
  static {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, lambda;
    para.#maxw = 70;
    para.#optw = 63;
    para.#nil_ = [
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
    para.#test = tmp20;
    lambda = (undefined, function () {
      let tmp21;
      tmp21 = para.testPara_nofib();
      return NofibPrelude.nofibListToString(tmp21)
    });
    BenchmarkPrelude.benchmark(lambda)
  }
  static unwords(ws) {
    let go, param0, param1, w, ws1, tmp;
    if (ws instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ws instanceof NofibPrelude.Cons.class) {
      param0 = ws.head;
      param1 = ws.tail;
      w = param0;
      ws1 = param1;
      go = function go(vs) {
        let param01, param11, v, vs1, tmp1, tmp2;
        if (vs instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (vs instanceof NofibPrelude.Cons.class) {
          param01 = vs.head;
          param11 = vs.tail;
          v = param01;
          vs1 = param11;
          tmp1 = go(vs1);
          tmp2 = NofibPrelude.append(v, tmp1);
          return NofibPrelude.Cons(" ", tmp2)
        } else {
          throw new globalThis.Error("match error");
        }
      };
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
    let scrut, first1, first0, l, s_, param0, param1, s__, tmp, lambda;
    lambda = (undefined, function (x) {
      return x === "\n"
    });
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
    let tmp, lambda;
    lambda = (undefined, function (l) {
      let tmp1;
      tmp1 = NofibPrelude.nofibStringToList("\n");
      return NofibPrelude.append(l, tmp1)
    });
    tmp = NofibPrelude.map(lambda, ls);
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
    let tmp, lambda, lambda1;
    lambda = (undefined, function (a, s2) {
      let tmp1, tmp2;
      tmp1 = NofibPrelude.head(s2);
      tmp2 = runtime.safeCall(f1(a, tmp1));
      return NofibPrelude.Cons(tmp2, s2)
    });
    tmp = lambda;
    lambda1 = (undefined, function (a) {
      let tmp1;
      tmp1 = runtime.safeCall(g1(a));
      return NofibPrelude.Cons(tmp1, NofibPrelude.Nil)
    });
    return para.fold1(tmp, lambda1, xs3)
  } 
  static tails(xs4) {
    let lambda, lambda1;
    lambda = (undefined, function (a, s2) {
      return NofibPrelude.Cons(a, s2)
    });
    lambda1 = (undefined, function (a) {
      return NofibPrelude.Cons(a, NofibPrelude.Nil)
    });
    return para.scan1(lambda, lambda1, xs4)
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
    let tmp, lambda, lambda1;
    lambda = (undefined, function (a, b) {
      let scrut, tmp1, tmp2;
      tmp1 = runtime.safeCall(f2(a));
      tmp2 = runtime.safeCall(f2(b));
      scrut = tmp1 < tmp2;
      if (scrut === true) {
        return a
      } else {
        return b
      }
    });
    tmp = lambda;
    lambda1 = (undefined, function (x) {
      return x
    });
    return para.fold1(tmp, lambda1, xs6)
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
    let tmp, tmp1, lambda, lambda1;
    lambda = (undefined, function (w2, ps) {
      let tmp2, tmp3, lambda2, lambda3;
      lambda2 = (undefined, function (p2) {
        return para.new_(w2, p2)
      });
      tmp2 = NofibPrelude.map(lambda2, ps);
      lambda3 = (undefined, function (p2) {
        return para.glue(w2, p2)
      });
      tmp3 = NofibPrelude.map(lambda3, ps);
      return NofibPrelude.append(tmp2, tmp3)
    });
    tmp = lambda;
    lambda1 = (undefined, function (x) {
      let tmp2, tmp3;
      tmp2 = NofibPrelude.Cons(x, NofibPrelude.Nil);
      tmp3 = NofibPrelude.Cons(tmp2, NofibPrelude.Nil);
      return NofibPrelude.Cons(tmp3, NofibPrelude.Nil)
    });
    tmp1 = lambda1;
    return para.fold1(tmp, tmp1, txt)
  } 
  static width(ls3) {
    let plus;
    plus = function plus(w2, n) {
      let tmp, tmp1;
      tmp = NofibPrelude.listLen(w2);
      tmp1 = tmp + 1;
      return tmp1 + n
    };
    return para.fold1(plus, NofibPrelude.listLen, ls3)
  } 
  static fits(xs7) {
    let tmp;
    tmp = para.width(xs7);
    return tmp <= para.#maxw
  } 
  static feasible(a) {
    return para.all(para.fits, a)
  } 
  static cost(ls4) {
    let linc, plus, lambda;
    linc = function linc(l) {
      let a1, tmp, tmp1;
      tmp = para.width(l);
      tmp1 = para.#optw - tmp;
      a1 = tmp1;
      return a1 * a1
    };
    plus = function plus(l, n) {
      let tmp;
      tmp = linc(l);
      return tmp + n
    };
    lambda = (undefined, function (x) {
      return 0
    });
    return para.fold1(plus, lambda, ls4)
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
    let tmp, lambda, lambda1;
    lambda = (undefined, function (xs8, ys) {
      let tmp1, tmp2;
      tmp1 = NofibPrelude.Cons(a3, NofibPrelude.Nil);
      tmp2 = NofibPrelude.append(tmp1, ys);
      return NofibPrelude.append(xs8, tmp2)
    });
    tmp = lambda;
    lambda1 = (undefined, function (x1) {
      return x1
    });
    return para.fold1(tmp, lambda1, l)
  } 
  static format(a4, x1) {
    let start, breakk, unknownEq, lambda, lambda1;
    if (x1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil)
    } else {
      unknownEq = function unknownEq(a5, b) {
        return a5 === b
      };
      breakk = function breakk(a5, b, xs8) {
        let scrut, tmp, tmp1, tmp2;
        scrut = unknownEq(a5, b);
        if (scrut === true) {
          return NofibPrelude.Cons(NofibPrelude.Nil, xs8)
        } else {
          tmp = NofibPrelude.head(xs8);
          tmp1 = NofibPrelude.Cons(b, tmp);
          tmp2 = NofibPrelude.tail(xs8);
          return NofibPrelude.Cons(tmp1, tmp2)
        }
      };
      start = function start(a5, b) {
        let tmp;
        tmp = NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil);
        return breakk(a5, b, tmp)
      };
      lambda = (undefined, function (x2, y) {
        return breakk(a4, x2, y)
      });
      lambda1 = (undefined, function (y) {
        return start(a4, y)
      });
      return para.fold1(lambda, lambda1, x1)
    }
  } 
  static unparas(ls6) {
    return para.unformat(NofibPrelude.Nil, ls6)
  } 
  static paras(ls7) {
    let tmp, lambda;
    tmp = para.format(NofibPrelude.Nil, ls7);
    lambda = (undefined, function (x2) {
      return NofibPrelude.listNeq(NofibPrelude.Nil, x2)
    });
    return NofibPrelude.filter(lambda, tmp)
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
    scrut = a5 <= para.#maxw;
    if (scrut === true) {
      tmp = para.cons_([
        0,
        0,
        0
      ], para.#nil_);
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
    let tmp, tmp1, lambda;
    tmp = para.parse(par);
    lambda = (undefined, function (x2) {
      let tmp2;
      tmp2 = NofibPrelude.concat(x2);
      return runtime.safeCall(par(tmp2))
    });
    tmp1 = NofibPrelude.map(lambda, tmp);
    return para.unparse(tmp1)
  } 
  static stepr(w2, ps_tw_tl) {
    let bf, old_width_hd, width_hd, myAdd, single, trim, new_, cost, drop_nofit, first2, first1, first0, ps, tw, tl, tot_width, tot_len, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    if (globalThis.Array.isArray(ps_tw_tl) && ps_tw_tl.length === 3) {
      first0 = ps_tw_tl[0];
      first1 = ps_tw_tl[1];
      first2 = ps_tw_tl[2];
      ps = first0;
      tw = first1;
      tl = first2;
      single = function single(p2) {
        let tmp8;
        tmp8 = para.len_tl(p2);
        return tmp8 === 0
      };
      width_hd = function width_hd(p2) {
        let scrut, tmp8, tmp9;
        scrut = single(p2);
        if (scrut === true) {
          return tot_width
        } else {
          tmp8 = para.width_tl(p2);
          tmp9 = tot_width - tmp8;
          return tmp9 - 1
        }
      };
      cost = function cost(p2) {
        let a6, scrut, tmp8, tmp9, tmp10, tmp11;
        scrut = single(p2);
        if (scrut === true) {
          return 0
        } else {
          tmp8 = para.cost_tl(p2);
          tmp9 = width_hd(p2);
          tmp10 = para.#optw - tmp9;
          a6 = tmp10;
          tmp11 = a6 * a6;
          return tmp8 + tmp11
        }
      };
      old_width_hd = function old_width_hd(p2) {
        let scrut, tmp8, tmp9;
        scrut = single(p2);
        if (scrut === true) {
          return tw
        } else {
          tmp8 = para.width_tl(p2);
          tmp9 = tw - tmp8;
          return tmp9 - 1
        }
      };
      new_ = function new_(p2) {
        let x2, scrut, tmp8, tmp9, tmp10, tmp11, tmp12;
        scrut = single(p2);
        if (scrut === true) {
          return [
            tw,
            0,
            tl
          ]
        } else {
          tmp8 = para.cost_tl(p2);
          tmp9 = old_width_hd(p2);
          tmp10 = para.#optw - tmp9;
          x2 = tmp10;
          tmp11 = x2 * x2;
          tmp12 = tmp8 + tmp11;
          return [
            tw,
            tmp12,
            tl
          ]
        }
      };
      trim = function trim(ps_pq) {
        let ps_p, q, p2, scrut, scrut1, scrut2, tmp8, tmp9;
        scrut2 = para.null__(ps_pq);
        if (scrut2 === true) {
          return ps_pq
        } else {
          scrut1 = para.single_(ps_pq);
          if (scrut1 === true) {
            return ps_pq
          } else {
            ps_p = para.init_(ps_pq);
            q = para.last_(ps_pq);
            p2 = para.last_(ps_p);
            tmp8 = cost(p2);
            tmp9 = cost(q);
            scrut = tmp8 <= tmp9;
            if (scrut === true) {
              return trim(ps_p)
            } else {
              return ps_pq
            }
          }
        }
      };
      drop_nofit = function drop_nofit(ps_p) {
        let scrut, scrut1, tmp8, tmp9, tmp10;
        scrut1 = para.null__(ps_p);
        if (scrut1 === true) {
          return ps_p
        } else {
          tmp8 = para.last_(ps_p);
          tmp9 = width_hd(tmp8);
          scrut = tmp9 > para.#maxw;
          if (scrut === true) {
            tmp10 = para.init_(ps_p);
            return drop_nofit(tmp10)
          } else {
            return ps_p
          }
        }
      };
      bf = function bf(p2, q) {
        let wqh, rqh, scrut, scrut1, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22;
        tmp8 = width_hd(q);
        wqh = tmp8;
        tmp9 = para.#maxw - wqh;
        tmp10 = tmp9 + 1;
        rqh = tmp10;
        tmp11 = single(q);
        tmp12 = para.cost_tl(p2);
        tmp13 = tmp12 === 0;
        scrut1 = tmp11 && tmp13;
        if (scrut1 === true) {
          tmp14 = width_hd(p2);
          tmp15 = para.#optw - tmp14;
          return NofibPrelude.min(tmp15, rqh)
        } else {
          scrut = single(q);
          if (scrut === true) {
            return rqh
          } else {
            tmp16 = cost(p2);
            tmp17 = cost(q);
            tmp18 = tmp16 - tmp17;
            tmp19 = width_hd(p2);
            tmp20 = wqh - tmp19;
            tmp21 = 2 * tmp20;
            tmp22 = para.ceildiv(tmp18, tmp21);
            return NofibPrelude.min(tmp22, rqh)
          }
        }
      };
      myAdd = function myAdd(p2, qr_rs) {
        let q, r_rs, r, scrut, scrut1, tmp8, tmp9, tmp10, tmp11;
        tmp8 = para.single_(qr_rs);
        tmp9 = para.null__(qr_rs);
        scrut1 = tmp8 || tmp9;
        if (scrut1 === true) {
          return para.cons_(p2, qr_rs)
        } else {
          q = para.head_(qr_rs);
          r_rs = para.tail_(qr_rs);
          r = para.head_(r_rs);
          tmp10 = bf(p2, q);
          tmp11 = bf(q, r);
          scrut = tmp10 <= tmp11;
          if (scrut === true) {
            return myAdd(p2, r_rs)
          } else {
            return para.cons_(p2, qr_rs)
          }
        }
      };
      tmp = w2 + 1;
      tmp1 = tmp + tw;
      tot_width = tmp1;
      tmp2 = 1 + tl;
      tot_len = tmp2;
      tmp3 = para.last_(ps);
      tmp4 = new_(tmp3);
      tmp5 = myAdd(tmp4, ps);
      tmp6 = drop_nofit(tmp5);
      tmp7 = trim(tmp6);
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
    let zs, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, lambda;
    tmp = NofibPrelude.map(NofibPrelude.listLen, ws2);
    tmp1 = para.scan1(para.stepr, para.startr, tmp);
    zs = tmp1;
    lambda = (undefined, function (x2) {
      let tmp6, tmp7;
      tmp6 = para.fst3(x2);
      tmp7 = para.last_(tmp6);
      return para.len_tl(tmp7)
    });
    tmp2 = lambda;
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
    scrut = NofibPrelude.null_(para.#test);
    if (scrut === true) {
      return NofibPrelude.Nil
    } else {
      return para.fmt(para.#test)
    }
  }
  static toString() { return "para"; }
};
let para = para1; export default para;
