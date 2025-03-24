import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let primetest1;
primetest1 = class primetest {
  static {
    primetest1 = primetest;
    let lambda;
    lambda = (undefined, function () {
      let tmp;
      tmp = primetest.testPrimetest_nofib(0);
      return runtime.safeCall(tmp.toString())
    });
    BenchmarkPrelude.benchmark(lambda)
  }
  static even(x) {
    let tmp;
    tmp = NofibPrelude.intMod(x, 2);
    return tmp == 0
  } 
  static int_val_of_char(x1) {
    let tmp;
    tmp = NofibPrelude.int_of_char(x1);
    return tmp - 48
  } 
  static int_val_of_string(s) {
    let f;
    f = function f(l, a) {
      let param0, param1, h, t, tmp, tmp1, tmp2;
      if (l instanceof NofibPrelude.Nil.class) {
        return a
      } else if (l instanceof NofibPrelude.Cons.class) {
        param0 = l.head;
        param1 = l.tail;
        h = param0;
        t = param1;
        tmp = 10 * a;
        tmp1 = primetest.int_val_of_char(h);
        tmp2 = tmp + tmp1;
        return f(t, tmp2)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    return f(s, 0)
  } 
  static break_(p, ls) {
    let param0, param1, x2, xs, scrut, first1, first0, ys, zs, scrut1, tmp, tmp1;
    if (ls instanceof NofibPrelude.Nil.class) {
      return [
        NofibPrelude.Nil,
        NofibPrelude.Nil
      ]
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x2 = param0;
      xs = param1;
      scrut1 = runtime.safeCall(p(x2));
      if (scrut1 === true) {
        tmp = NofibPrelude.Cons(x2, xs);
        return [
          NofibPrelude.Nil,
          tmp
        ]
      } else {
        scrut = primetest.break_(p, xs);
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first0 = scrut[0];
          first1 = scrut[1];
          ys = first0;
          zs = first1;
          tmp1 = NofibPrelude.Cons(x2, ys);
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
  static lines(s1) {
    let scrut, first1, first0, l, s_, tt, param0, param1, s__, tmp, lambda;
    lambda = (undefined, function (x2) {
      return x2 == "|"
    });
    scrut = primetest.break_(lambda, s1);
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
        tmp = primetest.lines(s__);
      } else {
        throw new globalThis.Error("match error");
      }
      tt = tmp;
      return NofibPrelude.Cons(l, tt)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static makeNumber(b, ls1) {
    let lambda;
    lambda = (undefined, function (a, x2) {
      let tmp;
      tmp = a * b;
      return tmp + x2
    });
    return NofibPrelude.foldl(lambda, 0, ls1)
  } 
  static chop(b1, n) {
    let chop_;
    chop_ = function chop_(a, n1) {
      let scrut, first1, first0, q, r, scrut1, tmp;
      scrut = NofibPrelude.divMod(n1, b1);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        q = first0;
        r = first1;
        scrut1 = n1 == 0;
        if (scrut1 === true) {
          return a
        } else {
          tmp = NofibPrelude.Cons(r, a);
          return chop_(tmp, q)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    return chop_(NofibPrelude.Nil, n)
  } 
  static powerMod(a, b2, m) {
    let f, a_, scrut, tmp;
    f = function f(a1, b3, c) {
      let g, scrut1;
      g = function g(a2, b4) {
        let scrut2, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
        scrut2 = primetest.even(b4);
        if (scrut2 === true) {
          tmp1 = a2 * a2;
          tmp2 = NofibPrelude.intMod(tmp1, m);
          tmp3 = NofibPrelude.intDiv(b4, 2);
          return g(tmp2, tmp3)
        } else {
          tmp4 = b4 - 1;
          tmp5 = a2 * c;
          tmp6 = NofibPrelude.intMod(tmp5, m);
          return f(a2, tmp4, tmp6)
        }
      };
      scrut1 = b3 == 0;
      if (scrut1 === true) {
        return c
      } else {
        return g(a1, b3)
      }
    };
    scrut = b2 == 0;
    if (scrut === true) {
      return 1
    } else {
      a_ = NofibPrelude.intMod(a, m);
      tmp = b2 - 1;
      return f(a_, tmp, a_)
    }
  } 
  static log2(x2) {
    let tmp;
    tmp = primetest.chop(2, x2);
    return NofibPrelude.listLen(tmp)
  } 
  static rands(s11, s2) {
    let k, s1_, s1__, scrut, k_, s2_, s2__, scrut1, z, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, lambda, lambda1;
    tmp = NofibPrelude.intDiv(s11, 53668);
    k = tmp;
    tmp1 = k * 53668;
    tmp2 = s11 - tmp1;
    tmp3 = 40014 * tmp2;
    tmp4 = k * 12211;
    tmp5 = tmp3 - tmp4;
    s1_ = tmp5;
    scrut = s1_ < 0;
    if (scrut === true) {
      tmp6 = s1_ + 2147483563;
    } else {
      tmp6 = s1_;
    }
    s1__ = tmp6;
    tmp7 = NofibPrelude.intDiv(s2, 52774);
    k_ = tmp7;
    tmp8 = k_ * 52774;
    tmp9 = s2 - tmp8;
    tmp10 = 40692 * tmp9;
    tmp11 = k_ * 3791;
    tmp12 = tmp10 - tmp11;
    s2_ = tmp12;
    scrut1 = s2_ < 0;
    if (scrut1 === true) {
      tmp13 = s2_ + 2147483399;
    } else {
      tmp13 = s2_;
    }
    s2__ = tmp13;
    tmp14 = s1__ - s2__;
    z = tmp14;
    scrut2 = z < 1;
    if (scrut2 === true) {
      lambda = (undefined, function () {
        let tmp15, tmp16;
        tmp15 = z + 2147483562;
        tmp16 = primetest.rands(s1__, s2__);
        return NofibPrelude.LzCons(tmp15, tmp16)
      });
      return NofibPrelude.lazy(lambda)
    } else {
      lambda1 = (undefined, function () {
        let tmp15;
        tmp15 = primetest.rands(s1__, s2__);
        return NofibPrelude.LzCons(z, tmp15)
      });
      return NofibPrelude.lazy(lambda1)
    }
  } 
  static randomInts(s12, s21) {
    let scrut, scrut1, scrut2, scrut3;
    scrut = 1 <= s12;
    if (scrut === true) {
      scrut1 = s12 <= 2147483562;
      if (scrut1 === true) {
        scrut2 = 1 <= s21;
        if (scrut2 === true) {
          scrut3 = s21 <= 2147483398;
          if (scrut3 === true) {
            return primetest.rands(s12, s21)
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
  static findKQ(n1) {
    let f, tmp;
    f = function f(k, q) {
      let scrut, first1, first0, d, r, scrut1, tmp1;
      scrut = NofibPrelude.divMod(q, 2);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        d = first0;
        r = first1;
        scrut1 = r == 0;
        if (scrut1 === true) {
          tmp1 = k + 1;
          return f(tmp1, d)
        } else {
          return [
            k,
            q
          ]
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = n1 - 1;
    return f(0, tmp)
  } 
  static uniform(nns, rrs) {
    let param0, param1, n2, ns, param01, param11, r, rs, t, scrut, n3, r1, rs1, tmp, tmp1, tmp2, tmp3, lambda;
    if (nns instanceof NofibPrelude.Cons.class) {
      param0 = nns.head;
      param1 = nns.tail;
      n3 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        if (rrs instanceof NofibPrelude.Cons.class) {
          param01 = rrs.head;
          param11 = rrs.tail;
          r1 = param01;
          rs1 = param11;
          tmp = NofibPrelude.intMod(r1, n3);
          return NofibPrelude.Cons(tmp, NofibPrelude.Nil)
        } else {
          n2 = param0;
          ns = param1;
          throw new globalThis.Error("match error");
        }
      } else {
        n2 = param0;
        ns = param1;
        if (rrs instanceof NofibPrelude.Cons.class) {
          param01 = rrs.head;
          param11 = rrs.tail;
          r = param01;
          rs = param11;
          tmp1 = n2 + 1;
          t = NofibPrelude.intMod(r, tmp1);
          scrut = t == n2;
          if (scrut === true) {
            tmp2 = primetest.uniform(ns, rs);
            return NofibPrelude.Cons(t, tmp2)
          } else {
            lambda = (undefined, function (x3) {
              return NofibPrelude.intMod(x3, 65536)
            });
            tmp3 = NofibPrelude.map(lambda, rs);
            return NofibPrelude.Cons(t, tmp3)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static random(n2, rs) {
    let ns, scrut, first1, first0, rs1, rs2, tmp, tmp1, tmp2, tmp3;
    tmp = primetest.chop(65536, n2);
    ns = tmp;
    tmp1 = NofibPrelude.listLen(ns);
    scrut = NofibPrelude.splitAt_lz(tmp1, rs);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      rs1 = first0;
      rs2 = first1;
      tmp2 = primetest.uniform(ns, rs1);
      tmp3 = primetest.makeNumber(65536, tmp2);
      return [
        tmp3,
        rs2
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static singleTestX(n3, kq, x3) {
    let square, witness, first1, first0, k, q, scrut, param0, param1, t, ts, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    square = function square(x4) {
      let tmp7;
      tmp7 = x4 * x4;
      return NofibPrelude.intMod(tmp7, n3)
    };
    witness = function witness(ls2) {
      let param01, param11, t1, ts1, scrut1, scrut2, tmp7;
      if (ls2 instanceof NofibPrelude.Nil.class) {
        return false
      } else if (ls2 instanceof NofibPrelude.Cons.class) {
        param01 = ls2.head;
        param11 = ls2.tail;
        t1 = param01;
        ts1 = param11;
        tmp7 = n3 - 1;
        scrut2 = t1 == tmp7;
        if (scrut2 === true) {
          return true
        } else {
          scrut1 = t1 == 1;
          if (scrut1 === true) {
            return false
          } else {
            return witness(ts1)
          }
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    if (globalThis.Array.isArray(kq) && kq.length === 2) {
      first0 = kq[0];
      first1 = kq[1];
      k = first0;
      q = first1;
      tmp = primetest.powerMod(x3, q, n3);
      tmp1 = NofibPrelude.iterate(square, tmp);
      scrut = NofibPrelude.take_lz(k, tmp1);
      if (scrut instanceof NofibPrelude.Cons.class) {
        param0 = scrut.head;
        param1 = scrut.tail;
        t = param0;
        ts = param1;
        tmp2 = t == 1;
        tmp3 = n3 - 1;
        tmp4 = t == tmp3;
        tmp5 = tmp2 || tmp4;
        tmp6 = witness(ts);
        return tmp5 || tmp6
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static singleTest(n4, kq1, rs1) {
    let scrut, first1, first0, x4, rs_, tmp, tmp1, tmp2;
    tmp = n4 - 2;
    scrut = primetest.random(tmp, rs1);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      x4 = first0;
      rs_ = first1;
      tmp1 = 2 + x4;
      tmp2 = primetest.singleTestX(n4, kq1, tmp1);
      return [
        tmp2,
        rs_
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static multiTest(k, rs2, n5) {
    let mTest, scrut, tmp, tmp1, tmp2;
    mTest = function mTest(k1, rs3) {
      let scrut1, first1, first0, t, rs_, scrut2, tmp3, tmp4;
      scrut2 = k1 == 0;
      if (scrut2 === true) {
        return [
          true,
          rs3
        ]
      } else {
        tmp3 = primetest.findKQ(n5);
        scrut1 = primetest.singleTest(n5, tmp3, rs3);
        if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
          first0 = scrut1[0];
          first1 = scrut1[1];
          t = first0;
          rs_ = first1;
          if (t === true) {
            tmp4 = k1 - 1;
            return mTest(tmp4, rs_)
          } else {
            return [
              false,
              rs_
            ]
          }
        } else {
          throw new globalThis.Error("match error");
        }
      }
    };
    tmp = n5 <= 1;
    tmp1 = primetest.even(n5);
    scrut = tmp || tmp1;
    if (scrut === true) {
      tmp2 = n5 == 2;
      return [
        tmp2,
        rs2
      ]
    } else {
      return mTest(k, rs2)
    }
  } 
  static doLine(cs, cont, rs3) {
    let n6, scrut, first1, first0, t, rs_, tmp, tmp1, tmp2;
    tmp = primetest.int_val_of_string(cs);
    n6 = tmp;
    scrut = primetest.multiTest(100, rs3, n6);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      t = first0;
      rs_ = first1;
      if (t === true) {
        tmp1 = runtime.safeCall(cont(rs_));
        return NofibPrelude.Cons("Probably prime", tmp1)
      } else {
        tmp2 = runtime.safeCall(cont(rs_));
        return NofibPrelude.Cons("Composite", tmp2)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static doInput(state, lls) {
    let param0, param1, l, ls2, lambda;
    if (lls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (lls instanceof NofibPrelude.Cons.class) {
      param0 = lls.head;
      param1 = lls.tail;
      l = param0;
      ls2 = param1;
      lambda = (undefined, function (state1) {
        return primetest.doInput(state1, ls2)
      });
      return primetest.doLine(l, lambda, state)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static process(process_arg1) {
    let tmp;
    tmp = primetest.randomInts(111, 47);
    return primetest.doInput(tmp, process_arg1)
  } 
  static testPrimetest_nofib(d) {
    let cts, tmp, tmp1;
    tmp = NofibPrelude.nofibStringToList("24|48|47|1317|8901");
    cts = tmp;
    tmp1 = primetest.lines(cts);
    return primetest.process(tmp1)
  }
  static toString() { return "primetest"; }
};
let primetest = primetest1; export default primetest;
