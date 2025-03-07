import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let doLine, break_, multiTest, int_val_of_char, uniform, findKQ, rands, lines, randomInts, makeNumber, powerMod, random, log2, int_val_of_string, process, doInput, singleTest, testPrimetest_nofib, chop, singleTestX, even, lambda;
even = function even(x) {
  let tmp;
  tmp = NofibPrelude.intMod(x, 2);
  return tmp == 0
};
int_val_of_char = function int_val_of_char(x) {
  let tmp;
  tmp = NofibPrelude.int_of_char(x);
  return tmp - 48
};
int_val_of_string = function int_val_of_string(s) {
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
      tmp1 = int_val_of_char(h);
      tmp2 = tmp + tmp1;
      return f(t, tmp2)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  return f(s, 0)
};
break_ = function break_(p, ls) {
  let param0, param1, x, xs, scrut, first1, first0, ys, zs, scrut1, tmp, tmp1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return [
      NofibPrelude.Nil,
      NofibPrelude.Nil
    ]
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    x = param0;
    xs = param1;
    scrut1 = runtime.safeCall(p(x));
    if (scrut1 === true) {
      tmp = NofibPrelude.Cons(x, xs);
      return [
        NofibPrelude.Nil,
        tmp
      ]
    } else {
      scrut = NofibPrelude.break_(p, xs);
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
};
lines = function lines(s) {
  let scrut, first1, first0, l, s_, tt, param0, param1, s__, tmp, lambda1;
  lambda1 = (undefined, function (x) {
    return x == "|"
  });
  scrut = NofibPrelude.break_(lambda1, s);
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
      tmp = lines(s__);
    } else {
      throw new globalThis.Error("match error");
    }
    tt = tmp;
    return NofibPrelude.Cons(l, tt)
  } else {
    throw new globalThis.Error("match error");
  }
};
makeNumber = function makeNumber(b, ls) {
  let lambda1;
  lambda1 = (undefined, function (a, x) {
    let tmp;
    tmp = a * b;
    return tmp + x
  });
  return NofibPrelude.foldl(lambda1, 0, ls)
};
chop = function chop(b, n) {
  let chop_;
  chop_ = function chop_(a, n1) {
    let scrut, first1, first0, q, r, scrut1, tmp;
    scrut = NofibPrelude.divMod(n1, b);
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
};
powerMod = function powerMod(a, b, m) {
  let f, a_, scrut, tmp;
  f = function f(a1, b1, c) {
    let g, scrut1;
    g = function g(a2, b2) {
      let scrut2, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
      scrut2 = even(b2);
      if (scrut2 === true) {
        tmp1 = a2 * a2;
        tmp2 = NofibPrelude.intMod(tmp1, m);
        tmp3 = NofibPrelude.intDiv(b2, 2);
        return g(tmp2, tmp3)
      } else {
        tmp4 = b2 - 1;
        tmp5 = a2 * c;
        tmp6 = NofibPrelude.intMod(tmp5, m);
        return f(a2, tmp4, tmp6)
      }
    };
    scrut1 = b1 == 0;
    if (scrut1 === true) {
      return c
    } else {
      return g(a1, b1)
    }
  };
  scrut = b == 0;
  if (scrut === true) {
    return 1
  } else {
    a_ = NofibPrelude.intMod(a, m);
    tmp = b - 1;
    return f(a_, tmp, a_)
  }
};
log2 = function log2(x) {
  let tmp;
  tmp = chop(2, x);
  return NofibPrelude.listLen(tmp)
};
rands = function rands(s1, s2) {
  let k, s1_, s1__, scrut, k_, s2_, s2__, scrut1, z, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, lambda1, lambda2;
  tmp = NofibPrelude.intDiv(s1, 53668);
  k = tmp;
  tmp1 = k * 53668;
  tmp2 = s1 - tmp1;
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
    lambda1 = (undefined, function () {
      let tmp15, tmp16;
      tmp15 = z + 2147483562;
      tmp16 = rands(s1__, s2__);
      return NofibPrelude.LzCons(tmp15, tmp16)
    });
    return NofibPrelude.lazy(lambda1)
  } else {
    lambda2 = (undefined, function () {
      let tmp15;
      tmp15 = rands(s1__, s2__);
      return NofibPrelude.LzCons(z, tmp15)
    });
    return NofibPrelude.lazy(lambda2)
  }
};
randomInts = function randomInts(s1, s2) {
  let scrut, scrut1, scrut2, scrut3;
  scrut = 1 <= s1;
  if (scrut === true) {
    scrut1 = s1 <= 2147483562;
    if (scrut1 === true) {
      scrut2 = 1 <= s2;
      if (scrut2 === true) {
        scrut3 = s2 <= 2147483398;
        if (scrut3 === true) {
          return rands(s1, s2)
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
};
findKQ = function findKQ(n) {
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
  tmp = n - 1;
  return f(0, tmp)
};
uniform = function uniform(nns, rrs) {
  let param0, param1, n, ns, param01, param11, r, rs, t, scrut, n1, r1, rs1, tmp, tmp1, tmp2, tmp3, lambda1;
  if (nns instanceof NofibPrelude.Cons.class) {
    param0 = nns.head;
    param1 = nns.tail;
    n1 = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      if (rrs instanceof NofibPrelude.Cons.class) {
        param01 = rrs.head;
        param11 = rrs.tail;
        r1 = param01;
        rs1 = param11;
        tmp = NofibPrelude.intMod(r1, n1);
        return NofibPrelude.Cons(tmp, NofibPrelude.Nil)
      } else {
        n = param0;
        ns = param1;
        throw new globalThis.Error("match error");
      }
    } else {
      n = param0;
      ns = param1;
      if (rrs instanceof NofibPrelude.Cons.class) {
        param01 = rrs.head;
        param11 = rrs.tail;
        r = param01;
        rs = param11;
        tmp1 = n + 1;
        t = NofibPrelude.intMod(r, tmp1);
        scrut = t == n;
        if (scrut === true) {
          tmp2 = uniform(ns, rs);
          return NofibPrelude.Cons(t, tmp2)
        } else {
          lambda1 = (undefined, function (x) {
            return NofibPrelude.intMod(x, 65536)
          });
          tmp3 = NofibPrelude.map(lambda1, rs);
          return NofibPrelude.Cons(t, tmp3)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
random = function random(n, rs) {
  let ns, scrut, first1, first0, rs1, rs2, tmp, tmp1, tmp2, tmp3;
  tmp = chop(65536, n);
  ns = tmp;
  tmp1 = NofibPrelude.listLen(ns);
  scrut = NofibPrelude.splitAt_lz(tmp1, rs);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    rs1 = first0;
    rs2 = first1;
    tmp2 = uniform(ns, rs1);
    tmp3 = makeNumber(65536, tmp2);
    return [
      tmp3,
      rs2
    ]
  } else {
    throw new globalThis.Error("match error");
  }
};
singleTestX = function singleTestX(n, kq, x) {
  let square, witness, first1, first0, k, q, scrut, param0, param1, t, ts, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
  square = function square(x1) {
    let tmp7;
    tmp7 = x1 * x1;
    return NofibPrelude.intMod(tmp7, n)
  };
  witness = function witness(ls) {
    let param01, param11, t1, ts1, scrut1, scrut2, tmp7;
    if (ls instanceof NofibPrelude.Nil.class) {
      return false
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param01 = ls.head;
      param11 = ls.tail;
      t1 = param01;
      ts1 = param11;
      tmp7 = n - 1;
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
    tmp = powerMod(x, q, n);
    tmp1 = NofibPrelude.iterate(square, tmp);
    scrut = NofibPrelude.take_lz(k, tmp1);
    if (scrut instanceof NofibPrelude.Cons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      t = param0;
      ts = param1;
      tmp2 = t == 1;
      tmp3 = n - 1;
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
};
singleTest = function singleTest(n, kq, rs) {
  let scrut, first1, first0, x, rs_, tmp, tmp1, tmp2;
  tmp = n - 2;
  scrut = random(tmp, rs);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    x = first0;
    rs_ = first1;
    tmp1 = 2 + x;
    tmp2 = singleTestX(n, kq, tmp1);
    return [
      tmp2,
      rs_
    ]
  } else {
    throw new globalThis.Error("match error");
  }
};
multiTest = function multiTest(k, rs, n) {
  let mTest, scrut, tmp, tmp1, tmp2;
  mTest = function mTest(k1, rs1) {
    let scrut1, first1, first0, t, rs_, scrut2, tmp3, tmp4;
    scrut2 = k1 == 0;
    if (scrut2 === true) {
      return [
        true,
        rs1
      ]
    } else {
      tmp3 = findKQ(n);
      scrut1 = singleTest(n, tmp3, rs1);
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
  tmp = n <= 1;
  tmp1 = even(n);
  scrut = tmp || tmp1;
  if (scrut === true) {
    tmp2 = n == 2;
    return [
      tmp2,
      rs
    ]
  } else {
    return mTest(k, rs)
  }
};
doLine = function doLine(cs, cont, rs) {
  let n, scrut, first1, first0, t, rs_, tmp, tmp1, tmp2;
  tmp = int_val_of_string(cs);
  n = tmp;
  scrut = multiTest(100, rs, n);
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
};
doInput = function doInput(state, lls) {
  let param0, param1, l, ls, lambda1;
  if (lls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (lls instanceof NofibPrelude.Cons.class) {
    param0 = lls.head;
    param1 = lls.tail;
    l = param0;
    ls = param1;
    lambda1 = (undefined, function (state1) {
      return doInput(state1, ls)
    });
    return doLine(l, lambda1, state)
  } else {
    throw new globalThis.Error("match error");
  }
};
process = function process(process_arg1) {
  let tmp;
  tmp = randomInts(111, 47);
  return doInput(tmp, process_arg1)
};
testPrimetest_nofib = function testPrimetest_nofib(d) {
  let cts, tmp, tmp1;
  tmp = NofibPrelude.nofibStringToList("24|48|47|1317|8901");
  cts = tmp;
  tmp1 = lines(cts);
  return process(tmp1)
};
lambda = (undefined, function () {
  let tmp;
  tmp = testPrimetest_nofib(0);
  return runtime.safeCall(tmp.toString())
});
BenchmarkPrelude.benchmark(lambda)