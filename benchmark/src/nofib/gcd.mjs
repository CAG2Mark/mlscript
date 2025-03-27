import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let lscomp2, lscomp1, gcd1, lambda, lambda1, lscomp1$, lscomp2$;
lscomp2$ = function lscomp2$(ms, h1, t1, p2) {
  let param0, param1, h2, t2, tmp;
  if (p2 instanceof NofibPrelude.Nil.class) {
    return lscomp1$(ms, t1)
  } else if (p2 instanceof NofibPrelude.Cons.class) {
    param0 = p2.head;
    param1 = p2.tail;
    h2 = param0;
    t2 = param1;
    tmp = lscomp2$(ms, h1, t1, t2);
    return NofibPrelude.Cons([
      h1,
      h2
    ], tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp2 = function lscomp2(ms, h1, t1) {
  return (p2) => {
    return lscomp2$(ms, h1, t1, p2)
  }
};
lscomp1$ = function lscomp1$(ms, p1) {
  let param0, param1, h1, t1;
  if (p1 instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (p1 instanceof NofibPrelude.Cons.class) {
    param0 = p1.head;
    param1 = p1.tail;
    h1 = param0;
    t1 = param1;
    return lscomp2$(ms, h1, t1, ms)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp1 = function lscomp1(ms) {
  return (p1) => {
    return lscomp1$(ms, p1)
  }
};
lambda = (undefined, function (caseScrut) {
  let first1, first0, x, y, tmp;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    x = first0;
    y = first1;
    tmp = gcd1.gcdE(x, y);
    return [
      x,
      y,
      tmp
    ]
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda1 = (undefined, function (caseScrut) {
  let first2, first1, first0, d1, d2, first21, first11, first01, gg, u, v, tmp, tmp1;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    first2 = caseScrut[2];
    d1 = first0;
    d2 = first1;
    if (globalThis.Array.isArray(first2) && first2.length === 3) {
      first01 = first2[0];
      first11 = first2[1];
      first21 = first2[2];
      gg = first01;
      u = first11;
      v = first21;
      tmp = gg + u;
      tmp1 = tmp + v;
      return NofibPrelude.abs(tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
});
gcd1 = class gcd {
  static {
    gcd1 = gcd;
    let lambda2;
    lambda2 = (undefined, function () {
      return gcd.testGcd_nofib(40)
    });
    BenchmarkPrelude.benchmark(lambda2)
  }
  static g(u1u2u3, v1v2v3) {
    let first2, first1, first0, u1, u2, u3, first21, first11, first01, v1, v2, v3, scrut, first12, first02, q, r, scrut1, tmp, tmp1, tmp2, tmp3;
    if (globalThis.Array.isArray(u1u2u3) && u1u2u3.length === 3) {
      first0 = u1u2u3[0];
      first1 = u1u2u3[1];
      first2 = u1u2u3[2];
      u1 = first0;
      u2 = first1;
      u3 = first2;
      if (globalThis.Array.isArray(v1v2v3) && v1v2v3.length === 3) {
        first01 = v1v2v3[0];
        first11 = v1v2v3[1];
        first21 = v1v2v3[2];
        v1 = first01;
        v2 = first11;
        v3 = first21;
        scrut1 = v3 == 0;
        if (scrut1 === true) {
          return [
            u3,
            u1,
            u2
          ]
        } else {
          scrut = NofibPrelude.quotRem(u3, v3);
          if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
            first02 = scrut[0];
            first12 = scrut[1];
            q = first02;
            r = first12;
            tmp = q * v1;
            tmp1 = u1 - tmp;
            tmp2 = q * v2;
            tmp3 = u2 - tmp2;
            return gcd.g([
              v1,
              v2,
              v3
            ], [
              tmp1,
              tmp3,
              r
            ])
          } else {
            throw new globalThis.Error("match error");
          }
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static gcdE(x, y) {
    let scrut;
    scrut = x == 0;
    if (scrut === true) {
      return [
        y,
        0,
        1
      ]
    } else {
      return gcd.g([
        1,
        0,
        x
      ], [
        0,
        1,
        y
      ])
    }
  } 
  static max_(ls) {
    let param0, param1, x1, param01, param11, y1, xs, scrut, x2, tmp, tmp1;
    if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x2 = param0;
      x1 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return x2
      } else if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        y1 = param01;
        xs = param11;
        scrut = x1 < y1;
        if (scrut === true) {
          tmp = NofibPrelude.Cons(y1, xs);
          return gcd.max_(tmp)
        } else {
          tmp1 = NofibPrelude.Cons(x1, xs);
          return gcd.max_(tmp1)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static test(d) {
    let ns, ms, tripls, rs, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    tmp = 5000 + d;
    tmp1 = NofibPrelude.enumFromTo(5000, tmp);
    ns = tmp1;
    tmp2 = 10000 + d;
    tmp3 = NofibPrelude.enumFromTo(10000, tmp2);
    ms = tmp3;
    tmp4 = lambda;
    tmp5 = lscomp1$(ms, ns);
    tmp6 = NofibPrelude.map(tmp4, tmp5);
    tripls = tmp6;
    tmp7 = lambda1;
    tmp8 = NofibPrelude.map(tmp7, tripls);
    rs = tmp8;
    return gcd.max_(rs)
  } 
  static testGcd_nofib(x1) {
    return gcd.test(x1)
  }
  static toString() { return "gcd"; }
};
let gcd = gcd1; export default gcd;
