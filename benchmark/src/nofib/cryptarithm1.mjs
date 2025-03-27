import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let lscomp, lscomp2, lscomp1, cryptarithm11, lambda, lscomp$, lscomp1$, lscomp2$;
lambda = (undefined, function (i) {
  let p0, tmp, tmp1, tmp2, tmp3;
  tmp = 9 + i;
  tmp1 = NofibPrelude.enumFromTo(0, tmp);
  tmp2 = NofibPrelude.take(10, tmp1);
  p0 = tmp2;
  tmp3 = cryptarithm11.permutations(p0);
  return NofibPrelude.filter(cryptarithm11.condition, tmp3)
});
lscomp2$ = function lscomp2$(j, t1, p2) {
  let param0, param1, r, t2, tmp;
  if (p2 instanceof NofibPrelude.Nil.class) {
    return lscomp1$(j, t1)
  } else if (p2 instanceof NofibPrelude.Cons.class) {
    param0 = p2.head;
    param1 = p2.tail;
    r = param0;
    t2 = param1;
    tmp = lscomp2$(j, t1, t2);
    return NofibPrelude.Cons(r, tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp2 = function lscomp2(j, t1) {
  return (p2) => {
    return lscomp2$(j, t1, p2)
  }
};
lscomp1$ = function lscomp1$(j, p1) {
  let param0, param1, pjs, t1, tmp;
  if (p1 instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (p1 instanceof NofibPrelude.Cons.class) {
    param0 = p1.head;
    param1 = p1.tail;
    pjs = param0;
    t1 = param1;
    tmp = cryptarithm11.addj(j, pjs);
    return lscomp2$(j, t1, tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp1 = function lscomp1(j) {
  return (p1) => {
    return lscomp1$(j, p1)
  }
};
lscomp$ = function lscomp$(k, p1) {
  let param0, param1, h1, t1, tmp, tmp1;
  if (p1 instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (p1 instanceof NofibPrelude.Cons.class) {
    param0 = p1.head;
    param1 = p1.tail;
    h1 = param0;
    t1 = param1;
    tmp = NofibPrelude.Cons(k, h1);
    tmp1 = lscomp$(k, t1);
    return NofibPrelude.Cons(tmp, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp = function lscomp(k) {
  return (p1) => {
    return lscomp$(k, p1)
  }
};
cryptarithm11 = class cryptarithm1 {
  static {
    cryptarithm11 = cryptarithm1;
    let lambda1;
    lambda1 = (undefined, function () {
      let tmp;
      tmp = cryptarithm1.testCryptarithm_nofib(1);
      return BenchmarkPrelude.print(tmp)
    });
    BenchmarkPrelude.benchmark(lambda1)
  }
  static expand(a, b, c, d, e, f) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    tmp = e * 10;
    tmp1 = f + tmp;
    tmp2 = d * 100;
    tmp3 = tmp1 + tmp2;
    tmp4 = c * 1000;
    tmp5 = tmp3 + tmp4;
    tmp6 = b * 10000;
    tmp7 = tmp5 + tmp6;
    tmp8 = a * 100000;
    return tmp7 + tmp8
  } 
  static condition(thirywelvn) {
    let param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4;
    if (thirywelvn instanceof NofibPrelude.Cons.class) {
      param0 = thirywelvn.head;
      param1 = thirywelvn.tail;
      t = param0;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        h = param01;
        if (param11 instanceof NofibPrelude.Cons.class) {
          param02 = param11.head;
          param12 = param11.tail;
          i = param02;
          if (param12 instanceof NofibPrelude.Cons.class) {
            param03 = param12.head;
            param13 = param12.tail;
            r = param03;
            if (param13 instanceof NofibPrelude.Cons.class) {
              param04 = param13.head;
              param14 = param13.tail;
              y = param04;
              if (param14 instanceof NofibPrelude.Cons.class) {
                param05 = param14.head;
                param15 = param14.tail;
                w = param05;
                if (param15 instanceof NofibPrelude.Cons.class) {
                  param06 = param15.head;
                  param16 = param15.tail;
                  e1 = param06;
                  if (param16 instanceof NofibPrelude.Cons.class) {
                    param07 = param16.head;
                    param17 = param16.tail;
                    l = param07;
                    if (param17 instanceof NofibPrelude.Cons.class) {
                      param08 = param17.head;
                      param18 = param17.tail;
                      v = param08;
                      if (param18 instanceof NofibPrelude.Cons.class) {
                        param09 = param18.head;
                        param19 = param18.tail;
                        n = param09;
                        if (param19 instanceof NofibPrelude.Nil.class) {
                          tmp = cryptarithm1.expand(t, h, i, r, t, y);
                          tmp1 = cryptarithm1.expand(t, w, e1, l, v, e1);
                          tmp2 = 5 * tmp1;
                          tmp3 = tmp + tmp2;
                          tmp4 = cryptarithm1.expand(n, i, n, e1, t, y);
                          return tmp3 == tmp4
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
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static addj(j, ls) {
    let param0, param1, k, ks, tmp, tmp1, tmp2, tmp3, tmp4;
    if (ls instanceof NofibPrelude.Nil.class) {
      tmp = NofibPrelude.Cons(j, NofibPrelude.Nil);
      return NofibPrelude.Cons(tmp, NofibPrelude.Nil)
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      k = param0;
      ks = param1;
      tmp1 = NofibPrelude.Cons(k, ks);
      tmp2 = NofibPrelude.Cons(j, tmp1);
      tmp3 = cryptarithm1.addj(j, ks);
      tmp4 = lscomp$(k, tmp3);
      return NofibPrelude.Cons(tmp2, tmp4)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static permutations(ls1) {
    let param0, param1, j1, js, tmp;
    if (ls1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil)
    } else if (ls1 instanceof NofibPrelude.Cons.class) {
      param0 = ls1.head;
      param1 = ls1.tail;
      j1 = param0;
      js = param1;
      tmp = cryptarithm1.permutations(js);
      return lscomp1$(j1, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static testCryptarithm_nofib(n) {
    let tmp, tmp1;
    tmp = lambda;
    tmp1 = NofibPrelude.enumFromTo(1, n);
    return NofibPrelude.map(tmp, tmp1)
  }
  static toString() { return "cryptarithm1"; }
};
let cryptarithm1 = cryptarithm11; export default cryptarithm1;
