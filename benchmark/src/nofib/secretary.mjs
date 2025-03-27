import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let f, lscomp, proc, listcomp, secretary1, lambda, lambda1, lambda2, f$, lambda$, lscomp$, proc$, lambda$1, listcomp$;
listcomp$ = function listcomp$(n, ls) {
  let param0, param1, h, t, tmp, tmp1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    tmp = secretary1.sim(n, h);
    tmp1 = listcomp$(n, t);
    return NofibPrelude.Cons(tmp, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
listcomp = function listcomp(n) {
  return (ls) => {
    return listcomp$(n, ls)
  }
};
lambda$1 = function lambda$(bestk, x) {
  return x < bestk
};
lambda2 = (undefined, function (bestk) {
  return (x) => {
    return lambda$1(bestk, x)
  }
});
proc$ = function proc$(k, rs) {
  let xs, best, bestk, afterk, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, lambda$this;
  tmp = NofibPrelude.nub_lz(rs);
  tmp1 = NofibPrelude.take_lz(100, tmp);
  xs = tmp1;
  best = 100;
  tmp2 = NofibPrelude.take(k, xs);
  tmp3 = NofibPrelude.maximum(tmp2);
  bestk = tmp3;
  tmp4 = NofibPrelude.drop(k, xs);
  lambda$this = runtime.safeCall(lambda2(bestk));
  tmp5 = NofibPrelude.dropWhile(lambda$this, tmp4);
  afterk = tmp5;
  tmp6 = NofibPrelude.Cons(best, NofibPrelude.Nil);
  tmp7 = NofibPrelude.take(1, afterk);
  return NofibPrelude.listEq(tmp6, tmp7)
};
proc = function proc(k) {
  return (rs) => {
    return proc$(k, rs)
  }
};
lscomp$ = function lscomp$(m, proc1, ls) {
  let param0, param1, seed, t, tmp, tmp1, tmp2;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    seed = param0;
    t = param1;
    tmp = secretary1.infRand(m, seed);
    tmp1 = runtime.safeCall(proc1(tmp));
    tmp2 = lscomp$(m, proc1, t);
    return NofibPrelude.Cons(tmp1, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp = function lscomp(m, proc1) {
  return (ls) => {
    return lscomp$(m, proc1, ls)
  }
};
lambda1 = (undefined, function (x) {
  return x
});
lambda$ = function lambda$(m, x) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
  tmp = NofibPrelude.intMod(x, m);
  tmp1 = tmp + 1;
  tmp2 = 97 * x;
  tmp3 = tmp2 + 11;
  tmp4 = NofibPrelude.power(2, 7);
  tmp5 = NofibPrelude.intMod(tmp3, tmp4);
  tmp6 = f$(m, tmp5);
  return NofibPrelude.LzCons(tmp1, tmp6)
};
lambda = (undefined, function (m, x) {
  return () => {
    return lambda$(m, x)
  }
});
f$ = function f$(m, x) {
  let tmp;
  tmp = runtime.safeCall(lambda(m, x));
  return NofibPrelude.lazy(tmp)
};
f = function f(m) {
  return (x) => {
    return f$(m, x)
  }
};
secretary1 = class secretary {
  static {
    secretary1 = secretary;
    let lambda3;
    lambda3 = (undefined, function () {
      let tmp;
      tmp = secretary.testSecretary_nofib(50);
      return runtime.safeCall(tmp.toString())
    });
    BenchmarkPrelude.benchmark(lambda3)
  }
  static infRand(m, s) {
    return f$(m, s)
  } 
  static simulate(n, m1, proc1) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = NofibPrelude.enumFromTo(1, n);
    tmp1 = lscomp$(m1, proc1, tmp);
    tmp2 = NofibPrelude.filter(lambda1, tmp1);
    tmp3 = NofibPrelude.listLen(tmp2);
    return tmp3 / n
  } 
  static sim(n1, k) {
    let proc$this;
    proc$this = runtime.safeCall(proc(k));
    return secretary.simulate(n1, 100, proc$this)
  } 
  static testSecretary_nofib(n2) {
    let tmp;
    tmp = NofibPrelude.enumFromTo(35, 39);
    return listcomp$(n2, tmp)
  }
  static toString() { return "secretary"; }
};
let secretary = secretary1; export default secretary;
