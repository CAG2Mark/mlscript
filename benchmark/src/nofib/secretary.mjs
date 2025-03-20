import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let secretary1;
secretary1 = class secretary {
  static {
    let lambda;
    lambda = (undefined, function () {
      let tmp;
      tmp = secretary.testSecretary_nofib(50);
      return runtime.safeCall(tmp.toString())
    });
    BenchmarkPrelude.benchmark(lambda)
  }
  static infRand(m, s) {
    let f;
    f = function f(x) {
      let tmp, lambda;
      lambda = (undefined, function () {
        let tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
        tmp1 = NofibPrelude.intMod(x, m);
        tmp2 = tmp1 + 1;
        tmp3 = 97 * x;
        tmp4 = tmp3 + 11;
        tmp5 = NofibPrelude.power(2, 7);
        tmp6 = NofibPrelude.intMod(tmp4, tmp5);
        tmp7 = f(tmp6);
        return NofibPrelude.LzCons(tmp2, tmp7)
      });
      tmp = lambda;
      return NofibPrelude.lazy(tmp)
    };
    return f(s)
  } 
  static simulate(n, m1, proc) {
    let lscomp, tmp, tmp1, tmp2, tmp3, lambda;
    lscomp = function lscomp(ls) {
      let param0, param1, seed, t, tmp4, tmp5, tmp6;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        seed = param0;
        t = param1;
        tmp4 = secretary.infRand(m1, seed);
        tmp5 = runtime.safeCall(proc(tmp4));
        tmp6 = lscomp(t);
        return NofibPrelude.Cons(tmp5, tmp6)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = NofibPrelude.enumFromTo(1, n);
    tmp1 = lscomp(tmp);
    lambda = (undefined, function (x) {
      return x
    });
    tmp2 = NofibPrelude.filter(lambda, tmp1);
    tmp3 = NofibPrelude.listLen(tmp2);
    return tmp3 / n
  } 
  static sim(n1, k) {
    let proc1;
    proc1 = function proc(rs) {
      let xs, best, bestk, afterk, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, lambda;
      tmp = NofibPrelude.nub_lz(rs);
      tmp1 = NofibPrelude.take_lz(100, tmp);
      xs = tmp1;
      best = 100;
      tmp2 = NofibPrelude.take(k, xs);
      tmp3 = NofibPrelude.maximum(tmp2);
      bestk = tmp3;
      tmp4 = NofibPrelude.drop(k, xs);
      lambda = (undefined, function (x) {
        return x < bestk
      });
      tmp5 = NofibPrelude.dropWhile(lambda, tmp4);
      afterk = tmp5;
      tmp6 = NofibPrelude.Cons(best, NofibPrelude.Nil);
      tmp7 = NofibPrelude.take(1, afterk);
      return NofibPrelude.listEq(tmp6, tmp7)
    };
    return secretary.simulate(n1, 100, proc1)
  } 
  static testSecretary_nofib(n2) {
    let listcomp, tmp;
    listcomp = function listcomp(ls) {
      let param0, param1, h, t, tmp1, tmp2;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        h = param0;
        t = param1;
        tmp1 = secretary.sim(n2, h);
        tmp2 = listcomp(t);
        return NofibPrelude.Cons(tmp1, tmp2)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = NofibPrelude.enumFromTo(35, 39);
    return listcomp(tmp)
  }
  static toString() { return "secretary"; }
};
let secretary = secretary1; export default secretary;
