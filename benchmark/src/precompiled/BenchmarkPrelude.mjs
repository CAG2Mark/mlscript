import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import Runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import Predef from "./../../../hkmc2/shared/src/test/mlscript-compile/Predef.mjs";
import NofibPrelude from "./NofibPrelude.mjs";
import benchmark from "benchmark";
let BenchmarkPrelude1, b;
b = benchmark;
BenchmarkPrelude1 = class BenchmarkPrelude {
  static {
    globalThis.Predef = Predef;
    runtime.Unit
  }
  static print(s) {
    return Predef.print(s)
  } 
  static helper(f) {
    let lambda, lambda1;
    lambda = (undefined, function () {
      return runtime.safeCall(f())
    });
    lambda1 = (undefined, function (e) {
      let tmp;
      tmp = "Error: " + e;
      return BenchmarkPrelude.print(tmp)
    });
    return runtime.try_catch(lambda, lambda1)
  } 
  static benchmark(fn) {
    let start, res, end, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = runtime.safeCall(globalThis.Date.now());
    start = tmp;
    tmp1 = BenchmarkPrelude.helper(fn);
    res = tmp1;
    tmp2 = runtime.safeCall(globalThis.Date.now());
    end = tmp2;
    tmp3 = end - start;
    tmp4 = "Time: " + tmp3;
    tmp5 = tmp4 + "ms";
    return BenchmarkPrelude.print(tmp5)
  }
  static toString() { return "BenchmarkPrelude"; }
};
let BenchmarkPrelude = BenchmarkPrelude1; export default BenchmarkPrelude;
