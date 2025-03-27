import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import Runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import Predef from "./../../../hkmc2/shared/src/test/mlscript-compile/Predef.mjs";
import NofibPrelude from "./NofibPrelude.mjs";
import benchmark from "benchmark";
let BenchmarkPrelude1, b, lambda, lambda1, lambda$, lambda$1, helper$capture1;
b = benchmark;
lambda$1 = function lambda$(f) {
  return runtime.safeCall(f())
};
lambda = (undefined, function (f) {
  return () => {
    return lambda$1(f)
  }
});
lambda$ = function lambda$(helper$capture2, e) {
  let tmp;
  helper$capture2.success0$ = false;
  tmp = "Error: " + e;
  return Predef.print(tmp)
};
lambda1 = (undefined, function (helper$capture2) {
  return (e) => {
    return lambda$(helper$capture2, e)
  }
});
helper$capture1 = function helper$capture(success0$1) {
  return new helper$capture.class(success0$1);
};
helper$capture1.class = class helper$capture {
  constructor(success0$) {
    this.success0$ = success0$;
  }
  toString() { return "helper$capture(" + globalThis.Predef.render(this.success0$) + ")"; }
};
BenchmarkPrelude1 = class BenchmarkPrelude {
  static {
    BenchmarkPrelude1 = BenchmarkPrelude;
    globalThis.Predef = Predef;
    runtime.Unit
  }
  static not(x) {
    return x === false
  } 
  static print(s) {
    return s
  } 
  static helper(f) {
    let tmp, capture, lambda$this, lambda$this1;
    capture = new helper$capture1(null);
    capture.success0$ = true;
    lambda$this = runtime.safeCall(lambda(f));
    lambda$this1 = runtime.safeCall(lambda1(capture));
    tmp = runtime.try_catch(lambda$this, lambda$this1);
    return capture.success0$
  } 
  static benchmark(fn) {
    let start, res, end, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = runtime.safeCall(globalThis.performance.now());
    start = tmp;
    tmp1 = BenchmarkPrelude.helper(fn);
    res = tmp1;
    tmp2 = runtime.safeCall(globalThis.performance.now());
    end = tmp2;
    if (res === true) {
      tmp3 = end - start;
      tmp4 = "Time: " + tmp3;
      tmp5 = tmp4 + "ms";
      return Predef.print(tmp5)
    } else {
      return runtime.Unit
    }
  }
  static toString() { return "BenchmarkPrelude"; }
};
let BenchmarkPrelude = BenchmarkPrelude1; export default BenchmarkPrelude;
