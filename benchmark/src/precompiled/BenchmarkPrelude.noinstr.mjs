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
  static benchmark(fn) {
    let suite, settings, tmp, tmp1, tmp2, tmp3;
    tmp = BenchmarkPrelude.print("benchmarking...");
    tmp1 = new b.Suite();
    suite = tmp1;
    tmp2 = suite.add("main", fn);
    settings = runtime.Unit;
    settings.async = false;
    tmp3 = suite.on("cycle", (event) => {
      let tmp4;
      tmp4 = globalThis.String(event.target);
      return BenchmarkPrelude.print(tmp4)
    });
    return runtime.safeCall(tmp3.run(settings))
  }
  static toString() { return "BenchmarkPrelude"; }
};
let BenchmarkPrelude = BenchmarkPrelude1; export default BenchmarkPrelude;
