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
  static not(x) {
    return x === false
  } 
  static print(s) {
    return Predef.print(s)
  } 
  static helper(f) {
    let tmp, Cont$func$helper$BenchmarkPrelude$_mls_L0_330_372$1;
    Cont$func$helper$BenchmarkPrelude$_mls_L0_330_372$1 = function Cont$func$helper$BenchmarkPrelude$_mls_L0_330_372$(pc1) {
      return new Cont$func$helper$BenchmarkPrelude$_mls_L0_330_372$.class(pc1);
    };
    Cont$func$helper$BenchmarkPrelude$_mls_L0_330_372$1.class = class Cont$func$helper$BenchmarkPrelude$_mls_L0_330_372$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp1;
        tmp1 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 0) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 1) {
            tmp = Runtime.runStackSafe(500, f);
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 0;
              tmp.contTrace.last.next = this;
              tmp.contTrace.last = this;
              return tmp
            }
            this.pc = 0;
            continue contLoop;
          } else if (this.pc === 0) {
            return true
          }
          break;
        }
      }
      toString() { return "Cont$func$helper$BenchmarkPrelude$_mls_L0_330_372$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    tmp = Runtime.runStackSafe(500, f);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = new Cont$func$helper$BenchmarkPrelude$_mls_L0_330_372$1.class(0);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    return true
  } 
  static benchmark(fn) {
    let start, res, end, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, Cont$func$benchmark$BenchmarkPrelude$_mls_L0_385_805$1;
    Cont$func$benchmark$BenchmarkPrelude$_mls_L0_385_805$1 = function Cont$func$benchmark$BenchmarkPrelude$_mls_L0_385_805$(pc1) {
      return new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_385_805$.class(pc1);
    };
    Cont$func$benchmark$BenchmarkPrelude$_mls_L0_385_805$1.class = class Cont$func$benchmark$BenchmarkPrelude$_mls_L0_385_805$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp6;
        tmp6 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 2) {
          tmp = value$;
        } else if (this.pc === 3) {
          tmp1 = value$;
        } else if (this.pc === 4) {
          tmp2 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 8) {
            tmp = runtime.safeCall(globalThis.performance.now());
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 2;
              tmp.contTrace.last.next = this;
              tmp.contTrace.last = this;
              return tmp
            }
            this.pc = 2;
            continue contLoop;
          } else if (this.pc === 2) {
            start = tmp;
            this.pc = 7;
            continue contLoop;
          } else if (this.pc === 7) {
            tmp1 = BenchmarkPrelude.helper(fn);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 3;
              tmp1.contTrace.last.next = this;
              tmp1.contTrace.last = this;
              return tmp1
            }
            this.pc = 3;
            continue contLoop;
          } else if (this.pc === 3) {
            res = tmp1;
            this.pc = 6;
            continue contLoop;
          } else if (this.pc === 6) {
            tmp2 = runtime.safeCall(globalThis.performance.now());
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 4;
              tmp2.contTrace.last.next = this;
              tmp2.contTrace.last = this;
              return tmp2
            }
            this.pc = 4;
            continue contLoop;
          } else if (this.pc === 4) {
            end = tmp2;
            tmp3 = end - start;
            tmp4 = "Time: " + tmp3;
            tmp5 = tmp4 + "ms";
            this.pc = 5;
            continue contLoop;
          } else if (this.pc === 5) {
            return BenchmarkPrelude.print(tmp5)
          }
          break;
        }
      }
      toString() { return "Cont$func$benchmark$BenchmarkPrelude$_mls_L0_385_805$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    tmp = runtime.safeCall(globalThis.performance.now());
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_385_805$1.class(2);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    start = tmp;
    tmp1 = BenchmarkPrelude.helper(fn);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_385_805$1.class(3);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    res = tmp1;
    tmp2 = runtime.safeCall(globalThis.performance.now());
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_385_805$1.class(4);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    end = tmp2;
    tmp3 = end - start;
    tmp4 = "Time: " + tmp3;
    tmp5 = tmp4 + "ms";
    return BenchmarkPrelude.print(tmp5)
  }
  static toString() { return "BenchmarkPrelude"; }
};
let BenchmarkPrelude = BenchmarkPrelude1; export default BenchmarkPrelude;
