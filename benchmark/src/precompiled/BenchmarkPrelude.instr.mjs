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
    let res, outerHandler, tmp, handleBlock$, Cont$func$helper$BenchmarkPrelude$_mls_L0_304_721$1;
    Cont$func$helper$BenchmarkPrelude$_mls_L0_304_721$1 = function Cont$func$helper$BenchmarkPrelude$_mls_L0_304_721$(pc1) {
      return new Cont$func$helper$BenchmarkPrelude$_mls_L0_304_721$.class(pc1);
    };
    Cont$func$helper$BenchmarkPrelude$_mls_L0_304_721$1.class = class Cont$func$helper$BenchmarkPrelude$_mls_L0_304_721$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp1;
        tmp1 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 2) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 2) {
            if (tmp instanceof runtime.Return.class) {
              return tmp.value
            }
            this.pc = 3;
            continue contLoop;
          } else if (this.pc === 3) {
            Runtime.stackDepth = 0;
            Runtime.stackHandler = outerHandler;
            return res
          }
          break;
        }
      }
      toString() { return "Cont$func$helper$BenchmarkPrelude$_mls_L0_304_721$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    handleBlock$ = function handleBlock$() {
      let h, tmp1, Cont$handleBlock$h$1, Handler$h$1;
      Handler$h$1 = class Handler$h$ extends Runtime.StackDelay {
        constructor() {
          let tmp2;
          tmp2 = super();
        }
        perform() {
          return runtime.mkEffect(this, (k) => {
            Runtime.stackOffset = Runtime.stackDepth;
            return runtime.safeCall(k(runtime.Unit))
          })
        }
        toString() { return "Handler$h$"; }
      };
      h = new Handler$h$1();
      Cont$handleBlock$h$1 = function Cont$handleBlock$h$(pc1) {
        return new Cont$handleBlock$h$.class(pc1);
      };
      Cont$handleBlock$h$1.class = class Cont$handleBlock$h$ extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp2;
          tmp2 = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 0) {
            tmp1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 1) {
              tmp1 = runtime.safeCall(f());
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 0;
                tmp1.contTrace.last.next = this;
                tmp1.contTrace.last = this;
                return tmp1
              }
              this.pc = 0;
              continue contLoop;
            } else if (this.pc === 0) {
              res = tmp1;
              return runtime.Unit
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$h$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      Runtime.stackLimit = 500;
      Runtime.stackOffset = 0;
      Runtime.stackDepth = 1;
      Runtime.stackHandler = h;
      tmp1 = runtime.safeCall(f());
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = Cont$handleBlock$h$1(0);
        return runtime.handleBlockImpl(tmp1, h)
      }
      res = tmp1;
      return runtime.Unit
    };
    res = undefined;
    outerHandler = Runtime.stackHandler;
    tmp = handleBlock$();
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = new Cont$func$helper$BenchmarkPrelude$_mls_L0_304_721$1.class(2);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    if (tmp instanceof runtime.Return.class) {
      return tmp.value
    }
    Runtime.stackDepth = 0;
    Runtime.stackHandler = outerHandler;
    return res
  } 
  static benchmark(fn) {
    let start, res, end, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, Cont$func$benchmark$BenchmarkPrelude$_mls_L0_727_1133$1;
    Cont$func$benchmark$BenchmarkPrelude$_mls_L0_727_1133$1 = function Cont$func$benchmark$BenchmarkPrelude$_mls_L0_727_1133$(pc1) {
      return new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_727_1133$.class(pc1);
    };
    Cont$func$benchmark$BenchmarkPrelude$_mls_L0_727_1133$1.class = class Cont$func$benchmark$BenchmarkPrelude$_mls_L0_727_1133$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp6;
        tmp6 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 4) {
          tmp = value$;
        } else if (this.pc === 5) {
          tmp1 = value$;
        } else if (this.pc === 6) {
          tmp2 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 10) {
            tmp = runtime.safeCall(globalThis.Date.now());
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 4;
              tmp.contTrace.last.next = this;
              tmp.contTrace.last = this;
              return tmp
            }
            this.pc = 4;
            continue contLoop;
          } else if (this.pc === 4) {
            start = tmp;
            this.pc = 9;
            continue contLoop;
          } else if (this.pc === 9) {
            tmp1 = BenchmarkPrelude.helper(fn);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 5;
              tmp1.contTrace.last.next = this;
              tmp1.contTrace.last = this;
              return tmp1
            }
            this.pc = 5;
            continue contLoop;
          } else if (this.pc === 5) {
            res = tmp1;
            this.pc = 8;
            continue contLoop;
          } else if (this.pc === 8) {
            tmp2 = runtime.safeCall(globalThis.Date.now());
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 6;
              tmp2.contTrace.last.next = this;
              tmp2.contTrace.last = this;
              return tmp2
            }
            this.pc = 6;
            continue contLoop;
          } else if (this.pc === 6) {
            end = tmp2;
            tmp3 = end - start;
            tmp4 = "Time: " + tmp3;
            tmp5 = tmp4 + "ms";
            this.pc = 7;
            continue contLoop;
          } else if (this.pc === 7) {
            return BenchmarkPrelude.print(tmp5)
          }
          break;
        }
      }
      toString() { return "Cont$func$benchmark$BenchmarkPrelude$_mls_L0_727_1133$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    tmp = runtime.safeCall(globalThis.Date.now());
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_727_1133$1.class(4);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    start = tmp;
    tmp1 = BenchmarkPrelude.helper(fn);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_727_1133$1.class(5);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    res = tmp1;
    tmp2 = runtime.safeCall(globalThis.Date.now());
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_727_1133$1.class(6);
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
