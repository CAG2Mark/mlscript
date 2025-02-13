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
    let stackDelayRes, Cont$func$print$BenchmarkPrelude$_mls_L0_272_298$1;
    Cont$func$print$BenchmarkPrelude$_mls_L0_272_298$1 = function Cont$func$print$BenchmarkPrelude$_mls_L0_272_298$(pc1, next1) { return new Cont$func$print$BenchmarkPrelude$_mls_L0_272_298$.class(pc1, next1); };
    Cont$func$print$BenchmarkPrelude$_mls_L0_272_298$1.class = class Cont$func$print$BenchmarkPrelude$_mls_L0_272_298$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp;
        tmp = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 0) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 0) {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return Predef.print(s)
          }
          break;
        }
      }
      toString() { return "Cont$func$print$BenchmarkPrelude$_mls_L0_272_298$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$print$BenchmarkPrelude$_mls_L0_272_298$1.class(0, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return Predef.print(s)
  } 
  static helper(f) {
    let res, tmp, handleBlock$, Cont$func$helper$BenchmarkPrelude$_mls_L0_304_671$1;
    Cont$func$helper$BenchmarkPrelude$_mls_L0_304_671$1 = function Cont$func$helper$BenchmarkPrelude$_mls_L0_304_671$(pc1, next1) { return new Cont$func$helper$BenchmarkPrelude$_mls_L0_304_671$.class(pc1, next1); };
    Cont$func$helper$BenchmarkPrelude$_mls_L0_304_671$1.class = class Cont$func$helper$BenchmarkPrelude$_mls_L0_304_671$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp1;
        tmp1 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 7) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 7) {
            if (tmp instanceof runtime.Return.class) {
              this.completed = true;
              return tmp.value
            }
            this.pc = 8;
            continue contLoop;
          } else if (this.pc === 8) {
            Runtime.stackDepth = 0;
            Runtime.stackHandler = null;
            this.completed = true;
            return res
          }
          break;
        }
      }
      toString() { return "Cont$func$helper$BenchmarkPrelude$_mls_L0_304_671$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    handleBlock$ = function handleBlock$() {
      let h, tmp1, curDepth, stackDelayRes, Cont$handleBlock$h$1, Handler$h$1;
      Handler$h$1 = class Handler$h$ extends Runtime.StackDelay {
        constructor() {
          let tmp2;
          tmp2 = super();
        }
        perform() {
          return runtime.mkEffect(h, (k, handleBlock) => {
            let res1, Cont$handler$h$BenchmarkPrelude$_mls_L0_371_4481;
            Cont$handler$h$BenchmarkPrelude$_mls_L0_371_4481 = function Cont$handler$h$BenchmarkPrelude$_mls_L0_371_448(pc1, next1) { return new Cont$handler$h$BenchmarkPrelude$_mls_L0_371_448.class(pc1, next1); };
            Cont$handler$h$BenchmarkPrelude$_mls_L0_371_4481.class = class Cont$handler$h$BenchmarkPrelude$_mls_L0_371_448 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp2;
                tmp2 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 5) {
                  res1 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 5) {
                    if (res1 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res1
                    }
                    this.pc = 6;
                    continue contLoop;
                  } else if (this.pc === 6) {
                    this.completed = true;
                    return res1
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$h$BenchmarkPrelude$_mls_L0_371_448(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            Runtime.stackOffset = Runtime.stackDepth;
            runtime.stackDepth = runtime.stackDepth + 1;
            res1 = runtime.safeCall(k(runtime.Unit));
            if (res1 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$h$BenchmarkPrelude$_mls_L0_371_4481.class(5, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res1
            }
            if (res1 instanceof runtime.Return.class) {
              return res1
            }
            return res1
          })
        }
        toString() { return "Handler$h$"; }
      };
      h = new Handler$h$1();
      Cont$handleBlock$h$1 = function Cont$handleBlock$h$(pc1, next1) { return new Cont$handleBlock$h$.class(pc1, next1); };
      Cont$handleBlock$h$1.class = class Cont$handleBlock$h$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp2;
          tmp2 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 1) {
            stackDelayRes = value$;
          } else if (this.pc === 2) {
            tmp1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 1) {
              if (stackDelayRes instanceof runtime.Return.class) {
                this.completed = true;
                return stackDelayRes
              }
              this.pc = 4;
              continue contLoop;
            } else if (this.pc === 4) {
              Runtime.stackLimit = 500;
              Runtime.stackOffset = 0;
              Runtime.stackDepth = 1;
              Runtime.stackHandler = h;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = runtime.safeCall(f());
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 2;
                return tmp1
              }
              this.pc = 2;
              continue contLoop;
            } else if (this.pc === 2) {
              if (tmp1 instanceof runtime.Return.class) {
                this.completed = true;
                return tmp1
              }
              this.pc = 3;
              continue contLoop;
            } else if (this.pc === 3) {
              tmp1 = runtime.resetDepth(tmp1, curDepth);
              res = tmp1;
              this.completed = true;
              return runtime.Unit
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$h$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.tail.next = new Cont$handleBlock$h$1(1, null);
        return runtime.handleBlockImpl(stackDelayRes, h)
      }
      if (stackDelayRes instanceof runtime.Return.class) {
        return stackDelayRes
      }
      Runtime.stackLimit = 500;
      Runtime.stackOffset = 0;
      Runtime.stackDepth = 1;
      Runtime.stackHandler = h;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = runtime.safeCall(f());
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.tail.next = new Cont$handleBlock$h$1(2, null);
        return runtime.handleBlockImpl(tmp1, h)
      }
      if (tmp1 instanceof runtime.Return.class) {
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      res = tmp1;
      return runtime.Unit
    };
    res = undefined;
    tmp = handleBlock$();
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.tail.next = new Cont$func$helper$BenchmarkPrelude$_mls_L0_304_671$1.class(7, null);
      tmp.tail = tmp.tail.next;
      return tmp
    }
    if (tmp instanceof runtime.Return.class) {
      return tmp.value
    }
    Runtime.stackDepth = 0;
    Runtime.stackHandler = null;
    return res
  } 
  static benchmark(fn) {
    let suite, settings, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, Cont$func$benchmark$BenchmarkPrelude$_mls_L0_677_931$1;
    Cont$func$benchmark$BenchmarkPrelude$_mls_L0_677_931$1 = function Cont$func$benchmark$BenchmarkPrelude$_mls_L0_677_931$(pc1, next1) { return new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_677_931$.class(pc1, next1); };
    Cont$func$benchmark$BenchmarkPrelude$_mls_L0_677_931$1.class = class Cont$func$benchmark$BenchmarkPrelude$_mls_L0_677_931$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp4;
        tmp4 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 9) {
          stackDelayRes = value$;
        } else if (this.pc === 10) {
          tmp = value$;
        } else if (this.pc === 11) {
          tmp1 = value$;
        } else if (this.pc === 13) {
          tmp2 = value$;
        } else if (this.pc === 16) {
          tmp3 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 9) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = BenchmarkPrelude.print("benchmarking...");
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 10;
              return tmp
            }
            this.pc = 10;
            continue contLoop;
          } else if (this.pc === 10) {
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = new b.Suite();
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 11;
              return tmp1
            }
            this.pc = 11;
            continue contLoop;
          } else if (this.pc === 11) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            suite = tmp1;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = suite.add("main", () => {
              let stackDelayRes1, Cont$lambda$1;
              Cont$lambda$1 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$1.class = class Cont$lambda$2 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp4;
                  tmp4 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 12) {
                    stackDelayRes1 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 12) {
                      runtime.stackDepth = runtime.stackDepth + 1;
                      this.completed = true;
                      return BenchmarkPrelude.helper(fn)
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$1.class(12, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              runtime.stackDepth = runtime.stackDepth + 1;
              return BenchmarkPrelude.helper(fn)
            });
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 13;
              return tmp2
            }
            this.pc = 13;
            continue contLoop;
          } else if (this.pc === 13) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            settings = runtime.Unit;
            settings.async = false;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = suite.on("cycle", (event) => {
              let tmp4, curDepth1, stackDelayRes1, Cont$lambda$1;
              Cont$lambda$1 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$1.class = class Cont$lambda$ extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp5;
                  tmp5 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 14) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 15) {
                    tmp4 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 14) {
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp4 = globalThis.String(event.target);
                      if (tmp4 instanceof runtime.EffectSig.class) {
                        this.pc = 15;
                        return tmp4
                      }
                      this.pc = 15;
                      continue contLoop1;
                    } else if (this.pc === 15) {
                      tmp4 = runtime.resetDepth(tmp4, curDepth1);
                      runtime.stackDepth = runtime.stackDepth + 1;
                      this.completed = true;
                      return BenchmarkPrelude.print(tmp4)
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              curDepth1 = runtime.stackDepth;
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$1.class(14, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp4 = globalThis.String(event.target);
              if (tmp4 instanceof runtime.EffectSig.class) {
                tmp4.tail.next = new Cont$lambda$1.class(15, null);
                tmp4.tail = tmp4.tail.next;
                return tmp4
              }
              tmp4 = runtime.resetDepth(tmp4, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              return BenchmarkPrelude.print(tmp4)
            });
            if (tmp3 instanceof runtime.EffectSig.class) {
              this.pc = 16;
              return tmp3
            }
            this.pc = 16;
            continue contLoop;
          } else if (this.pc === 16) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return runtime.safeCall(tmp3.run(settings))
          }
          break;
        }
      }
      toString() { return "Cont$func$benchmark$BenchmarkPrelude$_mls_L0_677_931$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_677_931$1.class(9, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = BenchmarkPrelude.print("benchmarking...");
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.tail.next = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_677_931$1.class(10, null);
      tmp.tail = tmp.tail.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = new b.Suite();
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.tail.next = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_677_931$1.class(11, null);
      tmp1.tail = tmp1.tail.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    suite = tmp1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = suite.add("main", () => {
      let stackDelayRes1, Cont$lambda$1;
      Cont$lambda$1 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
      Cont$lambda$1.class = class Cont$lambda$2 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp4;
          tmp4 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 12) {
            stackDelayRes1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 12) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return BenchmarkPrelude.helper(fn)
            }
            break;
          }
        }
        toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$lambda$1.class(12, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return BenchmarkPrelude.helper(fn)
    });
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.tail.next = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_677_931$1.class(13, null);
      tmp2.tail = tmp2.tail.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    settings = runtime.Unit;
    settings.async = false;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp3 = suite.on("cycle", (event) => {
      let tmp4, curDepth1, stackDelayRes1, Cont$lambda$1;
      Cont$lambda$1 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
      Cont$lambda$1.class = class Cont$lambda$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp5;
          tmp5 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 14) {
            stackDelayRes1 = value$;
          } else if (this.pc === 15) {
            tmp4 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 14) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp4 = globalThis.String(event.target);
              if (tmp4 instanceof runtime.EffectSig.class) {
                this.pc = 15;
                return tmp4
              }
              this.pc = 15;
              continue contLoop;
            } else if (this.pc === 15) {
              tmp4 = runtime.resetDepth(tmp4, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return BenchmarkPrelude.print(tmp4)
            }
            break;
          }
        }
        toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth1 = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$lambda$1.class(14, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = globalThis.String(event.target);
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.tail.next = new Cont$lambda$1.class(15, null);
        tmp4.tail = tmp4.tail.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth1);
      runtime.stackDepth = runtime.stackDepth + 1;
      return BenchmarkPrelude.print(tmp4)
    });
    if (tmp3 instanceof runtime.EffectSig.class) {
      tmp3.tail.next = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_677_931$1.class(16, null);
      tmp3.tail = tmp3.tail.next;
      return tmp3
    }
    tmp3 = runtime.resetDepth(tmp3, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(tmp3.run(settings))
  }
  static toString() { return "BenchmarkPrelude"; }
};
let BenchmarkPrelude = BenchmarkPrelude1; export default BenchmarkPrelude;
