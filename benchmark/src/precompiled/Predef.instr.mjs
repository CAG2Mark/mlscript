import runtime from "./Runtime.mjs";
let Predef1;
Predef1 = class Predef {
  static {
    this.assert = globalThis.console.assert;
    this.foldl = Predef.fold;
    this.MatchResult = function MatchResult(captures1) { return new MatchResult.class(captures1); };
    this.MatchResult.class = class MatchResult {
      constructor(captures) {
        this.captures = captures;
      }
      toString() { return "MatchResult(" + globalThis.Predef.render(this.captures) + ")"; }
    };
    this.MatchFailure = function MatchFailure(errors1) { return new MatchFailure.class(errors1); };
    this.MatchFailure.class = class MatchFailure {
      constructor(errors) {
        this.errors = errors;
      }
      toString() { return "MatchFailure(" + globalThis.Predef.render(this.errors) + ")"; }
    };
    this.TraceLogger = class TraceLogger {
      static {
        this.enabled = false;
        this.indentLvl = 0;
      }
      static indent() {
        let scrut, prev, tmp;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          prev = TraceLogger.indentLvl;
          tmp = prev + 1;
          TraceLogger.indentLvl = tmp;
          return prev
        } else {
          return runtime.Unit
        }
      } 
      static resetIndent(n) {
        let scrut;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          TraceLogger.indentLvl = n;
          return runtime.Unit
        } else {
          return runtime.Unit
        }
      } 
      static log(msg) {
        let scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, stackDelayRes, Cont$func$log$Predef$_mls_L0_3816_3954$1;
        Cont$func$log$Predef$_mls_L0_3816_3954$1 = function Cont$func$log$Predef$_mls_L0_3816_3954$(pc1, next1) { return new Cont$func$log$Predef$_mls_L0_3816_3954$.class(pc1, next1); };
        Cont$func$log$Predef$_mls_L0_3816_3954$1.class = class Cont$func$log$Predef$_mls_L0_3816_3954$ extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp5;
            tmp5 = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 78) {
              stackDelayRes = value$;
            } else if (this.pc === 79) {
              tmp = value$;
            } else if (this.pc === 80) {
              tmp1 = value$;
            } else if (this.pc === 81) {
              tmp3 = value$;
            }
            contLoop: while (true) {
              if (this.pc === 78) {
                scrut = TraceLogger.enabled;
                if (scrut === true) {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp = runtime.safeCall("| ".repeat(TraceLogger.indentLvl));
                  if (tmp instanceof runtime.EffectSig.class) {
                    this.pc = 79;
                    return tmp
                  }
                  this.pc = 79;
                  continue contLoop;
                } else {
                  this.completed = true;
                  return runtime.Unit
                }
                this.pc = 82;
                continue contLoop;
              } else if (this.pc === 82) {
                break contLoop;
              } else if (this.pc === 79) {
                tmp = runtime.resetDepth(tmp, curDepth);
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp1 = runtime.safeCall("  ".repeat(TraceLogger.indentLvl));
                if (tmp1 instanceof runtime.EffectSig.class) {
                  this.pc = 80;
                  return tmp1
                }
                this.pc = 80;
                continue contLoop;
              } else if (this.pc === 80) {
                tmp1 = runtime.resetDepth(tmp1, curDepth);
                tmp2 = "\n" + tmp1;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp3 = msg.replaceAll("\n", tmp2);
                if (tmp3 instanceof runtime.EffectSig.class) {
                  this.pc = 81;
                  return tmp3
                }
                this.pc = 81;
                continue contLoop;
              } else if (this.pc === 81) {
                tmp3 = runtime.resetDepth(tmp3, curDepth);
                tmp4 = tmp + tmp3;
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return runtime.safeCall(globalThis.console.log(tmp4))
              }
              break;
            }
          }
          toString() { return "Cont$func$log$Predef$_mls_L0_3816_3954$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        curDepth = runtime.stackDepth;
        stackDelayRes = runtime.checkDepth();
        if (stackDelayRes instanceof runtime.EffectSig.class) {
          stackDelayRes.tail.next = new Cont$func$log$Predef$_mls_L0_3816_3954$1.class(78, null);
          stackDelayRes.tail = stackDelayRes.tail.next;
          return stackDelayRes
        }
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp = runtime.safeCall("| ".repeat(TraceLogger.indentLvl));
          if (tmp instanceof runtime.EffectSig.class) {
            tmp.tail.next = new Cont$func$log$Predef$_mls_L0_3816_3954$1.class(79, null);
            tmp.tail = tmp.tail.next;
            return tmp
          }
          tmp = runtime.resetDepth(tmp, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp1 = runtime.safeCall("  ".repeat(TraceLogger.indentLvl));
          if (tmp1 instanceof runtime.EffectSig.class) {
            tmp1.tail.next = new Cont$func$log$Predef$_mls_L0_3816_3954$1.class(80, null);
            tmp1.tail = tmp1.tail.next;
            return tmp1
          }
          tmp1 = runtime.resetDepth(tmp1, curDepth);
          tmp2 = "\n" + tmp1;
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp3 = msg.replaceAll("\n", tmp2);
          if (tmp3 instanceof runtime.EffectSig.class) {
            tmp3.tail.next = new Cont$func$log$Predef$_mls_L0_3816_3954$1.class(81, null);
            tmp3.tail = tmp3.tail.next;
            return tmp3
          }
          tmp3 = runtime.resetDepth(tmp3, curDepth);
          tmp4 = tmp + tmp3;
          runtime.stackDepth = runtime.stackDepth + 1;
          return runtime.safeCall(globalThis.console.log(tmp4))
        } else {
          return runtime.Unit
        }
      }
      static toString() { return "TraceLogger"; }
    };
    this.Test = class Test {
      constructor() {
        let tmp, curDepth, stackDelayRes, Cont$ctor$Test$Predef$_mls_L0_3963_4000$1;
        const this$Test = this;
        Cont$ctor$Test$Predef$_mls_L0_3963_4000$1 = function Cont$ctor$Test$Predef$_mls_L0_3963_4000$(pc1, next1) { return new Cont$ctor$Test$Predef$_mls_L0_3963_4000$.class(pc1, next1); };
        Cont$ctor$Test$Predef$_mls_L0_3963_4000$1.class = class Cont$ctor$Test$Predef$_mls_L0_3963_4000$ extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp1;
            tmp1 = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 83) {
              stackDelayRes = value$;
            } else if (this.pc === 84) {
              tmp = value$;
            }
            contLoop: while (true) {
              if (this.pc === 85) {
                this.completed = true;
                return this$Test
              } else if (this.pc === 83) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp = Predef.print("Test");
                if (tmp instanceof runtime.EffectSig.class) {
                  this.pc = 84;
                  return tmp
                }
                this.pc = 84;
                continue contLoop;
              } else if (this.pc === 84) {
                tmp = runtime.resetDepth(tmp, curDepth);
                this$Test.y = 1;
                this.pc = 85;
                continue contLoop;
              }
              break;
            }
          }
          toString() { return "Cont$ctor$Test$Predef$_mls_L0_3963_4000$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        curDepth = runtime.stackDepth;
        stackDelayRes = runtime.checkDepth();
        if (stackDelayRes instanceof runtime.EffectSig.class) {
          stackDelayRes.tail.next = new Cont$ctor$Test$Predef$_mls_L0_3963_4000$1.class(83, null);
          stackDelayRes.tail = stackDelayRes.tail.next;
          return stackDelayRes
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp = Predef.print("Test");
        if (tmp instanceof runtime.EffectSig.class) {
          tmp.tail.next = new Cont$ctor$Test$Predef$_mls_L0_3963_4000$1.class(84, null);
          tmp.tail = tmp.tail.next;
          return tmp
        }
        tmp = runtime.resetDepth(tmp, curDepth);
        this.y = 1;
      }
      toString() { return "Test"; }
    };
  }
  static id(x) {
    return x
  } 
  static not(x1) {
    if (x1 === false) {
      return true
    } else {
      return false
    }
  } 
  static pipeInto(x2, f) {
    let stackDelayRes, Cont$func$pipeInto$Predef$_mls_L0_70_96$1;
    Cont$func$pipeInto$Predef$_mls_L0_70_96$1 = function Cont$func$pipeInto$Predef$_mls_L0_70_96$(pc1, next1) { return new Cont$func$pipeInto$Predef$_mls_L0_70_96$.class(pc1, next1); };
    Cont$func$pipeInto$Predef$_mls_L0_70_96$1.class = class Cont$func$pipeInto$Predef$_mls_L0_70_96$ extends runtime.Cont.class {
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
            return runtime.safeCall(f(x2))
          }
          break;
        }
      }
      toString() { return "Cont$func$pipeInto$Predef$_mls_L0_70_96$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$pipeInto$Predef$_mls_L0_70_96$1.class(0, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(f(x2))
  } 
  static pipeFrom(f1, x3) {
    let stackDelayRes, Cont$func$pipeFrom$Predef$_mls_L0_101_127$1;
    Cont$func$pipeFrom$Predef$_mls_L0_101_127$1 = function Cont$func$pipeFrom$Predef$_mls_L0_101_127$(pc1, next1) { return new Cont$func$pipeFrom$Predef$_mls_L0_101_127$.class(pc1, next1); };
    Cont$func$pipeFrom$Predef$_mls_L0_101_127$1.class = class Cont$func$pipeFrom$Predef$_mls_L0_101_127$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp;
        tmp = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 1) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 1) {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return runtime.safeCall(f1(x3))
          }
          break;
        }
      }
      toString() { return "Cont$func$pipeFrom$Predef$_mls_L0_101_127$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$pipeFrom$Predef$_mls_L0_101_127$1.class(1, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(f1(x3))
  } 
  static andThen(f2, g) {
    return (x4) => {
      let tmp, curDepth, stackDelayRes, Cont$func$andThen$Predef$_mls_L0_133_164$1;
      Cont$func$andThen$Predef$_mls_L0_133_164$1 = function Cont$func$andThen$Predef$_mls_L0_133_164$(pc1, next1) { return new Cont$func$andThen$Predef$_mls_L0_133_164$.class(pc1, next1); };
      Cont$func$andThen$Predef$_mls_L0_133_164$1.class = class Cont$func$andThen$Predef$_mls_L0_133_164$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp1;
          tmp1 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 2) {
            stackDelayRes = value$;
          } else if (this.pc === 3) {
            tmp = value$;
          }
          contLoop: while (true) {
            if (this.pc === 2) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = runtime.safeCall(f2(x4));
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 3;
                return tmp
              }
              this.pc = 3;
              continue contLoop;
            } else if (this.pc === 3) {
              tmp = runtime.resetDepth(tmp, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return runtime.safeCall(g(tmp))
            }
            break;
          }
        }
        toString() { return "Cont$func$andThen$Predef$_mls_L0_133_164$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.tail.next = new Cont$func$andThen$Predef$_mls_L0_133_164$1.class(2, null);
        stackDelayRes.tail = stackDelayRes.tail.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = runtime.safeCall(f2(x4));
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.tail.next = new Cont$func$andThen$Predef$_mls_L0_133_164$1.class(3, null);
        tmp.tail = tmp.tail.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(g(tmp))
    }
  } 
  static compose(f3, g1) {
    return (x4) => {
      let tmp, curDepth, stackDelayRes, Cont$func$compose$Predef$_mls_L0_169_200$1;
      Cont$func$compose$Predef$_mls_L0_169_200$1 = function Cont$func$compose$Predef$_mls_L0_169_200$(pc1, next1) { return new Cont$func$compose$Predef$_mls_L0_169_200$.class(pc1, next1); };
      Cont$func$compose$Predef$_mls_L0_169_200$1.class = class Cont$func$compose$Predef$_mls_L0_169_200$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp1;
          tmp1 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 4) {
            stackDelayRes = value$;
          } else if (this.pc === 5) {
            tmp = value$;
          }
          contLoop: while (true) {
            if (this.pc === 4) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = runtime.safeCall(g1(x4));
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 5;
                return tmp
              }
              this.pc = 5;
              continue contLoop;
            } else if (this.pc === 5) {
              tmp = runtime.resetDepth(tmp, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return runtime.safeCall(f3(tmp))
            }
            break;
          }
        }
        toString() { return "Cont$func$compose$Predef$_mls_L0_169_200$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.tail.next = new Cont$func$compose$Predef$_mls_L0_169_200$1.class(4, null);
        stackDelayRes.tail = stackDelayRes.tail.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = runtime.safeCall(g1(x4));
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.tail.next = new Cont$func$compose$Predef$_mls_L0_169_200$1.class(5, null);
        tmp.tail = tmp.tail.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f3(tmp))
    }
  } 
  static passTo(receiver, f4) {
    return (...args) => {
      let stackDelayRes, Cont$func$passTo$Predef$_mls_L0_206_261$1;
      Cont$func$passTo$Predef$_mls_L0_206_261$1 = function Cont$func$passTo$Predef$_mls_L0_206_261$(pc1, next1) { return new Cont$func$passTo$Predef$_mls_L0_206_261$.class(pc1, next1); };
      Cont$func$passTo$Predef$_mls_L0_206_261$1.class = class Cont$func$passTo$Predef$_mls_L0_206_261$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp;
          tmp = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 6) {
            stackDelayRes = value$;
          }
          contLoop: while (true) {
            if (this.pc === 6) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return runtime.safeCall(f4(receiver, ...args))
            }
            break;
          }
        }
        toString() { return "Cont$func$passTo$Predef$_mls_L0_206_261$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.tail.next = new Cont$func$passTo$Predef$_mls_L0_206_261$1.class(6, null);
        stackDelayRes.tail = stackDelayRes.tail.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f4(receiver, ...args))
    }
  } 
  static call(receiver1, f5) {
    return (...args) => {
      let stackDelayRes, Cont$func$call$Predef$_mls_L0_267_327$1;
      Cont$func$call$Predef$_mls_L0_267_327$1 = function Cont$func$call$Predef$_mls_L0_267_327$(pc1, next1) { return new Cont$func$call$Predef$_mls_L0_267_327$.class(pc1, next1); };
      Cont$func$call$Predef$_mls_L0_267_327$1.class = class Cont$func$call$Predef$_mls_L0_267_327$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp;
          tmp = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 7) {
            stackDelayRes = value$;
          }
          contLoop: while (true) {
            if (this.pc === 7) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return f5.call(receiver1, ...args)
            }
            break;
          }
        }
        toString() { return "Cont$func$call$Predef$_mls_L0_267_327$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.tail.next = new Cont$func$call$Predef$_mls_L0_267_327$1.class(7, null);
        stackDelayRes.tail = stackDelayRes.tail.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return f5.call(receiver1, ...args)
    }
  } 
  static pass1(f6) {
    return (...xs) => {
      let stackDelayRes, Cont$func$pass1$Predef$_mls_L0_333_358$1;
      Cont$func$pass1$Predef$_mls_L0_333_358$1 = function Cont$func$pass1$Predef$_mls_L0_333_358$(pc1, next1) { return new Cont$func$pass1$Predef$_mls_L0_333_358$.class(pc1, next1); };
      Cont$func$pass1$Predef$_mls_L0_333_358$1.class = class Cont$func$pass1$Predef$_mls_L0_333_358$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp;
          tmp = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 8) {
            stackDelayRes = value$;
          }
          contLoop: while (true) {
            if (this.pc === 8) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return runtime.safeCall(f6(xs[0]))
            }
            break;
          }
        }
        toString() { return "Cont$func$pass1$Predef$_mls_L0_333_358$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.tail.next = new Cont$func$pass1$Predef$_mls_L0_333_358$1.class(8, null);
        stackDelayRes.tail = stackDelayRes.tail.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f6(xs[0]))
    }
  } 
  static pass2(f7) {
    return (...xs) => {
      let stackDelayRes, Cont$func$pass2$Predef$_mls_L0_363_394$1;
      Cont$func$pass2$Predef$_mls_L0_363_394$1 = function Cont$func$pass2$Predef$_mls_L0_363_394$(pc1, next1) { return new Cont$func$pass2$Predef$_mls_L0_363_394$.class(pc1, next1); };
      Cont$func$pass2$Predef$_mls_L0_363_394$1.class = class Cont$func$pass2$Predef$_mls_L0_363_394$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp;
          tmp = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 9) {
            stackDelayRes = value$;
          }
          contLoop: while (true) {
            if (this.pc === 9) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return runtime.safeCall(f7(xs[0], xs[1]))
            }
            break;
          }
        }
        toString() { return "Cont$func$pass2$Predef$_mls_L0_363_394$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.tail.next = new Cont$func$pass2$Predef$_mls_L0_363_394$1.class(9, null);
        stackDelayRes.tail = stackDelayRes.tail.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f7(xs[0], xs[1]))
    }
  } 
  static pass3(f8) {
    return (...xs) => {
      let stackDelayRes, Cont$func$pass3$Predef$_mls_L0_399_436$1;
      Cont$func$pass3$Predef$_mls_L0_399_436$1 = function Cont$func$pass3$Predef$_mls_L0_399_436$(pc1, next1) { return new Cont$func$pass3$Predef$_mls_L0_399_436$.class(pc1, next1); };
      Cont$func$pass3$Predef$_mls_L0_399_436$1.class = class Cont$func$pass3$Predef$_mls_L0_399_436$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp;
          tmp = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 10) {
            stackDelayRes = value$;
          }
          contLoop: while (true) {
            if (this.pc === 10) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return runtime.safeCall(f8(xs[0], xs[1], xs[2]))
            }
            break;
          }
        }
        toString() { return "Cont$func$pass3$Predef$_mls_L0_399_436$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.tail.next = new Cont$func$pass3$Predef$_mls_L0_399_436$1.class(10, null);
        stackDelayRes.tail = stackDelayRes.tail.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f8(xs[0], xs[1], xs[2]))
    }
  } 
  static print(...xs) {
    let tmp, tmp1, curDepth, stackDelayRes, Cont$func$print$Predef$_mls_L0_443_499$1;
    Cont$func$print$Predef$_mls_L0_443_499$1 = function Cont$func$print$Predef$_mls_L0_443_499$(pc1, next1) { return new Cont$func$print$Predef$_mls_L0_443_499$.class(pc1, next1); };
    Cont$func$print$Predef$_mls_L0_443_499$1.class = class Cont$func$print$Predef$_mls_L0_443_499$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp2;
        tmp2 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 11) {
          stackDelayRes = value$;
        } else if (this.pc === 12) {
          tmp = value$;
        } else if (this.pc === 13) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 11) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = Predef.map(Predef.renderAsStr);
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 12;
              return tmp
            }
            this.pc = 12;
            continue contLoop;
          } else if (this.pc === 12) {
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = runtime.safeCall(tmp(...xs));
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 13;
              return tmp1
            }
            this.pc = 13;
            continue contLoop;
          } else if (this.pc === 13) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return runtime.safeCall(globalThis.console.log(...tmp1))
          }
          break;
        }
      }
      toString() { return "Cont$func$print$Predef$_mls_L0_443_499$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$print$Predef$_mls_L0_443_499$1.class(11, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = Predef.map(Predef.renderAsStr);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.tail.next = new Cont$func$print$Predef$_mls_L0_443_499$1.class(12, null);
      tmp.tail = tmp.tail.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = runtime.safeCall(tmp(...xs));
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.tail.next = new Cont$func$print$Predef$_mls_L0_443_499$1.class(13, null);
      tmp1.tail = tmp1.tail.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(globalThis.console.log(...tmp1))
  } 
  static printRaw(x4) {
    let tmp, curDepth, stackDelayRes, Cont$func$printRaw$Predef$_mls_L0_505_543$1;
    Cont$func$printRaw$Predef$_mls_L0_505_543$1 = function Cont$func$printRaw$Predef$_mls_L0_505_543$(pc1, next1) { return new Cont$func$printRaw$Predef$_mls_L0_505_543$.class(pc1, next1); };
    Cont$func$printRaw$Predef$_mls_L0_505_543$1.class = class Cont$func$printRaw$Predef$_mls_L0_505_543$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp1;
        tmp1 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 14) {
          stackDelayRes = value$;
        } else if (this.pc === 15) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 14) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = Predef.render(x4);
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 15;
              return tmp
            }
            this.pc = 15;
            continue contLoop;
          } else if (this.pc === 15) {
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return runtime.safeCall(globalThis.console.log(tmp))
          }
          break;
        }
      }
      toString() { return "Cont$func$printRaw$Predef$_mls_L0_505_543$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$printRaw$Predef$_mls_L0_505_543$1.class(14, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = Predef.render(x4);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.tail.next = new Cont$func$printRaw$Predef$_mls_L0_505_543$1.class(15, null);
      tmp.tail = tmp.tail.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(globalThis.console.log(tmp))
  } 
  static interleave(sep) {
    return (...args) => {
      let res, len, i, scrut, idx, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, Cont$func$interleave$Predef$_mls_L0_549_826$1;
      Cont$func$interleave$Predef$_mls_L0_549_826$1 = function Cont$func$interleave$Predef$_mls_L0_549_826$(pc1, next1) { return new Cont$func$interleave$Predef$_mls_L0_549_826$.class(pc1, next1); };
      Cont$func$interleave$Predef$_mls_L0_549_826$1.class = class Cont$func$interleave$Predef$_mls_L0_549_826$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp8;
          tmp8 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 16) {
            stackDelayRes = value$;
          } else if (this.pc === 17) {
            tmp2 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 16) {
              scrut2 = args.length === 0;
              if (scrut2 === true) {
                this.completed = true;
                return []
              } else {
                tmp = args.length * 2;
                tmp1 = tmp - 1;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp2 = globalThis.Array(tmp1);
                if (tmp2 instanceof runtime.EffectSig.class) {
                  this.pc = 17;
                  return tmp2
                }
                this.pc = 17;
                continue contLoop;
              }
              this.pc = 18;
              continue contLoop;
            } else if (this.pc === 18) {
              break contLoop;
            } else if (this.pc === 17) {
              tmp2 = runtime.resetDepth(tmp2, curDepth);
              res = tmp2;
              len = args.length;
              i = 0;
              this.pc = 20;
              continue contLoop;
            } else if (this.pc === 19) {
              this.completed = true;
              return res
            } else if (this.pc === 20) {
              scrut = i < len;
              if (scrut === true) {
                tmp3 = i * 2;
                idx = tmp3;
                res[idx] = args[i];
                tmp4 = i + 1;
                i = tmp4;
                scrut1 = i < len;
                if (scrut1 === true) {
                  tmp5 = idx + 1;
                  res[tmp5] = sep;
                  tmp6 = runtime.Unit;
                  this.pc = 21;
                  continue contLoop;
                } else {
                  tmp6 = runtime.Unit;
                  this.pc = 21;
                  continue contLoop;
                }
                this.pc = 21;
                continue contLoop;
              } else {
                tmp7 = runtime.Unit;
                this.pc = 19;
                continue contLoop;
              }
              this.pc = 19;
              continue contLoop;
            } else if (this.pc === 21) {
              tmp7 = tmp6;
              this.pc = 20;
              continue contLoop;
            }
            break;
          }
        }
        toString() { return "Cont$func$interleave$Predef$_mls_L0_549_826$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.tail.next = new Cont$func$interleave$Predef$_mls_L0_549_826$1.class(16, null);
        stackDelayRes.tail = stackDelayRes.tail.next;
        return stackDelayRes
      }
      scrut2 = args.length === 0;
      if (scrut2 === true) {
        return []
      } else {
        tmp = args.length * 2;
        tmp1 = tmp - 1;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp2 = globalThis.Array(tmp1);
        if (tmp2 instanceof runtime.EffectSig.class) {
          tmp2.tail.next = new Cont$func$interleave$Predef$_mls_L0_549_826$1.class(17, null);
          tmp2.tail = tmp2.tail.next;
          return tmp2
        }
        tmp2 = runtime.resetDepth(tmp2, curDepth);
        res = tmp2;
        len = args.length;
        i = 0;
        tmp8: while (true) {
          scrut = i < len;
          if (scrut === true) {
            tmp3 = i * 2;
            idx = tmp3;
            res[idx] = args[i];
            tmp4 = i + 1;
            i = tmp4;
            scrut1 = i < len;
            if (scrut1 === true) {
              tmp5 = idx + 1;
              res[tmp5] = sep;
              tmp6 = runtime.Unit;
            } else {
              tmp6 = runtime.Unit;
            }
            tmp7 = tmp6;
            continue tmp8;
          } else {
            tmp7 = runtime.Unit;
          }
          break;
        }
        return res
      }
    }
  } 
  static renderAsStr(arg) {
    let stackDelayRes, Cont$func$renderAsStr$Predef$_mls_L0_832_892$1;
    Cont$func$renderAsStr$Predef$_mls_L0_832_892$1 = function Cont$func$renderAsStr$Predef$_mls_L0_832_892$(pc1, next1) { return new Cont$func$renderAsStr$Predef$_mls_L0_832_892$.class(pc1, next1); };
    Cont$func$renderAsStr$Predef$_mls_L0_832_892$1.class = class Cont$func$renderAsStr$Predef$_mls_L0_832_892$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp;
        tmp = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 22) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 22) {
            if (typeof arg === 'string') {
              this.completed = true;
              return arg
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return Predef.render(arg)
            }
            this.pc = 23;
            continue contLoop;
          } else if (this.pc === 23) {
            break contLoop;
          }
          break;
        }
      }
      toString() { return "Cont$func$renderAsStr$Predef$_mls_L0_832_892$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$renderAsStr$Predef$_mls_L0_832_892$1.class(22, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (typeof arg === 'string') {
      return arg
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      return Predef.render(arg)
    }
  } 
  static render(arg1) {
    let ts, p, scrut, scrut1, scrut2, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, Cont$func$render$Predef$_mls_L0_898_1708$1;
    Cont$func$render$Predef$_mls_L0_898_1708$1 = function Cont$func$render$Predef$_mls_L0_898_1708$(pc1, next1) { return new Cont$func$render$Predef$_mls_L0_898_1708$.class(pc1, next1); };
    Cont$func$render$Predef$_mls_L0_898_1708$1.class = class Cont$func$render$Predef$_mls_L0_898_1708$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp21;
        tmp21 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 24) {
          stackDelayRes = value$;
        } else if (this.pc === 40) {
          p = value$;
        } else if (this.pc === 35) {
          tmp10 = value$;
        } else if (this.pc === 36) {
          tmp11 = value$;
        } else if (this.pc === 37) {
          tmp12 = value$;
        } else if (this.pc === 38) {
          tmp13 = value$;
        } else if (this.pc === 39) {
          tmp14 = value$;
        } else if (this.pc === 30) {
          tmp5 = value$;
        } else if (this.pc === 31) {
          tmp6 = value$;
        } else if (this.pc === 32) {
          tmp7 = value$;
        } else if (this.pc === 33) {
          tmp8 = value$;
        } else if (this.pc === 34) {
          tmp9 = value$;
        } else if (this.pc === 25) {
          tmp = value$;
        } else if (this.pc === 26) {
          tmp1 = value$;
        } else if (this.pc === 27) {
          tmp2 = value$;
        } else if (this.pc === 28) {
          tmp3 = value$;
        } else if (this.pc === 29) {
          tmp4 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 24) {
            if (arg1 === undefined) {
              this.completed = true;
              return "undefined"
            } else if (arg1 === null) {
              this.completed = true;
              return "null";
              this.pc = 41;
              continue contLoop;
            } else if (arg1 instanceof globalThis.Array) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = Predef.fold((arg11, arg2) => {
                return arg11 + arg2
              });
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 25;
                return tmp
              }
              this.pc = 25;
              continue contLoop;
              this.pc = 41;
              continue contLoop;
              this.pc = 41;
              continue contLoop;
            } else {
              if (typeof arg1 === 'string') {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return runtime.safeCall(globalThis.JSON.stringify(arg1))
              } else if (arg1 instanceof globalThis.Set) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp5 = Predef.fold((arg11, arg2) => {
                  return arg11 + arg2
                });
                if (tmp5 instanceof runtime.EffectSig.class) {
                  this.pc = 30;
                  return tmp5
                }
                this.pc = 30;
                continue contLoop;
                this.pc = 41;
                continue contLoop;
              } else if (arg1 instanceof globalThis.Map) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp10 = Predef.fold((arg11, arg2) => {
                  return arg11 + arg2
                });
                if (tmp10 instanceof runtime.EffectSig.class) {
                  this.pc = 35;
                  return tmp10
                }
                this.pc = 35;
                continue contLoop;
                this.pc = 41;
                continue contLoop;
                this.pc = 41;
                continue contLoop;
              } else if (arg1 instanceof globalThis.Function) {
                runtime.stackDepth = runtime.stackDepth + 1;
                p = globalThis.Object.getOwnPropertyDescriptor(arg1, "prototype");
                if (p instanceof runtime.EffectSig.class) {
                  this.pc = 40;
                  return p
                }
                this.pc = 40;
                continue contLoop;
                this.pc = 41;
                continue contLoop;
                this.pc = 41;
                continue contLoop;
                this.pc = 41;
                continue contLoop;
              } else if (arg1 instanceof globalThis.Object) {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return globalThis.String(arg1);
                this.pc = 41;
                continue contLoop;
                this.pc = 41;
                continue contLoop;
                this.pc = 41;
                continue contLoop;
                this.pc = 41;
                continue contLoop;
              } else {
                ts = arg1["toString"];
                if (ts === undefined) {
                  tmp19 = typeof arg1;
                  tmp20 = "[" + tmp19;
                  this.completed = true;
                  return tmp20 + "]"
                } else {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  this.completed = true;
                  return runtime.safeCall(ts.call(arg1))
                }
                this.pc = 41;
                continue contLoop;
              }
              this.pc = 41;
              continue contLoop;
            }
            this.pc = 41;
            continue contLoop;
          } else if (this.pc === 41) {
            break contLoop;
          } else if (this.pc === 40) {
            p = runtime.resetDepth(p, curDepth);
            if (p instanceof globalThis.Object) {
              scrut = p["writable"];
              if (scrut === true) {
                tmp15 = true;
                this.pc = 44;
                continue contLoop;
              } else {
                tmp15 = false;
                this.pc = 44;
                continue contLoop;
              }
              this.pc = 44;
              continue contLoop;
            } else {
              tmp15 = false;
              this.pc = 44;
              continue contLoop;
            }
            this.pc = 44;
            continue contLoop;
          } else if (this.pc === 44) {
            if (p === undefined) {
              tmp16 = true;
              this.pc = 43;
              continue contLoop;
            } else {
              tmp16 = false;
              this.pc = 43;
              continue contLoop;
            }
            this.pc = 43;
            continue contLoop;
          } else if (this.pc === 43) {
            scrut1 = tmp15 || tmp16;
            if (scrut1 === true) {
              scrut2 = arg1.name;
              if (scrut2 === "") {
                tmp17 = "";
                this.pc = 42;
                continue contLoop;
              } else {
                nme = scrut2;
                tmp17 = " " + nme;
                this.pc = 42;
                continue contLoop;
              }
              this.pc = 42;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return globalThis.String(arg1)
            }
            this.pc = 41;
            continue contLoop;
          } else if (this.pc === 42) {
            tmp18 = "[function" + tmp17;
            this.completed = true;
            return tmp18 + "]"
          } else if (this.pc === 35) {
            tmp10 = runtime.resetDepth(tmp10, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp11 = Predef.interleave(", ");
            if (tmp11 instanceof runtime.EffectSig.class) {
              this.pc = 36;
              return tmp11
            }
            this.pc = 36;
            continue contLoop;
          } else if (this.pc === 36) {
            tmp11 = runtime.resetDepth(tmp11, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp12 = Predef.map(Predef.render);
            if (tmp12 instanceof runtime.EffectSig.class) {
              this.pc = 37;
              return tmp12
            }
            this.pc = 37;
            continue contLoop;
          } else if (this.pc === 37) {
            tmp12 = runtime.resetDepth(tmp12, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp13 = runtime.safeCall(tmp12(...arg1));
            if (tmp13 instanceof runtime.EffectSig.class) {
              this.pc = 38;
              return tmp13
            }
            this.pc = 38;
            continue contLoop;
          } else if (this.pc === 38) {
            tmp13 = runtime.resetDepth(tmp13, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp14 = runtime.safeCall(tmp11(...tmp13));
            if (tmp14 instanceof runtime.EffectSig.class) {
              this.pc = 39;
              return tmp14
            }
            this.pc = 39;
            continue contLoop;
          } else if (this.pc === 39) {
            tmp14 = runtime.resetDepth(tmp14, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return runtime.safeCall(tmp10("Map{", ...tmp14, "}"))
          } else if (this.pc === 30) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp6 = Predef.interleave(", ");
            if (tmp6 instanceof runtime.EffectSig.class) {
              this.pc = 31;
              return tmp6
            }
            this.pc = 31;
            continue contLoop;
          } else if (this.pc === 31) {
            tmp6 = runtime.resetDepth(tmp6, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp7 = Predef.map(Predef.render);
            if (tmp7 instanceof runtime.EffectSig.class) {
              this.pc = 32;
              return tmp7
            }
            this.pc = 32;
            continue contLoop;
          } else if (this.pc === 32) {
            tmp7 = runtime.resetDepth(tmp7, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp8 = runtime.safeCall(tmp7(...arg1));
            if (tmp8 instanceof runtime.EffectSig.class) {
              this.pc = 33;
              return tmp8
            }
            this.pc = 33;
            continue contLoop;
          } else if (this.pc === 33) {
            tmp8 = runtime.resetDepth(tmp8, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp9 = runtime.safeCall(tmp6(...tmp8));
            if (tmp9 instanceof runtime.EffectSig.class) {
              this.pc = 34;
              return tmp9
            }
            this.pc = 34;
            continue contLoop;
          } else if (this.pc === 34) {
            tmp9 = runtime.resetDepth(tmp9, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return runtime.safeCall(tmp5("Set{", ...tmp9, "}"))
          } else if (this.pc === 25) {
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = Predef.interleave(", ");
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 26;
              return tmp1
            }
            this.pc = 26;
            continue contLoop;
          } else if (this.pc === 26) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = Predef.map(Predef.render);
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 27;
              return tmp2
            }
            this.pc = 27;
            continue contLoop;
          } else if (this.pc === 27) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = runtime.safeCall(tmp2(...arg1));
            if (tmp3 instanceof runtime.EffectSig.class) {
              this.pc = 28;
              return tmp3
            }
            this.pc = 28;
            continue contLoop;
          } else if (this.pc === 28) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = runtime.safeCall(tmp1(...tmp3));
            if (tmp4 instanceof runtime.EffectSig.class) {
              this.pc = 29;
              return tmp4
            }
            this.pc = 29;
            continue contLoop;
          } else if (this.pc === 29) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return runtime.safeCall(tmp("[", ...tmp4, "]"))
          }
          break;
        }
      }
      toString() { return "Cont$func$render$Predef$_mls_L0_898_1708$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(24, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (arg1 === undefined) {
      return "undefined"
    } else if (arg1 === null) {
      return "null"
    } else if (arg1 instanceof globalThis.Array) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = Predef.fold((arg11, arg2) => {
        return arg11 + arg2
      });
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(25, null);
        tmp.tail = tmp.tail.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = Predef.interleave(", ");
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(26, null);
        tmp1.tail = tmp1.tail.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = Predef.map(Predef.render);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(27, null);
        tmp2.tail = tmp2.tail.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = runtime.safeCall(tmp2(...arg1));
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(28, null);
        tmp3.tail = tmp3.tail.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = runtime.safeCall(tmp1(...tmp3));
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(29, null);
        tmp4.tail = tmp4.tail.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(tmp("[", ...tmp4, "]"))
    } else if (typeof arg1 === 'string') {
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(globalThis.JSON.stringify(arg1))
    } else if (arg1 instanceof globalThis.Set) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp5 = Predef.fold((arg11, arg2) => {
        return arg11 + arg2
      });
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(30, null);
        tmp5.tail = tmp5.tail.next;
        return tmp5
      }
      tmp5 = runtime.resetDepth(tmp5, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp6 = Predef.interleave(", ");
      if (tmp6 instanceof runtime.EffectSig.class) {
        tmp6.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(31, null);
        tmp6.tail = tmp6.tail.next;
        return tmp6
      }
      tmp6 = runtime.resetDepth(tmp6, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp7 = Predef.map(Predef.render);
      if (tmp7 instanceof runtime.EffectSig.class) {
        tmp7.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(32, null);
        tmp7.tail = tmp7.tail.next;
        return tmp7
      }
      tmp7 = runtime.resetDepth(tmp7, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp8 = runtime.safeCall(tmp7(...arg1));
      if (tmp8 instanceof runtime.EffectSig.class) {
        tmp8.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(33, null);
        tmp8.tail = tmp8.tail.next;
        return tmp8
      }
      tmp8 = runtime.resetDepth(tmp8, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp9 = runtime.safeCall(tmp6(...tmp8));
      if (tmp9 instanceof runtime.EffectSig.class) {
        tmp9.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(34, null);
        tmp9.tail = tmp9.tail.next;
        return tmp9
      }
      tmp9 = runtime.resetDepth(tmp9, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(tmp5("Set{", ...tmp9, "}"))
    } else if (arg1 instanceof globalThis.Map) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp10 = Predef.fold((arg11, arg2) => {
        return arg11 + arg2
      });
      if (tmp10 instanceof runtime.EffectSig.class) {
        tmp10.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(35, null);
        tmp10.tail = tmp10.tail.next;
        return tmp10
      }
      tmp10 = runtime.resetDepth(tmp10, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp11 = Predef.interleave(", ");
      if (tmp11 instanceof runtime.EffectSig.class) {
        tmp11.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(36, null);
        tmp11.tail = tmp11.tail.next;
        return tmp11
      }
      tmp11 = runtime.resetDepth(tmp11, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp12 = Predef.map(Predef.render);
      if (tmp12 instanceof runtime.EffectSig.class) {
        tmp12.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(37, null);
        tmp12.tail = tmp12.tail.next;
        return tmp12
      }
      tmp12 = runtime.resetDepth(tmp12, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp13 = runtime.safeCall(tmp12(...arg1));
      if (tmp13 instanceof runtime.EffectSig.class) {
        tmp13.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(38, null);
        tmp13.tail = tmp13.tail.next;
        return tmp13
      }
      tmp13 = runtime.resetDepth(tmp13, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp14 = runtime.safeCall(tmp11(...tmp13));
      if (tmp14 instanceof runtime.EffectSig.class) {
        tmp14.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(39, null);
        tmp14.tail = tmp14.tail.next;
        return tmp14
      }
      tmp14 = runtime.resetDepth(tmp14, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(tmp10("Map{", ...tmp14, "}"))
    } else if (arg1 instanceof globalThis.Function) {
      runtime.stackDepth = runtime.stackDepth + 1;
      p = globalThis.Object.getOwnPropertyDescriptor(arg1, "prototype");
      if (p instanceof runtime.EffectSig.class) {
        p.tail.next = new Cont$func$render$Predef$_mls_L0_898_1708$1.class(40, null);
        p.tail = p.tail.next;
        return p
      }
      p = runtime.resetDepth(p, curDepth);
      if (p instanceof globalThis.Object) {
        scrut = p["writable"];
        if (scrut === true) {
          tmp15 = true;
        } else {
          tmp15 = false;
        }
      } else {
        tmp15 = false;
      }
      if (p === undefined) {
        tmp16 = true;
      } else {
        tmp16 = false;
      }
      scrut1 = tmp15 || tmp16;
      if (scrut1 === true) {
        scrut2 = arg1.name;
        if (scrut2 === "") {
          tmp17 = "";
        } else {
          nme = scrut2;
          tmp17 = " " + nme;
        }
        tmp18 = "[function" + tmp17;
        return tmp18 + "]"
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        return globalThis.String(arg1)
      }
    } else if (arg1 instanceof globalThis.Object) {
      runtime.stackDepth = runtime.stackDepth + 1;
      return globalThis.String(arg1)
    } else {
      ts = arg1["toString"];
      if (ts === undefined) {
        tmp19 = typeof arg1;
        tmp20 = "[" + tmp19;
        return tmp20 + "]"
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(ts.call(arg1))
      }
    }
  } 
  static notImplemented(msg) {
    let tmp, tmp1, curDepth, stackDelayRes, Cont$func$notImplemented$Predef$_mls_L0_1743_1808$1;
    Cont$func$notImplemented$Predef$_mls_L0_1743_1808$1 = function Cont$func$notImplemented$Predef$_mls_L0_1743_1808$(pc1, next1) { return new Cont$func$notImplemented$Predef$_mls_L0_1743_1808$.class(pc1, next1); };
    Cont$func$notImplemented$Predef$_mls_L0_1743_1808$1.class = class Cont$func$notImplemented$Predef$_mls_L0_1743_1808$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp2;
        tmp2 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 45) {
          stackDelayRes = value$;
        } else if (this.pc === 46) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 45) {
            tmp = "Not implemented: " + msg;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = globalThis.Error(tmp);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 46;
              return tmp1
            }
            this.pc = 46;
            continue contLoop;
          } else if (this.pc === 46) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            throw tmp1;
          }
          break;
        }
      }
      toString() { return "Cont$func$notImplemented$Predef$_mls_L0_1743_1808$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$notImplemented$Predef$_mls_L0_1743_1808$1.class(45, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    tmp = "Not implemented: " + msg;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = globalThis.Error(tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.tail.next = new Cont$func$notImplemented$Predef$_mls_L0_1743_1808$1.class(46, null);
      tmp1.tail = tmp1.tail.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    throw tmp1;
  } 
  static get notImplementedError() {
    let tmp, curDepth, stackDelayRes, Cont$func$notImplementedError$Predef$_mls_L0_1813_1871$1;
    Cont$func$notImplementedError$Predef$_mls_L0_1813_1871$1 = function Cont$func$notImplementedError$Predef$_mls_L0_1813_1871$(pc1, next1) { return new Cont$func$notImplementedError$Predef$_mls_L0_1813_1871$.class(pc1, next1); };
    Cont$func$notImplementedError$Predef$_mls_L0_1813_1871$1.class = class Cont$func$notImplementedError$Predef$_mls_L0_1813_1871$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp1;
        tmp1 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 47) {
          stackDelayRes = value$;
        } else if (this.pc === 48) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 47) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = globalThis.Error("Not implemented");
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 48;
              return tmp
            }
            this.pc = 48;
            continue contLoop;
          } else if (this.pc === 48) {
            tmp = runtime.resetDepth(tmp, curDepth);
            throw tmp;
          }
          break;
        }
      }
      toString() { return "Cont$func$notImplementedError$Predef$_mls_L0_1813_1871$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$notImplementedError$Predef$_mls_L0_1813_1871$1.class(47, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = globalThis.Error("Not implemented");
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.tail.next = new Cont$func$notImplementedError$Predef$_mls_L0_1813_1871$1.class(48, null);
      tmp.tail = tmp.tail.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    throw tmp;
  } 
  static tuple(...xs1) {
    return xs1
  } 
  static tupleSlice(xs2, i, j) {
    let tmp, stackDelayRes, Cont$func$tupleSlice$Predef$_mls_L0_1901_2103$1;
    Cont$func$tupleSlice$Predef$_mls_L0_1901_2103$1 = function Cont$func$tupleSlice$Predef$_mls_L0_1901_2103$(pc1, next1) { return new Cont$func$tupleSlice$Predef$_mls_L0_1901_2103$.class(pc1, next1); };
    Cont$func$tupleSlice$Predef$_mls_L0_1901_2103$1.class = class Cont$func$tupleSlice$Predef$_mls_L0_1901_2103$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp1;
        tmp1 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 49) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 49) {
            tmp = xs2.length - j;
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return runtime.safeCall(globalThis.Array.prototype.slice.call(xs2, i, tmp))
          }
          break;
        }
      }
      toString() { return "Cont$func$tupleSlice$Predef$_mls_L0_1901_2103$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$tupleSlice$Predef$_mls_L0_1901_2103$1.class(49, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    tmp = xs2.length - j;
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(globalThis.Array.prototype.slice.call(xs2, i, tmp))
  } 
  static tupleGet(xs3, i1) {
    let stackDelayRes, Cont$func$tupleGet$Predef$_mls_L0_2109_2245$1;
    Cont$func$tupleGet$Predef$_mls_L0_2109_2245$1 = function Cont$func$tupleGet$Predef$_mls_L0_2109_2245$(pc1, next1) { return new Cont$func$tupleGet$Predef$_mls_L0_2109_2245$.class(pc1, next1); };
    Cont$func$tupleGet$Predef$_mls_L0_2109_2245$1.class = class Cont$func$tupleGet$Predef$_mls_L0_2109_2245$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp;
        tmp = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 50) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 50) {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return globalThis.Array.prototype.at.call(xs3, i1)
          }
          break;
        }
      }
      toString() { return "Cont$func$tupleGet$Predef$_mls_L0_2109_2245$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$tupleGet$Predef$_mls_L0_2109_2245$1.class(50, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return globalThis.Array.prototype.at.call(xs3, i1)
  } 
  static map(f9) {
    return (...xs4) => {
      let tmp, curDepth, stackDelayRes, Cont$func$map$Predef$_mls_L0_2251_2283$1;
      Cont$func$map$Predef$_mls_L0_2251_2283$1 = function Cont$func$map$Predef$_mls_L0_2251_2283$(pc1, next1) { return new Cont$func$map$Predef$_mls_L0_2251_2283$.class(pc1, next1); };
      Cont$func$map$Predef$_mls_L0_2251_2283$1.class = class Cont$func$map$Predef$_mls_L0_2251_2283$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp1;
          tmp1 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 51) {
            stackDelayRes = value$;
          } else if (this.pc === 52) {
            tmp = value$;
          }
          contLoop: while (true) {
            if (this.pc === 51) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = Predef.pass1(f9);
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 52;
                return tmp
              }
              this.pc = 52;
              continue contLoop;
            } else if (this.pc === 52) {
              tmp = runtime.resetDepth(tmp, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return runtime.safeCall(xs4.map(tmp))
            }
            break;
          }
        }
        toString() { return "Cont$func$map$Predef$_mls_L0_2251_2283$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.tail.next = new Cont$func$map$Predef$_mls_L0_2251_2283$1.class(51, null);
        stackDelayRes.tail = stackDelayRes.tail.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = Predef.pass1(f9);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.tail.next = new Cont$func$map$Predef$_mls_L0_2251_2283$1.class(52, null);
        tmp.tail = tmp.tail.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(xs4.map(tmp))
    }
  } 
  static fold(f10) {
    return (init, ...rest) => {
      let i2, len, scrut, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, Cont$func$fold$Predef$_mls_L0_2289_2431$1;
      Cont$func$fold$Predef$_mls_L0_2289_2431$1 = function Cont$func$fold$Predef$_mls_L0_2289_2431$(pc1, next1) { return new Cont$func$fold$Predef$_mls_L0_2289_2431$.class(pc1, next1); };
      Cont$func$fold$Predef$_mls_L0_2289_2431$1.class = class Cont$func$fold$Predef$_mls_L0_2289_2431$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp4;
          tmp4 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 53) {
            stackDelayRes = value$;
          } else if (this.pc === 54) {
            tmp = value$;
          } else if (this.pc === 55) {
            tmp1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 53) {
              i2 = 0;
              len = rest.length;
              this.pc = 57;
              continue contLoop;
            } else if (this.pc === 56) {
              this.completed = true;
              return init
            } else if (this.pc === 57) {
              scrut = i2 < len;
              if (scrut === true) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp = runtime.safeCall(rest.at(i2));
                if (tmp instanceof runtime.EffectSig.class) {
                  this.pc = 54;
                  return tmp
                }
                this.pc = 54;
                continue contLoop;
              } else {
                tmp3 = runtime.Unit;
                this.pc = 56;
                continue contLoop;
              }
              this.pc = 56;
              continue contLoop;
            } else if (this.pc === 54) {
              tmp = runtime.resetDepth(tmp, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = runtime.safeCall(f10(init, tmp));
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 55;
                return tmp1
              }
              this.pc = 55;
              continue contLoop;
            } else if (this.pc === 55) {
              tmp1 = runtime.resetDepth(tmp1, curDepth);
              init = tmp1;
              tmp2 = i2 + 1;
              i2 = tmp2;
              tmp3 = runtime.Unit;
              this.pc = 57;
              continue contLoop;
            }
            break;
          }
        }
        toString() { return "Cont$func$fold$Predef$_mls_L0_2289_2431$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.tail.next = new Cont$func$fold$Predef$_mls_L0_2289_2431$1.class(53, null);
        stackDelayRes.tail = stackDelayRes.tail.next;
        return stackDelayRes
      }
      i2 = 0;
      len = rest.length;
      tmp4: while (true) {
        scrut = i2 < len;
        if (scrut === true) {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp = runtime.safeCall(rest.at(i2));
          if (tmp instanceof runtime.EffectSig.class) {
            tmp.tail.next = new Cont$func$fold$Predef$_mls_L0_2289_2431$1.class(54, null);
            tmp.tail = tmp.tail.next;
            return tmp
          }
          tmp = runtime.resetDepth(tmp, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp1 = runtime.safeCall(f10(init, tmp));
          if (tmp1 instanceof runtime.EffectSig.class) {
            tmp1.tail.next = new Cont$func$fold$Predef$_mls_L0_2289_2431$1.class(55, null);
            tmp1.tail = tmp1.tail.next;
            return tmp1
          }
          tmp1 = runtime.resetDepth(tmp1, curDepth);
          init = tmp1;
          tmp2 = i2 + 1;
          i2 = tmp2;
          tmp3 = runtime.Unit;
          continue tmp4;
        } else {
          tmp3 = runtime.Unit;
        }
        break;
      }
      return init
    }
  } 
  static foldr(f11) {
    return (first, ...rest) => {
      let len, i2, init, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, Cont$func$foldr$Predef$_mls_L0_2514_2729$1;
      Cont$func$foldr$Predef$_mls_L0_2514_2729$1 = function Cont$func$foldr$Predef$_mls_L0_2514_2729$(pc1, next1) { return new Cont$func$foldr$Predef$_mls_L0_2514_2729$.class(pc1, next1); };
      Cont$func$foldr$Predef$_mls_L0_2514_2729$1.class = class Cont$func$foldr$Predef$_mls_L0_2514_2729$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp6;
          tmp6 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 58) {
            stackDelayRes = value$;
          } else if (this.pc === 59) {
            tmp1 = value$;
          } else if (this.pc === 60) {
            tmp3 = value$;
          } else if (this.pc === 61) {
            tmp4 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 58) {
              len = rest.length;
              scrut1 = len == 0;
              if (scrut1 === true) {
                this.completed = true;
                return first
              } else {
                tmp = len - 1;
                i2 = tmp;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp1 = runtime.safeCall(rest.at(i2));
                if (tmp1 instanceof runtime.EffectSig.class) {
                  this.pc = 59;
                  return tmp1
                }
                this.pc = 59;
                continue contLoop;
              }
              this.pc = 62;
              continue contLoop;
            } else if (this.pc === 62) {
              break contLoop;
            } else if (this.pc === 59) {
              tmp1 = runtime.resetDepth(tmp1, curDepth);
              init = tmp1;
              this.pc = 64;
              continue contLoop;
            } else if (this.pc === 63) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return runtime.safeCall(f11(first, init))
            } else if (this.pc === 64) {
              scrut = i2 > 0;
              if (scrut === true) {
                tmp2 = i2 - 1;
                i2 = tmp2;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp3 = runtime.safeCall(rest.at(i2));
                if (tmp3 instanceof runtime.EffectSig.class) {
                  this.pc = 60;
                  return tmp3
                }
                this.pc = 60;
                continue contLoop;
              } else {
                tmp5 = runtime.Unit;
                this.pc = 63;
                continue contLoop;
              }
              this.pc = 63;
              continue contLoop;
            } else if (this.pc === 60) {
              tmp3 = runtime.resetDepth(tmp3, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp4 = runtime.safeCall(f11(tmp3, init));
              if (tmp4 instanceof runtime.EffectSig.class) {
                this.pc = 61;
                return tmp4
              }
              this.pc = 61;
              continue contLoop;
            } else if (this.pc === 61) {
              tmp4 = runtime.resetDepth(tmp4, curDepth);
              init = tmp4;
              tmp5 = runtime.Unit;
              this.pc = 64;
              continue contLoop;
            }
            break;
          }
        }
        toString() { return "Cont$func$foldr$Predef$_mls_L0_2514_2729$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.tail.next = new Cont$func$foldr$Predef$_mls_L0_2514_2729$1.class(58, null);
        stackDelayRes.tail = stackDelayRes.tail.next;
        return stackDelayRes
      }
      len = rest.length;
      scrut1 = len == 0;
      if (scrut1 === true) {
        return first
      } else {
        tmp = len - 1;
        i2 = tmp;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp1 = runtime.safeCall(rest.at(i2));
        if (tmp1 instanceof runtime.EffectSig.class) {
          tmp1.tail.next = new Cont$func$foldr$Predef$_mls_L0_2514_2729$1.class(59, null);
          tmp1.tail = tmp1.tail.next;
          return tmp1
        }
        tmp1 = runtime.resetDepth(tmp1, curDepth);
        init = tmp1;
        tmp6: while (true) {
          scrut = i2 > 0;
          if (scrut === true) {
            tmp2 = i2 - 1;
            i2 = tmp2;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = runtime.safeCall(rest.at(i2));
            if (tmp3 instanceof runtime.EffectSig.class) {
              tmp3.tail.next = new Cont$func$foldr$Predef$_mls_L0_2514_2729$1.class(60, null);
              tmp3.tail = tmp3.tail.next;
              return tmp3
            }
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = runtime.safeCall(f11(tmp3, init));
            if (tmp4 instanceof runtime.EffectSig.class) {
              tmp4.tail.next = new Cont$func$foldr$Predef$_mls_L0_2514_2729$1.class(61, null);
              tmp4.tail = tmp4.tail.next;
              return tmp4
            }
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            init = tmp4;
            tmp5 = runtime.Unit;
            continue tmp6;
          } else {
            tmp5 = runtime.Unit;
          }
          break;
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(f11(first, init))
      }
    }
  } 
  static stringStartsWith(string, prefix) {
    let stackDelayRes, Cont$func$stringStartsWith$Predef$_mls_L0_2736_2796$1;
    Cont$func$stringStartsWith$Predef$_mls_L0_2736_2796$1 = function Cont$func$stringStartsWith$Predef$_mls_L0_2736_2796$(pc1, next1) { return new Cont$func$stringStartsWith$Predef$_mls_L0_2736_2796$.class(pc1, next1); };
    Cont$func$stringStartsWith$Predef$_mls_L0_2736_2796$1.class = class Cont$func$stringStartsWith$Predef$_mls_L0_2736_2796$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp;
        tmp = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 65) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 65) {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return runtime.safeCall(string.startsWith(prefix))
          }
          break;
        }
      }
      toString() { return "Cont$func$stringStartsWith$Predef$_mls_L0_2736_2796$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$stringStartsWith$Predef$_mls_L0_2736_2796$1.class(65, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(string.startsWith(prefix))
  } 
  static stringGet(string1, i2) {
    let stackDelayRes, Cont$func$stringGet$Predef$_mls_L0_2802_2837$1;
    Cont$func$stringGet$Predef$_mls_L0_2802_2837$1 = function Cont$func$stringGet$Predef$_mls_L0_2802_2837$(pc1, next1) { return new Cont$func$stringGet$Predef$_mls_L0_2802_2837$.class(pc1, next1); };
    Cont$func$stringGet$Predef$_mls_L0_2802_2837$1.class = class Cont$func$stringGet$Predef$_mls_L0_2802_2837$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp;
        tmp = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 66) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 66) {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return runtime.safeCall(string1.at(i2))
          }
          break;
        }
      }
      toString() { return "Cont$func$stringGet$Predef$_mls_L0_2802_2837$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$stringGet$Predef$_mls_L0_2802_2837$1.class(66, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(string1.at(i2))
  } 
  static stringDrop(string2, n) {
    let stackDelayRes, Cont$func$stringDrop$Predef$_mls_L0_2843_2882$1;
    Cont$func$stringDrop$Predef$_mls_L0_2843_2882$1 = function Cont$func$stringDrop$Predef$_mls_L0_2843_2882$(pc1, next1) { return new Cont$func$stringDrop$Predef$_mls_L0_2843_2882$.class(pc1, next1); };
    Cont$func$stringDrop$Predef$_mls_L0_2843_2882$1.class = class Cont$func$stringDrop$Predef$_mls_L0_2843_2882$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp;
        tmp = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 67) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 67) {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return runtime.safeCall(string2.slice(n))
          }
          break;
        }
      }
      toString() { return "Cont$func$stringDrop$Predef$_mls_L0_2843_2882$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$stringDrop$Predef$_mls_L0_2843_2882$1.class(67, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(string2.slice(n))
  } 
  static get unreachable() {
    let tmp, curDepth, stackDelayRes, Cont$func$unreachable$Predef$_mls_L0_2945_2985$1;
    Cont$func$unreachable$Predef$_mls_L0_2945_2985$1 = function Cont$func$unreachable$Predef$_mls_L0_2945_2985$(pc1, next1) { return new Cont$func$unreachable$Predef$_mls_L0_2945_2985$.class(pc1, next1); };
    Cont$func$unreachable$Predef$_mls_L0_2945_2985$1.class = class Cont$func$unreachable$Predef$_mls_L0_2945_2985$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp1;
        tmp1 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 68) {
          stackDelayRes = value$;
        } else if (this.pc === 69) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 68) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = globalThis.Error("unreachable");
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 69;
              return tmp
            }
            this.pc = 69;
            continue contLoop;
          } else if (this.pc === 69) {
            tmp = runtime.resetDepth(tmp, curDepth);
            throw tmp;
          }
          break;
        }
      }
      toString() { return "Cont$func$unreachable$Predef$_mls_L0_2945_2985$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$unreachable$Predef$_mls_L0_2945_2985$1.class(68, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = globalThis.Error("unreachable");
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.tail.next = new Cont$func$unreachable$Predef$_mls_L0_2945_2985$1.class(69, null);
      tmp.tail = tmp.tail.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    throw tmp;
  } 
  static checkArgs(functionName, expected, isUB, got) {
    let scrut, name, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, tmp9, stackDelayRes, Cont$func$checkArgs$Predef$_mls_L0_2991_3536$1;
    Cont$func$checkArgs$Predef$_mls_L0_2991_3536$1 = function Cont$func$checkArgs$Predef$_mls_L0_2991_3536$(pc1, next1) { return new Cont$func$checkArgs$Predef$_mls_L0_2991_3536$.class(pc1, next1); };
    Cont$func$checkArgs$Predef$_mls_L0_2991_3536$1.class = class Cont$func$checkArgs$Predef$_mls_L0_2991_3536$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp10;
        tmp10 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 70) {
          stackDelayRes = value$;
        } else if (this.pc === 71) {
          tmp5 = value$;
        } else if (this.pc === 72) {
          tmp8 = value$;
        } else if (this.pc === 73) {
          tmp9 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 70) {
            tmp = got < expected;
            tmp1 = got > expected;
            tmp2 = isUB && tmp1;
            scrut = tmp || tmp2;
            if (scrut === true) {
              scrut1 = functionName.length > 0;
              if (scrut1 === true) {
                tmp3 = " '" + functionName;
                tmp4 = tmp3 + "'";
                this.pc = 77;
                continue contLoop;
              } else {
                tmp4 = "";
                this.pc = 77;
                continue contLoop;
              }
              this.pc = 77;
              continue contLoop;
            } else {
              this.completed = true;
              return runtime.Unit
            }
            this.pc = 74;
            continue contLoop;
          } else if (this.pc === 74) {
            break contLoop;
          } else if (this.pc === 77) {
            name = tmp4;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp5 = Predef.fold((arg11, arg2) => {
              return arg11 + arg2
            });
            if (tmp5 instanceof runtime.EffectSig.class) {
              this.pc = 71;
              return tmp5
            }
            this.pc = 71;
            continue contLoop;
          } else if (this.pc === 71) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            if (isUB === true) {
              tmp6 = "";
              this.pc = 76;
              continue contLoop;
            } else {
              tmp6 = "at least ";
              this.pc = 76;
              continue contLoop;
            }
            this.pc = 76;
            continue contLoop;
          } else if (this.pc === 76) {
            scrut2 = expected === 1;
            if (scrut2 === true) {
              tmp7 = "";
              this.pc = 75;
              continue contLoop;
            } else {
              tmp7 = "s";
              this.pc = 75;
              continue contLoop;
            }
            this.pc = 75;
            continue contLoop;
          } else if (this.pc === 75) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp8 = runtime.safeCall(tmp5("Function", name, " expected ", tmp6, expected, " argument", tmp7, " but got ", got));
            if (tmp8 instanceof runtime.EffectSig.class) {
              this.pc = 72;
              return tmp8
            }
            this.pc = 72;
            continue contLoop;
          } else if (this.pc === 72) {
            tmp8 = runtime.resetDepth(tmp8, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp9 = globalThis.Error(tmp8);
            if (tmp9 instanceof runtime.EffectSig.class) {
              this.pc = 73;
              return tmp9
            }
            this.pc = 73;
            continue contLoop;
          } else if (this.pc === 73) {
            tmp9 = runtime.resetDepth(tmp9, curDepth);
            throw tmp9;
          }
          break;
        }
      }
      toString() { return "Cont$func$checkArgs$Predef$_mls_L0_2991_3536$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$checkArgs$Predef$_mls_L0_2991_3536$1.class(70, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    tmp = got < expected;
    tmp1 = got > expected;
    tmp2 = isUB && tmp1;
    scrut = tmp || tmp2;
    if (scrut === true) {
      scrut1 = functionName.length > 0;
      if (scrut1 === true) {
        tmp3 = " '" + functionName;
        tmp4 = tmp3 + "'";
      } else {
        tmp4 = "";
      }
      name = tmp4;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp5 = Predef.fold((arg11, arg2) => {
        return arg11 + arg2
      });
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.tail.next = new Cont$func$checkArgs$Predef$_mls_L0_2991_3536$1.class(71, null);
        tmp5.tail = tmp5.tail.next;
        return tmp5
      }
      tmp5 = runtime.resetDepth(tmp5, curDepth);
      if (isUB === true) {
        tmp6 = "";
      } else {
        tmp6 = "at least ";
      }
      scrut2 = expected === 1;
      if (scrut2 === true) {
        tmp7 = "";
      } else {
        tmp7 = "s";
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp8 = runtime.safeCall(tmp5("Function", name, " expected ", tmp6, expected, " argument", tmp7, " but got ", got));
      if (tmp8 instanceof runtime.EffectSig.class) {
        tmp8.tail.next = new Cont$func$checkArgs$Predef$_mls_L0_2991_3536$1.class(72, null);
        tmp8.tail = tmp8.tail.next;
        return tmp8
      }
      tmp8 = runtime.resetDepth(tmp8, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp9 = globalThis.Error(tmp8);
      if (tmp9 instanceof runtime.EffectSig.class) {
        tmp9.tail.next = new Cont$func$checkArgs$Predef$_mls_L0_2991_3536$1.class(73, null);
        tmp9.tail = tmp9.tail.next;
        return tmp9
      }
      tmp9 = runtime.resetDepth(tmp9, curDepth);
      throw tmp9;
    } else {
      return runtime.Unit
    }
  }
  static toString() { return "Predef"; }
};
let Predef = Predef1; export default Predef;
