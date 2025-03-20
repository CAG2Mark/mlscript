import runtime from "./Runtime.mjs";
import Runtime from "./Runtime.mjs";
let Predef1;
Predef1 = class Predef {
  static {
    this.assert = globalThis.console.assert;
    this.foldl = Predef.fold;
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
        let scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, stackDelayRes, Cont$func$log$Predef$_mls_L0_4207_4345$1;
        Cont$func$log$Predef$_mls_L0_4207_4345$1 = function Cont$func$log$Predef$_mls_L0_4207_4345$(pc1) {
          return new Cont$func$log$Predef$_mls_L0_4207_4345$.class(pc1);
        };
        Cont$func$log$Predef$_mls_L0_4207_4345$1.class = class Cont$func$log$Predef$_mls_L0_4207_4345$ extends runtime.FunctionContFrame.class {
          constructor(pc) {
            let tmp5;
            tmp5 = super(null);
            this.pc = pc;
          }
          resume(value$) {
            if (this.pc === 192) {
              stackDelayRes = value$;
            } else if (this.pc === 193) {
              tmp = value$;
            } else if (this.pc === 194) {
              tmp1 = value$;
            } else if (this.pc === 195) {
              tmp3 = value$;
            }
            contLoop: while (true) {
              if (this.pc === 192) {
                scrut = TraceLogger.enabled;
                if (scrut === true) {
                  this.pc = 200;
                  continue contLoop;
                } else {
                  return runtime.Unit
                }
                this.pc = 196;
                continue contLoop;
              } else if (this.pc === 196) {
                break contLoop;
              } else if (this.pc === 197) {
                runtime.stackDepth = runtime.stackDepth + 1;
                return runtime.safeCall(globalThis.console.log(tmp4))
              } else if (this.pc === 200) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp = runtime.safeCall("| ".repeat(TraceLogger.indentLvl));
                if (tmp instanceof runtime.EffectSig.class) {
                  this.pc = 193;
                  tmp.contTrace.last.next = this;
                  tmp.contTrace.last = this;
                  return tmp
                }
                this.pc = 193;
                continue contLoop;
              } else if (this.pc === 193) {
                tmp = runtime.resetDepth(tmp, curDepth);
                this.pc = 199;
                continue contLoop;
              } else if (this.pc === 198) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp3 = msg.replaceAll("\n", tmp2);
                if (tmp3 instanceof runtime.EffectSig.class) {
                  this.pc = 195;
                  tmp3.contTrace.last.next = this;
                  tmp3.contTrace.last = this;
                  return tmp3
                }
                this.pc = 195;
                continue contLoop;
              } else if (this.pc === 199) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp1 = runtime.safeCall("  ".repeat(TraceLogger.indentLvl));
                if (tmp1 instanceof runtime.EffectSig.class) {
                  this.pc = 194;
                  tmp1.contTrace.last.next = this;
                  tmp1.contTrace.last = this;
                  return tmp1
                }
                this.pc = 194;
                continue contLoop;
              } else if (this.pc === 194) {
                tmp1 = runtime.resetDepth(tmp1, curDepth);
                tmp2 = "\n" + tmp1;
                this.pc = 198;
                continue contLoop;
              } else if (this.pc === 195) {
                tmp3 = runtime.resetDepth(tmp3, curDepth);
                tmp4 = tmp + tmp3;
                this.pc = 197;
                continue contLoop;
              }
              break;
            }
          }
          toString() { return "Cont$func$log$Predef$_mls_L0_4207_4345$(" + globalThis.Predef.render(this.pc) + ")"; }
        };
        curDepth = runtime.stackDepth;
        stackDelayRes = runtime.checkDepth();
        if (stackDelayRes instanceof runtime.EffectSig.class) {
          stackDelayRes.contTrace.last.next = new Cont$func$log$Predef$_mls_L0_4207_4345$1.class(192);
          stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
          return stackDelayRes
        }
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp = runtime.safeCall("| ".repeat(TraceLogger.indentLvl));
          if (tmp instanceof runtime.EffectSig.class) {
            tmp.contTrace.last.next = new Cont$func$log$Predef$_mls_L0_4207_4345$1.class(193);
            tmp.contTrace.last = tmp.contTrace.last.next;
            return tmp
          }
          tmp = runtime.resetDepth(tmp, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp1 = runtime.safeCall("  ".repeat(TraceLogger.indentLvl));
          if (tmp1 instanceof runtime.EffectSig.class) {
            tmp1.contTrace.last.next = new Cont$func$log$Predef$_mls_L0_4207_4345$1.class(194);
            tmp1.contTrace.last = tmp1.contTrace.last.next;
            return tmp1
          }
          tmp1 = runtime.resetDepth(tmp1, curDepth);
          tmp2 = "\n" + tmp1;
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp3 = msg.replaceAll("\n", tmp2);
          if (tmp3 instanceof runtime.EffectSig.class) {
            tmp3.contTrace.last.next = new Cont$func$log$Predef$_mls_L0_4207_4345$1.class(195);
            tmp3.contTrace.last = tmp3.contTrace.last.next;
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
        let tmp, curDepth, stackDelayRes, Cont$ctor$Test$Predef$_mls_L0_4359_4396$1;
        const this$Test = this;
        Cont$ctor$Test$Predef$_mls_L0_4359_4396$1 = function Cont$ctor$Test$Predef$_mls_L0_4359_4396$(pc1) {
          return new Cont$ctor$Test$Predef$_mls_L0_4359_4396$.class(pc1);
        };
        Cont$ctor$Test$Predef$_mls_L0_4359_4396$1.class = class Cont$ctor$Test$Predef$_mls_L0_4359_4396$ extends runtime.FunctionContFrame.class {
          constructor(pc) {
            let tmp1;
            tmp1 = super(null);
            this.pc = pc;
          }
          resume(value$) {
            if (this.pc === 201) {
              stackDelayRes = value$;
            } else if (this.pc === 202) {
              tmp = value$;
            }
            contLoop: while (true) {
              if (this.pc === 203) {
                return this$Test
              } else if (this.pc === 201) {
                this.pc = 204;
                continue contLoop;
              } else if (this.pc === 204) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp = Predef.print("Test");
                if (tmp instanceof runtime.EffectSig.class) {
                  this.pc = 202;
                  tmp.contTrace.last.next = this;
                  tmp.contTrace.last = this;
                  return tmp
                }
                this.pc = 202;
                continue contLoop;
              } else if (this.pc === 202) {
                tmp = runtime.resetDepth(tmp, curDepth);
                this$Test.y = 1;
                this.pc = 203;
                continue contLoop;
              }
              break;
            }
          }
          toString() { return "Cont$ctor$Test$Predef$_mls_L0_4359_4396$(" + globalThis.Predef.render(this.pc) + ")"; }
        };
        curDepth = runtime.stackDepth;
        stackDelayRes = runtime.checkDepth();
        if (stackDelayRes instanceof runtime.EffectSig.class) {
          stackDelayRes.contTrace.last.next = new Cont$ctor$Test$Predef$_mls_L0_4359_4396$1.class(201);
          stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
          return stackDelayRes
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp = Predef.print("Test");
        if (tmp instanceof runtime.EffectSig.class) {
          tmp.contTrace.last.next = new Cont$ctor$Test$Predef$_mls_L0_4359_4396$1.class(202);
          tmp.contTrace.last = tmp.contTrace.last.next;
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
  static apply(f, ...args) {
    let stackDelayRes, Cont$func$apply$Predef$_mls_L0_94_128$1;
    Cont$func$apply$Predef$_mls_L0_94_128$1 = function Cont$func$apply$Predef$_mls_L0_94_128$(pc1) {
      return new Cont$func$apply$Predef$_mls_L0_94_128$.class(pc1);
    };
    Cont$func$apply$Predef$_mls_L0_94_128$1.class = class Cont$func$apply$Predef$_mls_L0_94_128$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp;
        tmp = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 0) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 0) {
            this.pc = 1;
            continue contLoop;
          } else if (this.pc === 1) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(f(...args))
          }
          break;
        }
      }
      toString() { return "Cont$func$apply$Predef$_mls_L0_94_128$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$apply$Predef$_mls_L0_94_128$1.class(0);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(f(...args))
  } 
  static pipeInto(x2, f1) {
    let stackDelayRes, Cont$func$pipeInto$Predef$_mls_L0_134_160$1;
    Cont$func$pipeInto$Predef$_mls_L0_134_160$1 = function Cont$func$pipeInto$Predef$_mls_L0_134_160$(pc1) {
      return new Cont$func$pipeInto$Predef$_mls_L0_134_160$.class(pc1);
    };
    Cont$func$pipeInto$Predef$_mls_L0_134_160$1.class = class Cont$func$pipeInto$Predef$_mls_L0_134_160$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp;
        tmp = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 2) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 2) {
            this.pc = 3;
            continue contLoop;
          } else if (this.pc === 3) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(f1(x2))
          }
          break;
        }
      }
      toString() { return "Cont$func$pipeInto$Predef$_mls_L0_134_160$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$pipeInto$Predef$_mls_L0_134_160$1.class(2);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(f1(x2))
  } 
  static pipeFrom(f2, x3) {
    let stackDelayRes, Cont$func$pipeFrom$Predef$_mls_L0_165_191$1;
    Cont$func$pipeFrom$Predef$_mls_L0_165_191$1 = function Cont$func$pipeFrom$Predef$_mls_L0_165_191$(pc1) {
      return new Cont$func$pipeFrom$Predef$_mls_L0_165_191$.class(pc1);
    };
    Cont$func$pipeFrom$Predef$_mls_L0_165_191$1.class = class Cont$func$pipeFrom$Predef$_mls_L0_165_191$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp;
        tmp = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 4) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 4) {
            this.pc = 5;
            continue contLoop;
          } else if (this.pc === 5) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(f2(x3))
          }
          break;
        }
      }
      toString() { return "Cont$func$pipeFrom$Predef$_mls_L0_165_191$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$pipeFrom$Predef$_mls_L0_165_191$1.class(4);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(f2(x3))
  } 
  static tap(x4, f3) {
    let tmp, curDepth, stackDelayRes, Cont$func$tap$Predef$_mls_L0_197_221$1;
    Cont$func$tap$Predef$_mls_L0_197_221$1 = function Cont$func$tap$Predef$_mls_L0_197_221$(pc1) {
      return new Cont$func$tap$Predef$_mls_L0_197_221$.class(pc1);
    };
    Cont$func$tap$Predef$_mls_L0_197_221$1.class = class Cont$func$tap$Predef$_mls_L0_197_221$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp1;
        tmp1 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 6) {
          stackDelayRes = value$;
        } else if (this.pc === 7) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 6) {
            this.pc = 8;
            continue contLoop;
          } else if (this.pc === 8) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = runtime.safeCall(f3(x4));
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 7;
              tmp.contTrace.last.next = this;
              tmp.contTrace.last = this;
              return tmp
            }
            this.pc = 7;
            continue contLoop;
          } else if (this.pc === 7) {
            tmp = runtime.resetDepth(tmp, curDepth);
            return (tmp , x4)
          }
          break;
        }
      }
      toString() { return "Cont$func$tap$Predef$_mls_L0_197_221$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$tap$Predef$_mls_L0_197_221$1.class(6);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = runtime.safeCall(f3(x4));
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = new Cont$func$tap$Predef$_mls_L0_197_221$1.class(7);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    return (tmp , x4)
  } 
  static pat(f4, x5) {
    let tmp, curDepth, stackDelayRes, Cont$func$pat$Predef$_mls_L0_226_250$1;
    Cont$func$pat$Predef$_mls_L0_226_250$1 = function Cont$func$pat$Predef$_mls_L0_226_250$(pc1) {
      return new Cont$func$pat$Predef$_mls_L0_226_250$.class(pc1);
    };
    Cont$func$pat$Predef$_mls_L0_226_250$1.class = class Cont$func$pat$Predef$_mls_L0_226_250$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp1;
        tmp1 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 9) {
          stackDelayRes = value$;
        } else if (this.pc === 10) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 9) {
            this.pc = 11;
            continue contLoop;
          } else if (this.pc === 11) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = runtime.safeCall(f4(x5));
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 10;
              tmp.contTrace.last.next = this;
              tmp.contTrace.last = this;
              return tmp
            }
            this.pc = 10;
            continue contLoop;
          } else if (this.pc === 10) {
            tmp = runtime.resetDepth(tmp, curDepth);
            return (tmp , x5)
          }
          break;
        }
      }
      toString() { return "Cont$func$pat$Predef$_mls_L0_226_250$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$pat$Predef$_mls_L0_226_250$1.class(9);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = runtime.safeCall(f4(x5));
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = new Cont$func$pat$Predef$_mls_L0_226_250$1.class(10);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    return (tmp , x5)
  } 
  static andThen(f5, g) {
    return (x6) => {
      let tmp, curDepth, stackDelayRes, Cont$func$andThen$Predef$_mls_L0_256_287$1;
      Cont$func$andThen$Predef$_mls_L0_256_287$1 = function Cont$func$andThen$Predef$_mls_L0_256_287$(pc1) {
        return new Cont$func$andThen$Predef$_mls_L0_256_287$.class(pc1);
      };
      Cont$func$andThen$Predef$_mls_L0_256_287$1.class = class Cont$func$andThen$Predef$_mls_L0_256_287$ extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp1;
          tmp1 = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 12) {
            stackDelayRes = value$;
          } else if (this.pc === 13) {
            tmp = value$;
          }
          contLoop: while (true) {
            if (this.pc === 12) {
              this.pc = 15;
              continue contLoop;
            } else if (this.pc === 14) {
              runtime.stackDepth = runtime.stackDepth + 1;
              return runtime.safeCall(g(tmp))
            } else if (this.pc === 15) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = runtime.safeCall(f5(x6));
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 13;
                tmp.contTrace.last.next = this;
                tmp.contTrace.last = this;
                return tmp
              }
              this.pc = 13;
              continue contLoop;
            } else if (this.pc === 13) {
              tmp = runtime.resetDepth(tmp, curDepth);
              this.pc = 14;
              continue contLoop;
            }
            break;
          }
        }
        toString() { return "Cont$func$andThen$Predef$_mls_L0_256_287$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = new Cont$func$andThen$Predef$_mls_L0_256_287$1.class(12);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = runtime.safeCall(f5(x6));
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = new Cont$func$andThen$Predef$_mls_L0_256_287$1.class(13);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(g(tmp))
    }
  } 
  static compose(f6, g1) {
    return (x6) => {
      let tmp, curDepth, stackDelayRes, Cont$func$compose$Predef$_mls_L0_292_323$1;
      Cont$func$compose$Predef$_mls_L0_292_323$1 = function Cont$func$compose$Predef$_mls_L0_292_323$(pc1) {
        return new Cont$func$compose$Predef$_mls_L0_292_323$.class(pc1);
      };
      Cont$func$compose$Predef$_mls_L0_292_323$1.class = class Cont$func$compose$Predef$_mls_L0_292_323$ extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp1;
          tmp1 = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 16) {
            stackDelayRes = value$;
          } else if (this.pc === 17) {
            tmp = value$;
          }
          contLoop: while (true) {
            if (this.pc === 16) {
              this.pc = 19;
              continue contLoop;
            } else if (this.pc === 18) {
              runtime.stackDepth = runtime.stackDepth + 1;
              return runtime.safeCall(f6(tmp))
            } else if (this.pc === 19) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = runtime.safeCall(g1(x6));
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 17;
                tmp.contTrace.last.next = this;
                tmp.contTrace.last = this;
                return tmp
              }
              this.pc = 17;
              continue contLoop;
            } else if (this.pc === 17) {
              tmp = runtime.resetDepth(tmp, curDepth);
              this.pc = 18;
              continue contLoop;
            }
            break;
          }
        }
        toString() { return "Cont$func$compose$Predef$_mls_L0_292_323$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = new Cont$func$compose$Predef$_mls_L0_292_323$1.class(16);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = runtime.safeCall(g1(x6));
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = new Cont$func$compose$Predef$_mls_L0_292_323$1.class(17);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f6(tmp))
    }
  } 
  static passTo(receiver, f7) {
    return (...args1) => {
      let stackDelayRes, Cont$func$passTo$Predef$_mls_L0_329_384$1;
      Cont$func$passTo$Predef$_mls_L0_329_384$1 = function Cont$func$passTo$Predef$_mls_L0_329_384$(pc1) {
        return new Cont$func$passTo$Predef$_mls_L0_329_384$.class(pc1);
      };
      Cont$func$passTo$Predef$_mls_L0_329_384$1.class = class Cont$func$passTo$Predef$_mls_L0_329_384$ extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp;
          tmp = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 20) {
            stackDelayRes = value$;
          }
          contLoop: while (true) {
            if (this.pc === 20) {
              this.pc = 21;
              continue contLoop;
            } else if (this.pc === 21) {
              runtime.stackDepth = runtime.stackDepth + 1;
              return runtime.safeCall(f7(receiver, ...args1))
            }
            break;
          }
        }
        toString() { return "Cont$func$passTo$Predef$_mls_L0_329_384$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = new Cont$func$passTo$Predef$_mls_L0_329_384$1.class(20);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f7(receiver, ...args1))
    }
  } 
  static call(receiver1, f8) {
    return (...args1) => {
      let stackDelayRes, Cont$func$call$Predef$_mls_L0_390_450$1;
      Cont$func$call$Predef$_mls_L0_390_450$1 = function Cont$func$call$Predef$_mls_L0_390_450$(pc1) {
        return new Cont$func$call$Predef$_mls_L0_390_450$.class(pc1);
      };
      Cont$func$call$Predef$_mls_L0_390_450$1.class = class Cont$func$call$Predef$_mls_L0_390_450$ extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp;
          tmp = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 22) {
            stackDelayRes = value$;
          }
          contLoop: while (true) {
            if (this.pc === 22) {
              this.pc = 23;
              continue contLoop;
            } else if (this.pc === 23) {
              runtime.stackDepth = runtime.stackDepth + 1;
              return f8.call(receiver1, ...args1)
            }
            break;
          }
        }
        toString() { return "Cont$func$call$Predef$_mls_L0_390_450$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = new Cont$func$call$Predef$_mls_L0_390_450$1.class(22);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return f8.call(receiver1, ...args1)
    }
  } 
  static pass1(f9) {
    return (...xs) => {
      let stackDelayRes, Cont$func$pass1$Predef$_mls_L0_456_481$1;
      Cont$func$pass1$Predef$_mls_L0_456_481$1 = function Cont$func$pass1$Predef$_mls_L0_456_481$(pc1) {
        return new Cont$func$pass1$Predef$_mls_L0_456_481$.class(pc1);
      };
      Cont$func$pass1$Predef$_mls_L0_456_481$1.class = class Cont$func$pass1$Predef$_mls_L0_456_481$ extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp;
          tmp = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 24) {
            stackDelayRes = value$;
          }
          contLoop: while (true) {
            if (this.pc === 24) {
              this.pc = 25;
              continue contLoop;
            } else if (this.pc === 25) {
              runtime.stackDepth = runtime.stackDepth + 1;
              return runtime.safeCall(f9(xs[0]))
            }
            break;
          }
        }
        toString() { return "Cont$func$pass1$Predef$_mls_L0_456_481$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = new Cont$func$pass1$Predef$_mls_L0_456_481$1.class(24);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f9(xs[0]))
    }
  } 
  static pass2(f10) {
    return (...xs) => {
      let stackDelayRes, Cont$func$pass2$Predef$_mls_L0_486_517$1;
      Cont$func$pass2$Predef$_mls_L0_486_517$1 = function Cont$func$pass2$Predef$_mls_L0_486_517$(pc1) {
        return new Cont$func$pass2$Predef$_mls_L0_486_517$.class(pc1);
      };
      Cont$func$pass2$Predef$_mls_L0_486_517$1.class = class Cont$func$pass2$Predef$_mls_L0_486_517$ extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp;
          tmp = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 26) {
            stackDelayRes = value$;
          }
          contLoop: while (true) {
            if (this.pc === 26) {
              this.pc = 27;
              continue contLoop;
            } else if (this.pc === 27) {
              runtime.stackDepth = runtime.stackDepth + 1;
              return runtime.safeCall(f10(xs[0], xs[1]))
            }
            break;
          }
        }
        toString() { return "Cont$func$pass2$Predef$_mls_L0_486_517$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = new Cont$func$pass2$Predef$_mls_L0_486_517$1.class(26);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f10(xs[0], xs[1]))
    }
  } 
  static pass3(f11) {
    return (...xs) => {
      let stackDelayRes, Cont$func$pass3$Predef$_mls_L0_522_559$1;
      Cont$func$pass3$Predef$_mls_L0_522_559$1 = function Cont$func$pass3$Predef$_mls_L0_522_559$(pc1) {
        return new Cont$func$pass3$Predef$_mls_L0_522_559$.class(pc1);
      };
      Cont$func$pass3$Predef$_mls_L0_522_559$1.class = class Cont$func$pass3$Predef$_mls_L0_522_559$ extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp;
          tmp = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 28) {
            stackDelayRes = value$;
          }
          contLoop: while (true) {
            if (this.pc === 28) {
              this.pc = 29;
              continue contLoop;
            } else if (this.pc === 29) {
              runtime.stackDepth = runtime.stackDepth + 1;
              return runtime.safeCall(f11(xs[0], xs[1], xs[2]))
            }
            break;
          }
        }
        toString() { return "Cont$func$pass3$Predef$_mls_L0_522_559$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = new Cont$func$pass3$Predef$_mls_L0_522_559$1.class(28);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f11(xs[0], xs[1], xs[2]))
    }
  } 
  static passing(f12, ...args1) {
    let stackDelayRes, Cont$func$passing$Predef$_mls_L0_565_608$1;
    Cont$func$passing$Predef$_mls_L0_565_608$1 = function Cont$func$passing$Predef$_mls_L0_565_608$(pc1) {
      return new Cont$func$passing$Predef$_mls_L0_565_608$.class(pc1);
    };
    Cont$func$passing$Predef$_mls_L0_565_608$1.class = class Cont$func$passing$Predef$_mls_L0_565_608$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp;
        tmp = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 30) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 30) {
            this.pc = 31;
            continue contLoop;
          } else if (this.pc === 31) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return f12.bind(null, ...args1)
          }
          break;
        }
      }
      toString() { return "Cont$func$passing$Predef$_mls_L0_565_608$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$passing$Predef$_mls_L0_565_608$1.class(30);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return f12.bind(null, ...args1)
  } 
  static print(...xs) {
    let tmp, tmp1, curDepth, stackDelayRes, Cont$func$print$Predef$_mls_L0_615_671$1;
    Cont$func$print$Predef$_mls_L0_615_671$1 = function Cont$func$print$Predef$_mls_L0_615_671$(pc1) {
      return new Cont$func$print$Predef$_mls_L0_615_671$.class(pc1);
    };
    Cont$func$print$Predef$_mls_L0_615_671$1.class = class Cont$func$print$Predef$_mls_L0_615_671$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp2;
        tmp2 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 32) {
          stackDelayRes = value$;
        } else if (this.pc === 33) {
          tmp = value$;
        } else if (this.pc === 34) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 32) {
            this.pc = 37;
            continue contLoop;
          } else if (this.pc === 35) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(globalThis.console.log(...tmp1))
          } else if (this.pc === 37) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = Predef.map(Predef.renderAsStr);
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 33;
              tmp.contTrace.last.next = this;
              tmp.contTrace.last = this;
              return tmp
            }
            this.pc = 33;
            continue contLoop;
          } else if (this.pc === 33) {
            tmp = runtime.resetDepth(tmp, curDepth);
            this.pc = 36;
            continue contLoop;
          } else if (this.pc === 36) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = runtime.safeCall(tmp(...xs));
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 34;
              tmp1.contTrace.last.next = this;
              tmp1.contTrace.last = this;
              return tmp1
            }
            this.pc = 34;
            continue contLoop;
          } else if (this.pc === 34) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            this.pc = 35;
            continue contLoop;
          }
          break;
        }
      }
      toString() { return "Cont$func$print$Predef$_mls_L0_615_671$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$print$Predef$_mls_L0_615_671$1.class(32);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = Predef.map(Predef.renderAsStr);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = new Cont$func$print$Predef$_mls_L0_615_671$1.class(33);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = runtime.safeCall(tmp(...xs));
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = new Cont$func$print$Predef$_mls_L0_615_671$1.class(34);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(globalThis.console.log(...tmp1))
  } 
  static printRaw(x6) {
    let tmp, curDepth, stackDelayRes, Cont$func$printRaw$Predef$_mls_L0_677_715$1;
    Cont$func$printRaw$Predef$_mls_L0_677_715$1 = function Cont$func$printRaw$Predef$_mls_L0_677_715$(pc1) {
      return new Cont$func$printRaw$Predef$_mls_L0_677_715$.class(pc1);
    };
    Cont$func$printRaw$Predef$_mls_L0_677_715$1.class = class Cont$func$printRaw$Predef$_mls_L0_677_715$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp1;
        tmp1 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 38) {
          stackDelayRes = value$;
        } else if (this.pc === 39) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 38) {
            this.pc = 41;
            continue contLoop;
          } else if (this.pc === 40) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(globalThis.console.log(tmp))
          } else if (this.pc === 41) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = Predef.render(x6);
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 39;
              tmp.contTrace.last.next = this;
              tmp.contTrace.last = this;
              return tmp
            }
            this.pc = 39;
            continue contLoop;
          } else if (this.pc === 39) {
            tmp = runtime.resetDepth(tmp, curDepth);
            this.pc = 40;
            continue contLoop;
          }
          break;
        }
      }
      toString() { return "Cont$func$printRaw$Predef$_mls_L0_677_715$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$printRaw$Predef$_mls_L0_677_715$1.class(38);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = Predef.render(x6);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = new Cont$func$printRaw$Predef$_mls_L0_677_715$1.class(39);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(globalThis.console.log(tmp))
  } 
  static interleave(sep) {
    return (...args2) => {
      let res, len, i, scrut, idx, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, Cont$func$interleave$Predef$_mls_L0_721_998$1;
      Cont$func$interleave$Predef$_mls_L0_721_998$1 = function Cont$func$interleave$Predef$_mls_L0_721_998$(pc1) {
        return new Cont$func$interleave$Predef$_mls_L0_721_998$.class(pc1);
      };
      Cont$func$interleave$Predef$_mls_L0_721_998$1.class = class Cont$func$interleave$Predef$_mls_L0_721_998$ extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp8;
          tmp8 = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 42) {
            stackDelayRes = value$;
          } else if (this.pc === 43) {
            tmp2 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 42) {
              scrut2 = args2.length === 0;
              if (scrut2 === true) {
                this.pc = 45;
                continue contLoop;
              } else {
                tmp = args2.length * 2;
                tmp1 = tmp - 1;
                this.pc = 49;
                continue contLoop;
              }
              this.pc = 44;
              continue contLoop;
            } else if (this.pc === 44) {
              break contLoop;
            } else if (this.pc === 49) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp2 = globalThis.Array(tmp1);
              if (tmp2 instanceof runtime.EffectSig.class) {
                this.pc = 43;
                tmp2.contTrace.last.next = this;
                tmp2.contTrace.last = this;
                return tmp2
              }
              this.pc = 43;
              continue contLoop;
            } else if (this.pc === 43) {
              tmp2 = runtime.resetDepth(tmp2, curDepth);
              res = tmp2;
              len = args2.length;
              i = 0;
              this.pc = 47;
              continue contLoop;
            } else if (this.pc === 46) {
              return res
            } else if (this.pc === 47) {
              scrut = i < len;
              if (scrut === true) {
                tmp3 = i * 2;
                idx = tmp3;
                res[idx] = args2[i];
                tmp4 = i + 1;
                i = tmp4;
                scrut1 = i < len;
                if (scrut1 === true) {
                  tmp5 = idx + 1;
                  res[tmp5] = sep;
                  tmp6 = runtime.Unit;
                  this.pc = 48;
                  continue contLoop;
                } else {
                  tmp6 = runtime.Unit;
                  this.pc = 48;
                  continue contLoop;
                }
                this.pc = 48;
                continue contLoop;
              } else {
                tmp7 = runtime.Unit;
                this.pc = 46;
                continue contLoop;
              }
              this.pc = 46;
              continue contLoop;
            } else if (this.pc === 48) {
              tmp7 = tmp6;
              this.pc = 47;
              continue contLoop;
            } else if (this.pc === 45) {
              return []
            }
            break;
          }
        }
        toString() { return "Cont$func$interleave$Predef$_mls_L0_721_998$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = new Cont$func$interleave$Predef$_mls_L0_721_998$1.class(42);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      scrut2 = args2.length === 0;
      if (scrut2 === true) {
        return []
      } else {
        tmp = args2.length * 2;
        tmp1 = tmp - 1;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp2 = globalThis.Array(tmp1);
        if (tmp2 instanceof runtime.EffectSig.class) {
          tmp2.contTrace.last.next = new Cont$func$interleave$Predef$_mls_L0_721_998$1.class(43);
          tmp2.contTrace.last = tmp2.contTrace.last.next;
          return tmp2
        }
        tmp2 = runtime.resetDepth(tmp2, curDepth);
        res = tmp2;
        len = args2.length;
        i = 0;
        tmp8: while (true) {
          scrut = i < len;
          if (scrut === true) {
            tmp3 = i * 2;
            idx = tmp3;
            res[idx] = args2[i];
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
    let stackDelayRes, Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$1;
    Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$1 = function Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$(pc1) {
      return new Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$.class(pc1);
    };
    Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$1.class = class Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp;
        tmp = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 50) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 50) {
            if (typeof arg === 'string') {
              return arg
            } else {
              this.pc = 52;
              continue contLoop;
            }
            this.pc = 51;
            continue contLoop;
          } else if (this.pc === 51) {
            break contLoop;
          } else if (this.pc === 52) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return Predef.render(arg)
          }
          break;
        }
      }
      toString() { return "Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$1.class(50);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
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
    let ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, curDepth, stackDelayRes, Cont$func$render$Predef$_mls_L0_1070_2080$1;
    Cont$func$render$Predef$_mls_L0_1070_2080$1 = function Cont$func$render$Predef$_mls_L0_1070_2080$(pc1) {
      return new Cont$func$render$Predef$_mls_L0_1070_2080$.class(pc1);
    };
    Cont$func$render$Predef$_mls_L0_1070_2080$1.class = class Cont$func$render$Predef$_mls_L0_1070_2080$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp35;
        tmp35 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 53) {
          stackDelayRes = value$;
        } else if (this.pc === 81) {
          tmp26 = value$;
        } else if (this.pc === 82) {
          tmp27 = value$;
        } else if (this.pc === 83) {
          tmp28 = value$;
        } else if (this.pc === 89) {
          tmp30 = value$;
        } else if (this.pc === 90) {
          tmp31 = value$;
        } else if (this.pc === 91) {
          tmp32 = value$;
        } else if (this.pc === 69) {
          p = value$;
        } else if (this.pc === 70) {
          tmp19 = value$;
        } else if (this.pc === 71) {
          tmp20 = value$;
        } else if (this.pc === 72) {
          tmp21 = value$;
        } else if (this.pc === 78) {
          tmp23 = value$;
        } else if (this.pc === 79) {
          tmp24 = value$;
        } else if (this.pc === 80) {
          tmp25 = value$;
        } else if (this.pc === 64) {
          tmp10 = value$;
        } else if (this.pc === 65) {
          tmp11 = value$;
        } else if (this.pc === 66) {
          tmp12 = value$;
        } else if (this.pc === 67) {
          tmp13 = value$;
        } else if (this.pc === 68) {
          tmp14 = value$;
        } else if (this.pc === 59) {
          tmp5 = value$;
        } else if (this.pc === 60) {
          tmp6 = value$;
        } else if (this.pc === 61) {
          tmp7 = value$;
        } else if (this.pc === 62) {
          tmp8 = value$;
        } else if (this.pc === 63) {
          tmp9 = value$;
        } else if (this.pc === 54) {
          tmp = value$;
        } else if (this.pc === 55) {
          tmp1 = value$;
        } else if (this.pc === 56) {
          tmp2 = value$;
        } else if (this.pc === 57) {
          tmp3 = value$;
        } else if (this.pc === 58) {
          tmp4 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 53) {
            if (arg1 === undefined) {
              return "undefined"
            } else if (arg1 === null) {
              return "null";
              this.pc = 92;
              continue contLoop;
            } else if (arg1 instanceof globalThis.Array) {
              this.pc = 98;
              continue contLoop;
              this.pc = 92;
              continue contLoop;
              this.pc = 92;
              continue contLoop;
            } else {
              if (typeof arg1 === 'string') {
                this.pc = 99;
                continue contLoop;
              } else if (arg1 instanceof globalThis.Set) {
                this.pc = 105;
                continue contLoop;
                this.pc = 92;
                continue contLoop;
              } else if (arg1 instanceof globalThis.Map) {
                this.pc = 111;
                continue contLoop;
                this.pc = 92;
                continue contLoop;
                this.pc = 92;
                continue contLoop;
              } else if (arg1 instanceof globalThis.Function) {
                this.pc = 123;
                continue contLoop;
                this.pc = 92;
                continue contLoop;
                this.pc = 92;
                continue contLoop;
                this.pc = 92;
                continue contLoop;
              } else if (arg1 instanceof globalThis.Object) {
                scrut = arg1.constructor.name;
                if (scrut === "Object") {
                  this.pc = 130;
                  continue contLoop;
                } else {
                  this.pc = 131;
                  continue contLoop;
                }
                this.pc = 92;
                continue contLoop;
                this.pc = 92;
                continue contLoop;
                this.pc = 92;
                continue contLoop;
                this.pc = 92;
                continue contLoop;
                this.pc = 92;
                continue contLoop;
              } else {
                ts = arg1["toString"];
                if (ts === undefined) {
                  tmp33 = typeof arg1;
                  tmp34 = "[" + tmp33;
                  return tmp34 + "]"
                } else {
                  this.pc = 132;
                  continue contLoop;
                }
                this.pc = 92;
                continue contLoop;
              }
              this.pc = 92;
              continue contLoop;
            }
            this.pc = 92;
            continue contLoop;
          } else if (this.pc === 92) {
            break contLoop;
          } else if (this.pc === 132) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(ts.call(arg1))
          } else if (this.pc === 131) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return globalThis.String(arg1)
          } else if (this.pc === 130) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp26 = runtime.safeCall(globalThis.Object.entries(arg1));
            if (tmp26 instanceof runtime.EffectSig.class) {
              this.pc = 81;
              tmp26.contTrace.last.next = this;
              tmp26.contTrace.last = this;
              return tmp26
            }
            this.pc = 81;
            continue contLoop;
          } else if (this.pc === 81) {
            tmp26 = runtime.resetDepth(tmp26, curDepth);
            es = tmp26;
            this.pc = 129;
            continue contLoop;
          } else if (this.pc === 129) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp27 = Predef.fold(lambda5);
            if (tmp27 instanceof runtime.EffectSig.class) {
              this.pc = 82;
              tmp27.contTrace.last.next = this;
              tmp27.contTrace.last = this;
              return tmp27
            }
            this.pc = 82;
            continue contLoop;
          } else if (this.pc === 82) {
            tmp27 = runtime.resetDepth(tmp27, curDepth);
            this.pc = 128;
            continue contLoop;
          } else if (this.pc === 124) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(tmp27("{", ...tmp32, "}"))
          } else if (this.pc === 128) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp28 = Predef.interleave(", ");
            if (tmp28 instanceof runtime.EffectSig.class) {
              this.pc = 83;
              tmp28.contTrace.last.next = this;
              tmp28.contTrace.last = this;
              return tmp28
            }
            this.pc = 83;
            continue contLoop;
          } else if (this.pc === 83) {
            tmp28 = runtime.resetDepth(tmp28, curDepth);
            tmp29 = lambda6;
            this.pc = 127;
            continue contLoop;
          } else if (this.pc === 125) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp32 = runtime.safeCall(tmp28(...tmp31));
            if (tmp32 instanceof runtime.EffectSig.class) {
              this.pc = 91;
              tmp32.contTrace.last.next = this;
              tmp32.contTrace.last = this;
              return tmp32
            }
            this.pc = 91;
            continue contLoop;
          } else if (this.pc === 127) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp30 = Predef.map(tmp29);
            if (tmp30 instanceof runtime.EffectSig.class) {
              this.pc = 89;
              tmp30.contTrace.last.next = this;
              tmp30.contTrace.last = this;
              return tmp30
            }
            this.pc = 89;
            continue contLoop;
          } else if (this.pc === 89) {
            tmp30 = runtime.resetDepth(tmp30, curDepth);
            this.pc = 126;
            continue contLoop;
          } else if (this.pc === 126) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp31 = runtime.safeCall(tmp30(...es));
            if (tmp31 instanceof runtime.EffectSig.class) {
              this.pc = 90;
              tmp31.contTrace.last.next = this;
              tmp31.contTrace.last = this;
              return tmp31
            }
            this.pc = 90;
            continue contLoop;
          } else if (this.pc === 90) {
            tmp31 = runtime.resetDepth(tmp31, curDepth);
            this.pc = 125;
            continue contLoop;
          } else if (this.pc === 91) {
            tmp32 = runtime.resetDepth(tmp32, curDepth);
            this.pc = 124;
            continue contLoop;
          } else if (this.pc === 123) {
            runtime.stackDepth = runtime.stackDepth + 1;
            p = globalThis.Object.getOwnPropertyDescriptor(arg1, "prototype");
            if (p instanceof runtime.EffectSig.class) {
              this.pc = 69;
              p.contTrace.last.next = this;
              p.contTrace.last = this;
              return p
            }
            this.pc = 69;
            continue contLoop;
          } else if (this.pc === 69) {
            p = runtime.resetDepth(p, curDepth);
            if (p instanceof globalThis.Object) {
              scrut1 = p["writable"];
              if (scrut1 === true) {
                tmp15 = true;
                this.pc = 122;
                continue contLoop;
              } else {
                tmp15 = false;
                this.pc = 122;
                continue contLoop;
              }
              this.pc = 122;
              continue contLoop;
            } else {
              tmp15 = false;
              this.pc = 122;
              continue contLoop;
            }
            this.pc = 122;
            continue contLoop;
          } else if (this.pc === 122) {
            if (p === undefined) {
              tmp16 = true;
              this.pc = 121;
              continue contLoop;
            } else {
              tmp16 = false;
              this.pc = 121;
              continue contLoop;
            }
            this.pc = 121;
            continue contLoop;
          } else if (this.pc === 121) {
            scrut2 = tmp15 || tmp16;
            if (scrut2 === true) {
              scrut3 = arg1.name;
              if (scrut3 === "") {
                tmp17 = "";
                this.pc = 112;
                continue contLoop;
              } else {
                nme = scrut3;
                tmp17 = " " + nme;
                this.pc = 112;
                continue contLoop;
              }
              this.pc = 112;
              continue contLoop;
            } else {
              scrut = arg1.constructor.name;
              if (scrut === "Object") {
                this.pc = 119;
                continue contLoop;
              } else {
                this.pc = 120;
                continue contLoop;
              }
              this.pc = 92;
              continue contLoop;
            }
            this.pc = 92;
            continue contLoop;
          } else if (this.pc === 120) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return globalThis.String(arg1)
          } else if (this.pc === 119) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp19 = runtime.safeCall(globalThis.Object.entries(arg1));
            if (tmp19 instanceof runtime.EffectSig.class) {
              this.pc = 70;
              tmp19.contTrace.last.next = this;
              tmp19.contTrace.last = this;
              return tmp19
            }
            this.pc = 70;
            continue contLoop;
          } else if (this.pc === 70) {
            tmp19 = runtime.resetDepth(tmp19, curDepth);
            es = tmp19;
            this.pc = 118;
            continue contLoop;
          } else if (this.pc === 118) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp20 = Predef.fold(lambda3);
            if (tmp20 instanceof runtime.EffectSig.class) {
              this.pc = 71;
              tmp20.contTrace.last.next = this;
              tmp20.contTrace.last = this;
              return tmp20
            }
            this.pc = 71;
            continue contLoop;
          } else if (this.pc === 71) {
            tmp20 = runtime.resetDepth(tmp20, curDepth);
            this.pc = 117;
            continue contLoop;
          } else if (this.pc === 113) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(tmp20("{", ...tmp25, "}"))
          } else if (this.pc === 117) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp21 = Predef.interleave(", ");
            if (tmp21 instanceof runtime.EffectSig.class) {
              this.pc = 72;
              tmp21.contTrace.last.next = this;
              tmp21.contTrace.last = this;
              return tmp21
            }
            this.pc = 72;
            continue contLoop;
          } else if (this.pc === 72) {
            tmp21 = runtime.resetDepth(tmp21, curDepth);
            tmp22 = lambda4;
            this.pc = 116;
            continue contLoop;
          } else if (this.pc === 114) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp25 = runtime.safeCall(tmp21(...tmp24));
            if (tmp25 instanceof runtime.EffectSig.class) {
              this.pc = 80;
              tmp25.contTrace.last.next = this;
              tmp25.contTrace.last = this;
              return tmp25
            }
            this.pc = 80;
            continue contLoop;
          } else if (this.pc === 116) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp23 = Predef.map(tmp22);
            if (tmp23 instanceof runtime.EffectSig.class) {
              this.pc = 78;
              tmp23.contTrace.last.next = this;
              tmp23.contTrace.last = this;
              return tmp23
            }
            this.pc = 78;
            continue contLoop;
          } else if (this.pc === 78) {
            tmp23 = runtime.resetDepth(tmp23, curDepth);
            this.pc = 115;
            continue contLoop;
          } else if (this.pc === 115) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp24 = runtime.safeCall(tmp23(...es));
            if (tmp24 instanceof runtime.EffectSig.class) {
              this.pc = 79;
              tmp24.contTrace.last.next = this;
              tmp24.contTrace.last = this;
              return tmp24
            }
            this.pc = 79;
            continue contLoop;
          } else if (this.pc === 79) {
            tmp24 = runtime.resetDepth(tmp24, curDepth);
            this.pc = 114;
            continue contLoop;
          } else if (this.pc === 80) {
            tmp25 = runtime.resetDepth(tmp25, curDepth);
            this.pc = 113;
            continue contLoop;
          } else if (this.pc === 112) {
            tmp18 = "[function" + tmp17;
            return tmp18 + "]"
          } else if (this.pc === 111) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp10 = Predef.fold(lambda2);
            if (tmp10 instanceof runtime.EffectSig.class) {
              this.pc = 64;
              tmp10.contTrace.last.next = this;
              tmp10.contTrace.last = this;
              return tmp10
            }
            this.pc = 64;
            continue contLoop;
          } else if (this.pc === 64) {
            tmp10 = runtime.resetDepth(tmp10, curDepth);
            this.pc = 110;
            continue contLoop;
          } else if (this.pc === 106) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(tmp10("Map{", ...tmp14, "}"))
          } else if (this.pc === 110) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp11 = Predef.interleave(", ");
            if (tmp11 instanceof runtime.EffectSig.class) {
              this.pc = 65;
              tmp11.contTrace.last.next = this;
              tmp11.contTrace.last = this;
              return tmp11
            }
            this.pc = 65;
            continue contLoop;
          } else if (this.pc === 65) {
            tmp11 = runtime.resetDepth(tmp11, curDepth);
            this.pc = 109;
            continue contLoop;
          } else if (this.pc === 107) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp14 = runtime.safeCall(tmp11(...tmp13));
            if (tmp14 instanceof runtime.EffectSig.class) {
              this.pc = 68;
              tmp14.contTrace.last.next = this;
              tmp14.contTrace.last = this;
              return tmp14
            }
            this.pc = 68;
            continue contLoop;
          } else if (this.pc === 109) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp12 = Predef.map(Predef.render);
            if (tmp12 instanceof runtime.EffectSig.class) {
              this.pc = 66;
              tmp12.contTrace.last.next = this;
              tmp12.contTrace.last = this;
              return tmp12
            }
            this.pc = 66;
            continue contLoop;
          } else if (this.pc === 66) {
            tmp12 = runtime.resetDepth(tmp12, curDepth);
            this.pc = 108;
            continue contLoop;
          } else if (this.pc === 108) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp13 = runtime.safeCall(tmp12(...arg1));
            if (tmp13 instanceof runtime.EffectSig.class) {
              this.pc = 67;
              tmp13.contTrace.last.next = this;
              tmp13.contTrace.last = this;
              return tmp13
            }
            this.pc = 67;
            continue contLoop;
          } else if (this.pc === 67) {
            tmp13 = runtime.resetDepth(tmp13, curDepth);
            this.pc = 107;
            continue contLoop;
          } else if (this.pc === 68) {
            tmp14 = runtime.resetDepth(tmp14, curDepth);
            this.pc = 106;
            continue contLoop;
          } else if (this.pc === 105) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp5 = Predef.fold(lambda1);
            if (tmp5 instanceof runtime.EffectSig.class) {
              this.pc = 59;
              tmp5.contTrace.last.next = this;
              tmp5.contTrace.last = this;
              return tmp5
            }
            this.pc = 59;
            continue contLoop;
          } else if (this.pc === 59) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            this.pc = 104;
            continue contLoop;
          } else if (this.pc === 100) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(tmp5("Set{", ...tmp9, "}"))
          } else if (this.pc === 104) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp6 = Predef.interleave(", ");
            if (tmp6 instanceof runtime.EffectSig.class) {
              this.pc = 60;
              tmp6.contTrace.last.next = this;
              tmp6.contTrace.last = this;
              return tmp6
            }
            this.pc = 60;
            continue contLoop;
          } else if (this.pc === 60) {
            tmp6 = runtime.resetDepth(tmp6, curDepth);
            this.pc = 103;
            continue contLoop;
          } else if (this.pc === 101) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp9 = runtime.safeCall(tmp6(...tmp8));
            if (tmp9 instanceof runtime.EffectSig.class) {
              this.pc = 63;
              tmp9.contTrace.last.next = this;
              tmp9.contTrace.last = this;
              return tmp9
            }
            this.pc = 63;
            continue contLoop;
          } else if (this.pc === 103) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp7 = Predef.map(Predef.render);
            if (tmp7 instanceof runtime.EffectSig.class) {
              this.pc = 61;
              tmp7.contTrace.last.next = this;
              tmp7.contTrace.last = this;
              return tmp7
            }
            this.pc = 61;
            continue contLoop;
          } else if (this.pc === 61) {
            tmp7 = runtime.resetDepth(tmp7, curDepth);
            this.pc = 102;
            continue contLoop;
          } else if (this.pc === 102) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp8 = runtime.safeCall(tmp7(...arg1));
            if (tmp8 instanceof runtime.EffectSig.class) {
              this.pc = 62;
              tmp8.contTrace.last.next = this;
              tmp8.contTrace.last = this;
              return tmp8
            }
            this.pc = 62;
            continue contLoop;
          } else if (this.pc === 62) {
            tmp8 = runtime.resetDepth(tmp8, curDepth);
            this.pc = 101;
            continue contLoop;
          } else if (this.pc === 63) {
            tmp9 = runtime.resetDepth(tmp9, curDepth);
            this.pc = 100;
            continue contLoop;
          } else if (this.pc === 99) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(globalThis.JSON.stringify(arg1))
          } else if (this.pc === 98) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = Predef.fold(lambda);
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 54;
              tmp.contTrace.last.next = this;
              tmp.contTrace.last = this;
              return tmp
            }
            this.pc = 54;
            continue contLoop;
          } else if (this.pc === 54) {
            tmp = runtime.resetDepth(tmp, curDepth);
            this.pc = 97;
            continue contLoop;
          } else if (this.pc === 93) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(tmp("[", ...tmp4, "]"))
          } else if (this.pc === 97) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = Predef.interleave(", ");
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 55;
              tmp1.contTrace.last.next = this;
              tmp1.contTrace.last = this;
              return tmp1
            }
            this.pc = 55;
            continue contLoop;
          } else if (this.pc === 55) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            this.pc = 96;
            continue contLoop;
          } else if (this.pc === 94) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = runtime.safeCall(tmp1(...tmp3));
            if (tmp4 instanceof runtime.EffectSig.class) {
              this.pc = 58;
              tmp4.contTrace.last.next = this;
              tmp4.contTrace.last = this;
              return tmp4
            }
            this.pc = 58;
            continue contLoop;
          } else if (this.pc === 96) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = Predef.map(Predef.render);
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 56;
              tmp2.contTrace.last.next = this;
              tmp2.contTrace.last = this;
              return tmp2
            }
            this.pc = 56;
            continue contLoop;
          } else if (this.pc === 56) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            this.pc = 95;
            continue contLoop;
          } else if (this.pc === 95) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = runtime.safeCall(tmp2(...arg1));
            if (tmp3 instanceof runtime.EffectSig.class) {
              this.pc = 57;
              tmp3.contTrace.last.next = this;
              tmp3.contTrace.last = this;
              return tmp3
            }
            this.pc = 57;
            continue contLoop;
          } else if (this.pc === 57) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            this.pc = 94;
            continue contLoop;
          } else if (this.pc === 58) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            this.pc = 93;
            continue contLoop;
          }
          break;
        }
      }
      toString() { return "Cont$func$render$Predef$_mls_L0_1070_2080$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    lambda = (undefined, function (arg11, arg2) {
      return arg11 + arg2
    });
    lambda1 = (undefined, function (arg11, arg2) {
      return arg11 + arg2
    });
    lambda2 = (undefined, function (arg11, arg2) {
      return arg11 + arg2
    });
    lambda3 = (undefined, function (arg11, arg2) {
      return arg11 + arg2
    });
    lambda4 = (undefined, function (caseScrut) {
      let first1, first0, k, v, tmp35, tmp36, curDepth1, tmp37, stackDelayRes1, Cont$func$lambda$$3;
      Cont$func$lambda$$3 = function Cont$func$lambda$$(pc1) {
        return new Cont$func$lambda$$.class(pc1);
      };
      Cont$func$lambda$$3.class = class Cont$func$lambda$$ extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp38;
          tmp38 = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 73) {
            stackDelayRes1 = value$;
          } else if (this.pc === 75) {
            tmp37 = value$;
          } else if (this.pc === 74) {
            tmp36 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 73) {
              if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                first0 = caseScrut[0];
                first1 = caseScrut[1];
                k = first0;
                v = first1;
                tmp35 = k + ": ";
                this.pc = 77;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp37 = new globalThis.Error("match error");
                if (tmp37 instanceof runtime.EffectSig.class) {
                  this.pc = 75;
                  tmp37.contTrace.last.next = this;
                  tmp37.contTrace.last = this;
                  return tmp37
                }
                this.pc = 75;
                continue contLoop;
              }
              this.pc = 76;
              continue contLoop;
            } else if (this.pc === 76) {
              break contLoop;
            } else if (this.pc === 75) {
              tmp37 = runtime.resetDepth(tmp37, curDepth1);
              throw tmp37;
            } else if (this.pc === 77) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp36 = Predef.render(v);
              if (tmp36 instanceof runtime.EffectSig.class) {
                this.pc = 74;
                tmp36.contTrace.last.next = this;
                tmp36.contTrace.last = this;
                return tmp36
              }
              this.pc = 74;
              continue contLoop;
            } else if (this.pc === 74) {
              tmp36 = runtime.resetDepth(tmp36, curDepth1);
              return tmp35 + tmp36
            }
            break;
          }
        }
        toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      curDepth1 = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.contTrace.last.next = new Cont$func$lambda$$3.class(73);
        stackDelayRes1.contTrace.last = stackDelayRes1.contTrace.last.next;
        return stackDelayRes1
      }
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        k = first0;
        v = first1;
        tmp35 = k + ": ";
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp36 = Predef.render(v);
        if (tmp36 instanceof runtime.EffectSig.class) {
          tmp36.contTrace.last.next = new Cont$func$lambda$$3.class(74);
          tmp36.contTrace.last = tmp36.contTrace.last.next;
          return tmp36
        }
        tmp36 = runtime.resetDepth(tmp36, curDepth1);
        return tmp35 + tmp36
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp37 = new globalThis.Error("match error");
        if (tmp37 instanceof runtime.EffectSig.class) {
          tmp37.contTrace.last.next = new Cont$func$lambda$$3.class(75);
          tmp37.contTrace.last = tmp37.contTrace.last.next;
          return tmp37
        }
        tmp37 = runtime.resetDepth(tmp37, curDepth1);
        throw tmp37;
      }
    });
    lambda5 = (undefined, function (arg11, arg2) {
      return arg11 + arg2
    });
    lambda6 = (undefined, function (caseScrut) {
      let first1, first0, k, v, tmp35, tmp36, curDepth1, tmp37, stackDelayRes1, Cont$func$lambda$$3;
      Cont$func$lambda$$3 = function Cont$func$lambda$$(pc1) {
        return new Cont$func$lambda$$.class(pc1);
      };
      Cont$func$lambda$$3.class = class Cont$func$lambda$$1 extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp38;
          tmp38 = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 84) {
            stackDelayRes1 = value$;
          } else if (this.pc === 86) {
            tmp37 = value$;
          } else if (this.pc === 85) {
            tmp36 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 84) {
              if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                first0 = caseScrut[0];
                first1 = caseScrut[1];
                k = first0;
                v = first1;
                tmp35 = k + ": ";
                this.pc = 88;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp37 = new globalThis.Error("match error");
                if (tmp37 instanceof runtime.EffectSig.class) {
                  this.pc = 86;
                  tmp37.contTrace.last.next = this;
                  tmp37.contTrace.last = this;
                  return tmp37
                }
                this.pc = 86;
                continue contLoop;
              }
              this.pc = 87;
              continue contLoop;
            } else if (this.pc === 87) {
              break contLoop;
            } else if (this.pc === 86) {
              tmp37 = runtime.resetDepth(tmp37, curDepth1);
              throw tmp37;
            } else if (this.pc === 88) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp36 = Predef.render(v);
              if (tmp36 instanceof runtime.EffectSig.class) {
                this.pc = 85;
                tmp36.contTrace.last.next = this;
                tmp36.contTrace.last = this;
                return tmp36
              }
              this.pc = 85;
              continue contLoop;
            } else if (this.pc === 85) {
              tmp36 = runtime.resetDepth(tmp36, curDepth1);
              return tmp35 + tmp36
            }
            break;
          }
        }
        toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      curDepth1 = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.contTrace.last.next = new Cont$func$lambda$$3.class(84);
        stackDelayRes1.contTrace.last = stackDelayRes1.contTrace.last.next;
        return stackDelayRes1
      }
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        k = first0;
        v = first1;
        tmp35 = k + ": ";
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp36 = Predef.render(v);
        if (tmp36 instanceof runtime.EffectSig.class) {
          tmp36.contTrace.last.next = new Cont$func$lambda$$3.class(85);
          tmp36.contTrace.last = tmp36.contTrace.last.next;
          return tmp36
        }
        tmp36 = runtime.resetDepth(tmp36, curDepth1);
        return tmp35 + tmp36
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp37 = new globalThis.Error("match error");
        if (tmp37 instanceof runtime.EffectSig.class) {
          tmp37.contTrace.last.next = new Cont$func$lambda$$3.class(86);
          tmp37.contTrace.last = tmp37.contTrace.last.next;
          return tmp37
        }
        tmp37 = runtime.resetDepth(tmp37, curDepth1);
        throw tmp37;
      }
    });
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(53);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    if (arg1 === undefined) {
      return "undefined"
    } else if (arg1 === null) {
      return "null"
    } else if (arg1 instanceof globalThis.Array) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = Predef.fold(lambda);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(54);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = Predef.interleave(", ");
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(55);
        tmp1.contTrace.last = tmp1.contTrace.last.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = Predef.map(Predef.render);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(56);
        tmp2.contTrace.last = tmp2.contTrace.last.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = runtime.safeCall(tmp2(...arg1));
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(57);
        tmp3.contTrace.last = tmp3.contTrace.last.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = runtime.safeCall(tmp1(...tmp3));
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(58);
        tmp4.contTrace.last = tmp4.contTrace.last.next;
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
      tmp5 = Predef.fold(lambda1);
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(59);
        tmp5.contTrace.last = tmp5.contTrace.last.next;
        return tmp5
      }
      tmp5 = runtime.resetDepth(tmp5, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp6 = Predef.interleave(", ");
      if (tmp6 instanceof runtime.EffectSig.class) {
        tmp6.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(60);
        tmp6.contTrace.last = tmp6.contTrace.last.next;
        return tmp6
      }
      tmp6 = runtime.resetDepth(tmp6, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp7 = Predef.map(Predef.render);
      if (tmp7 instanceof runtime.EffectSig.class) {
        tmp7.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(61);
        tmp7.contTrace.last = tmp7.contTrace.last.next;
        return tmp7
      }
      tmp7 = runtime.resetDepth(tmp7, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp8 = runtime.safeCall(tmp7(...arg1));
      if (tmp8 instanceof runtime.EffectSig.class) {
        tmp8.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(62);
        tmp8.contTrace.last = tmp8.contTrace.last.next;
        return tmp8
      }
      tmp8 = runtime.resetDepth(tmp8, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp9 = runtime.safeCall(tmp6(...tmp8));
      if (tmp9 instanceof runtime.EffectSig.class) {
        tmp9.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(63);
        tmp9.contTrace.last = tmp9.contTrace.last.next;
        return tmp9
      }
      tmp9 = runtime.resetDepth(tmp9, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(tmp5("Set{", ...tmp9, "}"))
    } else if (arg1 instanceof globalThis.Map) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp10 = Predef.fold(lambda2);
      if (tmp10 instanceof runtime.EffectSig.class) {
        tmp10.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(64);
        tmp10.contTrace.last = tmp10.contTrace.last.next;
        return tmp10
      }
      tmp10 = runtime.resetDepth(tmp10, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp11 = Predef.interleave(", ");
      if (tmp11 instanceof runtime.EffectSig.class) {
        tmp11.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(65);
        tmp11.contTrace.last = tmp11.contTrace.last.next;
        return tmp11
      }
      tmp11 = runtime.resetDepth(tmp11, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp12 = Predef.map(Predef.render);
      if (tmp12 instanceof runtime.EffectSig.class) {
        tmp12.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(66);
        tmp12.contTrace.last = tmp12.contTrace.last.next;
        return tmp12
      }
      tmp12 = runtime.resetDepth(tmp12, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp13 = runtime.safeCall(tmp12(...arg1));
      if (tmp13 instanceof runtime.EffectSig.class) {
        tmp13.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(67);
        tmp13.contTrace.last = tmp13.contTrace.last.next;
        return tmp13
      }
      tmp13 = runtime.resetDepth(tmp13, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp14 = runtime.safeCall(tmp11(...tmp13));
      if (tmp14 instanceof runtime.EffectSig.class) {
        tmp14.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(68);
        tmp14.contTrace.last = tmp14.contTrace.last.next;
        return tmp14
      }
      tmp14 = runtime.resetDepth(tmp14, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(tmp10("Map{", ...tmp14, "}"))
    } else if (arg1 instanceof globalThis.Function) {
      runtime.stackDepth = runtime.stackDepth + 1;
      p = globalThis.Object.getOwnPropertyDescriptor(arg1, "prototype");
      if (p instanceof runtime.EffectSig.class) {
        p.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(69);
        p.contTrace.last = p.contTrace.last.next;
        return p
      }
      p = runtime.resetDepth(p, curDepth);
      if (p instanceof globalThis.Object) {
        scrut1 = p["writable"];
        if (scrut1 === true) {
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
      scrut2 = tmp15 || tmp16;
      if (scrut2 === true) {
        scrut3 = arg1.name;
        if (scrut3 === "") {
          tmp17 = "";
        } else {
          nme = scrut3;
          tmp17 = " " + nme;
        }
        tmp18 = "[function" + tmp17;
        return tmp18 + "]"
      } else {
        scrut = arg1.constructor.name;
        if (scrut === "Object") {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp19 = runtime.safeCall(globalThis.Object.entries(arg1));
          if (tmp19 instanceof runtime.EffectSig.class) {
            tmp19.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(70);
            tmp19.contTrace.last = tmp19.contTrace.last.next;
            return tmp19
          }
          tmp19 = runtime.resetDepth(tmp19, curDepth);
          es = tmp19;
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp20 = Predef.fold(lambda3);
          if (tmp20 instanceof runtime.EffectSig.class) {
            tmp20.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(71);
            tmp20.contTrace.last = tmp20.contTrace.last.next;
            return tmp20
          }
          tmp20 = runtime.resetDepth(tmp20, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp21 = Predef.interleave(", ");
          if (tmp21 instanceof runtime.EffectSig.class) {
            tmp21.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(72);
            tmp21.contTrace.last = tmp21.contTrace.last.next;
            return tmp21
          }
          tmp21 = runtime.resetDepth(tmp21, curDepth);
          tmp22 = lambda4;
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp23 = Predef.map(tmp22);
          if (tmp23 instanceof runtime.EffectSig.class) {
            tmp23.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(78);
            tmp23.contTrace.last = tmp23.contTrace.last.next;
            return tmp23
          }
          tmp23 = runtime.resetDepth(tmp23, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp24 = runtime.safeCall(tmp23(...es));
          if (tmp24 instanceof runtime.EffectSig.class) {
            tmp24.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(79);
            tmp24.contTrace.last = tmp24.contTrace.last.next;
            return tmp24
          }
          tmp24 = runtime.resetDepth(tmp24, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp25 = runtime.safeCall(tmp21(...tmp24));
          if (tmp25 instanceof runtime.EffectSig.class) {
            tmp25.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(80);
            tmp25.contTrace.last = tmp25.contTrace.last.next;
            return tmp25
          }
          tmp25 = runtime.resetDepth(tmp25, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          return runtime.safeCall(tmp20("{", ...tmp25, "}"))
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          return globalThis.String(arg1)
        }
      }
    } else if (arg1 instanceof globalThis.Object) {
      scrut = arg1.constructor.name;
      if (scrut === "Object") {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp26 = runtime.safeCall(globalThis.Object.entries(arg1));
        if (tmp26 instanceof runtime.EffectSig.class) {
          tmp26.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(81);
          tmp26.contTrace.last = tmp26.contTrace.last.next;
          return tmp26
        }
        tmp26 = runtime.resetDepth(tmp26, curDepth);
        es = tmp26;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp27 = Predef.fold(lambda5);
        if (tmp27 instanceof runtime.EffectSig.class) {
          tmp27.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(82);
          tmp27.contTrace.last = tmp27.contTrace.last.next;
          return tmp27
        }
        tmp27 = runtime.resetDepth(tmp27, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp28 = Predef.interleave(", ");
        if (tmp28 instanceof runtime.EffectSig.class) {
          tmp28.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(83);
          tmp28.contTrace.last = tmp28.contTrace.last.next;
          return tmp28
        }
        tmp28 = runtime.resetDepth(tmp28, curDepth);
        tmp29 = lambda6;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp30 = Predef.map(tmp29);
        if (tmp30 instanceof runtime.EffectSig.class) {
          tmp30.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(89);
          tmp30.contTrace.last = tmp30.contTrace.last.next;
          return tmp30
        }
        tmp30 = runtime.resetDepth(tmp30, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp31 = runtime.safeCall(tmp30(...es));
        if (tmp31 instanceof runtime.EffectSig.class) {
          tmp31.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(90);
          tmp31.contTrace.last = tmp31.contTrace.last.next;
          return tmp31
        }
        tmp31 = runtime.resetDepth(tmp31, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp32 = runtime.safeCall(tmp28(...tmp31));
        if (tmp32 instanceof runtime.EffectSig.class) {
          tmp32.contTrace.last.next = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(91);
          tmp32.contTrace.last = tmp32.contTrace.last.next;
          return tmp32
        }
        tmp32 = runtime.resetDepth(tmp32, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(tmp27("{", ...tmp32, "}"))
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        return globalThis.String(arg1)
      }
    } else {
      ts = arg1["toString"];
      if (ts === undefined) {
        tmp33 = typeof arg1;
        tmp34 = "[" + tmp33;
        return tmp34 + "]"
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(ts.call(arg1))
      }
    }
  } 
  static notImplemented(msg) {
    let tmp, tmp1, curDepth, stackDelayRes, Cont$func$notImplemented$Predef$_mls_L0_2115_2180$1;
    Cont$func$notImplemented$Predef$_mls_L0_2115_2180$1 = function Cont$func$notImplemented$Predef$_mls_L0_2115_2180$(pc1) {
      return new Cont$func$notImplemented$Predef$_mls_L0_2115_2180$.class(pc1);
    };
    Cont$func$notImplemented$Predef$_mls_L0_2115_2180$1.class = class Cont$func$notImplemented$Predef$_mls_L0_2115_2180$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp2;
        tmp2 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 133) {
          stackDelayRes = value$;
        } else if (this.pc === 134) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 133) {
            tmp = "Not implemented: " + msg;
            this.pc = 135;
            continue contLoop;
          } else if (this.pc === 135) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = globalThis.Error(tmp);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 134;
              tmp1.contTrace.last.next = this;
              tmp1.contTrace.last = this;
              return tmp1
            }
            this.pc = 134;
            continue contLoop;
          } else if (this.pc === 134) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            throw tmp1;
          }
          break;
        }
      }
      toString() { return "Cont$func$notImplemented$Predef$_mls_L0_2115_2180$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$notImplemented$Predef$_mls_L0_2115_2180$1.class(133);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    tmp = "Not implemented: " + msg;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = globalThis.Error(tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = new Cont$func$notImplemented$Predef$_mls_L0_2115_2180$1.class(134);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    throw tmp1;
  } 
  static get notImplementedError() {
    let tmp, curDepth, stackDelayRes, Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$1;
    Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$1 = function Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$(pc1) {
      return new Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$.class(pc1);
    };
    Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$1.class = class Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp1;
        tmp1 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 136) {
          stackDelayRes = value$;
        } else if (this.pc === 137) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 136) {
            this.pc = 138;
            continue contLoop;
          } else if (this.pc === 138) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = globalThis.Error("Not implemented");
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 137;
              tmp.contTrace.last.next = this;
              tmp.contTrace.last = this;
              return tmp
            }
            this.pc = 137;
            continue contLoop;
          } else if (this.pc === 137) {
            tmp = runtime.resetDepth(tmp, curDepth);
            throw tmp;
          }
          break;
        }
      }
      toString() { return "Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$1.class(136);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = globalThis.Error("Not implemented");
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = new Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$1.class(137);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    throw tmp;
  } 
  static tuple(...xs1) {
    return xs1
  } 
  static tupleSlice(xs2, i, j) {
    let tmp, stackDelayRes, Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$1;
    Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$1 = function Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$(pc1) {
      return new Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$.class(pc1);
    };
    Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$1.class = class Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp1;
        tmp1 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 139) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 139) {
            tmp = xs2.length - j;
            this.pc = 140;
            continue contLoop;
          } else if (this.pc === 140) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(globalThis.Array.prototype.slice.call(xs2, i, tmp))
          }
          break;
        }
      }
      toString() { return "Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$1.class(139);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    tmp = xs2.length - j;
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(globalThis.Array.prototype.slice.call(xs2, i, tmp))
  } 
  static tupleGet(xs3, i1) {
    let stackDelayRes, Cont$func$tupleGet$Predef$_mls_L0_2481_2617$1;
    Cont$func$tupleGet$Predef$_mls_L0_2481_2617$1 = function Cont$func$tupleGet$Predef$_mls_L0_2481_2617$(pc1) {
      return new Cont$func$tupleGet$Predef$_mls_L0_2481_2617$.class(pc1);
    };
    Cont$func$tupleGet$Predef$_mls_L0_2481_2617$1.class = class Cont$func$tupleGet$Predef$_mls_L0_2481_2617$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp;
        tmp = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 141) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 141) {
            this.pc = 142;
            continue contLoop;
          } else if (this.pc === 142) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return globalThis.Array.prototype.at.call(xs3, i1)
          }
          break;
        }
      }
      toString() { return "Cont$func$tupleGet$Predef$_mls_L0_2481_2617$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$tupleGet$Predef$_mls_L0_2481_2617$1.class(141);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return globalThis.Array.prototype.at.call(xs3, i1)
  } 
  static map(f13) {
    return (...xs4) => {
      let tmp, curDepth, stackDelayRes, Cont$func$map$Predef$_mls_L0_2623_2655$1;
      Cont$func$map$Predef$_mls_L0_2623_2655$1 = function Cont$func$map$Predef$_mls_L0_2623_2655$(pc1) {
        return new Cont$func$map$Predef$_mls_L0_2623_2655$.class(pc1);
      };
      Cont$func$map$Predef$_mls_L0_2623_2655$1.class = class Cont$func$map$Predef$_mls_L0_2623_2655$ extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp1;
          tmp1 = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 143) {
            stackDelayRes = value$;
          } else if (this.pc === 144) {
            tmp = value$;
          }
          contLoop: while (true) {
            if (this.pc === 143) {
              this.pc = 146;
              continue contLoop;
            } else if (this.pc === 145) {
              runtime.stackDepth = runtime.stackDepth + 1;
              return runtime.safeCall(xs4.map(tmp))
            } else if (this.pc === 146) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = Predef.pass1(f13);
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 144;
                tmp.contTrace.last.next = this;
                tmp.contTrace.last = this;
                return tmp
              }
              this.pc = 144;
              continue contLoop;
            } else if (this.pc === 144) {
              tmp = runtime.resetDepth(tmp, curDepth);
              this.pc = 145;
              continue contLoop;
            }
            break;
          }
        }
        toString() { return "Cont$func$map$Predef$_mls_L0_2623_2655$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = new Cont$func$map$Predef$_mls_L0_2623_2655$1.class(143);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = Predef.pass1(f13);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = new Cont$func$map$Predef$_mls_L0_2623_2655$1.class(144);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(xs4.map(tmp))
    }
  } 
  static fold(f14) {
    return (init, ...rest) => {
      let i2, len, scrut, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, Cont$func$fold$Predef$_mls_L0_2661_2803$1;
      Cont$func$fold$Predef$_mls_L0_2661_2803$1 = function Cont$func$fold$Predef$_mls_L0_2661_2803$(pc1) {
        return new Cont$func$fold$Predef$_mls_L0_2661_2803$.class(pc1);
      };
      Cont$func$fold$Predef$_mls_L0_2661_2803$1.class = class Cont$func$fold$Predef$_mls_L0_2661_2803$ extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp4;
          tmp4 = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 147) {
            stackDelayRes = value$;
          } else if (this.pc === 148) {
            tmp = value$;
          } else if (this.pc === 149) {
            tmp1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 147) {
              i2 = 0;
              len = rest.length;
              this.pc = 151;
              continue contLoop;
            } else if (this.pc === 150) {
              return init
            } else if (this.pc === 151) {
              scrut = i2 < len;
              if (scrut === true) {
                this.pc = 153;
                continue contLoop;
              } else {
                tmp3 = runtime.Unit;
                this.pc = 150;
                continue contLoop;
              }
              this.pc = 150;
              continue contLoop;
            } else if (this.pc === 152) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = runtime.safeCall(f14(init, tmp));
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 149;
                tmp1.contTrace.last.next = this;
                tmp1.contTrace.last = this;
                return tmp1
              }
              this.pc = 149;
              continue contLoop;
            } else if (this.pc === 153) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = runtime.safeCall(rest.at(i2));
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 148;
                tmp.contTrace.last.next = this;
                tmp.contTrace.last = this;
                return tmp
              }
              this.pc = 148;
              continue contLoop;
            } else if (this.pc === 148) {
              tmp = runtime.resetDepth(tmp, curDepth);
              this.pc = 152;
              continue contLoop;
            } else if (this.pc === 149) {
              tmp1 = runtime.resetDepth(tmp1, curDepth);
              init = tmp1;
              tmp2 = i2 + 1;
              i2 = tmp2;
              tmp3 = runtime.Unit;
              this.pc = 151;
              continue contLoop;
            }
            break;
          }
        }
        toString() { return "Cont$func$fold$Predef$_mls_L0_2661_2803$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = new Cont$func$fold$Predef$_mls_L0_2661_2803$1.class(147);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
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
            tmp.contTrace.last.next = new Cont$func$fold$Predef$_mls_L0_2661_2803$1.class(148);
            tmp.contTrace.last = tmp.contTrace.last.next;
            return tmp
          }
          tmp = runtime.resetDepth(tmp, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp1 = runtime.safeCall(f14(init, tmp));
          if (tmp1 instanceof runtime.EffectSig.class) {
            tmp1.contTrace.last.next = new Cont$func$fold$Predef$_mls_L0_2661_2803$1.class(149);
            tmp1.contTrace.last = tmp1.contTrace.last.next;
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
  static foldr(f15) {
    return (first, ...rest) => {
      let len, i2, init, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, Cont$func$foldr$Predef$_mls_L0_2886_3101$1;
      Cont$func$foldr$Predef$_mls_L0_2886_3101$1 = function Cont$func$foldr$Predef$_mls_L0_2886_3101$(pc1) {
        return new Cont$func$foldr$Predef$_mls_L0_2886_3101$.class(pc1);
      };
      Cont$func$foldr$Predef$_mls_L0_2886_3101$1.class = class Cont$func$foldr$Predef$_mls_L0_2886_3101$ extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp6;
          tmp6 = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 154) {
            stackDelayRes = value$;
          } else if (this.pc === 155) {
            tmp1 = value$;
          } else if (this.pc === 156) {
            tmp3 = value$;
          } else if (this.pc === 157) {
            tmp4 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 154) {
              len = rest.length;
              scrut1 = len == 0;
              if (scrut1 === true) {
                return first
              } else {
                tmp = len - 1;
                i2 = tmp;
                this.pc = 163;
                continue contLoop;
              }
              this.pc = 158;
              continue contLoop;
            } else if (this.pc === 158) {
              break contLoop;
            } else if (this.pc === 163) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = runtime.safeCall(rest.at(i2));
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 155;
                tmp1.contTrace.last.next = this;
                tmp1.contTrace.last = this;
                return tmp1
              }
              this.pc = 155;
              continue contLoop;
            } else if (this.pc === 155) {
              tmp1 = runtime.resetDepth(tmp1, curDepth);
              init = tmp1;
              this.pc = 160;
              continue contLoop;
            } else if (this.pc === 160) {
              scrut = i2 > 0;
              if (scrut === true) {
                tmp2 = i2 - 1;
                i2 = tmp2;
                this.pc = 162;
                continue contLoop;
              } else {
                tmp5 = runtime.Unit;
                this.pc = 159;
                continue contLoop;
              }
              this.pc = 159;
              continue contLoop;
            } else if (this.pc === 161) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp4 = runtime.safeCall(f15(tmp3, init));
              if (tmp4 instanceof runtime.EffectSig.class) {
                this.pc = 157;
                tmp4.contTrace.last.next = this;
                tmp4.contTrace.last = this;
                return tmp4
              }
              this.pc = 157;
              continue contLoop;
            } else if (this.pc === 162) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp3 = runtime.safeCall(rest.at(i2));
              if (tmp3 instanceof runtime.EffectSig.class) {
                this.pc = 156;
                tmp3.contTrace.last.next = this;
                tmp3.contTrace.last = this;
                return tmp3
              }
              this.pc = 156;
              continue contLoop;
            } else if (this.pc === 156) {
              tmp3 = runtime.resetDepth(tmp3, curDepth);
              this.pc = 161;
              continue contLoop;
            } else if (this.pc === 157) {
              tmp4 = runtime.resetDepth(tmp4, curDepth);
              init = tmp4;
              tmp5 = runtime.Unit;
              this.pc = 160;
              continue contLoop;
            } else if (this.pc === 159) {
              runtime.stackDepth = runtime.stackDepth + 1;
              return runtime.safeCall(f15(first, init))
            }
            break;
          }
        }
        toString() { return "Cont$func$foldr$Predef$_mls_L0_2886_3101$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = new Cont$func$foldr$Predef$_mls_L0_2886_3101$1.class(154);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
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
          tmp1.contTrace.last.next = new Cont$func$foldr$Predef$_mls_L0_2886_3101$1.class(155);
          tmp1.contTrace.last = tmp1.contTrace.last.next;
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
              tmp3.contTrace.last.next = new Cont$func$foldr$Predef$_mls_L0_2886_3101$1.class(156);
              tmp3.contTrace.last = tmp3.contTrace.last.next;
              return tmp3
            }
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = runtime.safeCall(f15(tmp3, init));
            if (tmp4 instanceof runtime.EffectSig.class) {
              tmp4.contTrace.last.next = new Cont$func$foldr$Predef$_mls_L0_2886_3101$1.class(157);
              tmp4.contTrace.last = tmp4.contTrace.last.next;
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
        return runtime.safeCall(f15(first, init))
      }
    }
  } 
  static mkStr(...xs4) {
    let tmp, tmp1, lambda, curDepth, stackDelayRes, Cont$func$mkStr$Predef$_mls_L0_3107_3176$1;
    Cont$func$mkStr$Predef$_mls_L0_3107_3176$1 = function Cont$func$mkStr$Predef$_mls_L0_3107_3176$(pc1) {
      return new Cont$func$mkStr$Predef$_mls_L0_3107_3176$.class(pc1);
    };
    Cont$func$mkStr$Predef$_mls_L0_3107_3176$1.class = class Cont$func$mkStr$Predef$_mls_L0_3107_3176$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp2;
        tmp2 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 164) {
          stackDelayRes = value$;
        } else if (this.pc === 168) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 164) {
            tmp = lambda;
            this.pc = 170;
            continue contLoop;
          } else if (this.pc === 170) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = Predef.fold(tmp);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 168;
              tmp1.contTrace.last.next = this;
              tmp1.contTrace.last = this;
              return tmp1
            }
            this.pc = 168;
            continue contLoop;
          } else if (this.pc === 168) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            this.pc = 169;
            continue contLoop;
          } else if (this.pc === 169) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(tmp1(...xs4))
          }
          break;
        }
      }
      toString() { return "Cont$func$mkStr$Predef$_mls_L0_3107_3176$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    lambda = (undefined, function (acc, x7) {
      let tmp2, tmp3, tmp4, curDepth1, stackDelayRes1, Cont$func$lambda$$3;
      Cont$func$lambda$$3 = function Cont$func$lambda$$(pc1) {
        return new Cont$func$lambda$$.class(pc1);
      };
      Cont$func$lambda$$3.class = class Cont$func$lambda$$2 extends runtime.FunctionContFrame.class {
        constructor(pc) {
          let tmp5;
          tmp5 = super(null);
          this.pc = pc;
        }
        resume(value$) {
          if (this.pc === 165) {
            stackDelayRes1 = value$;
          } else if (this.pc === 166) {
            tmp3 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 165) {
              if (typeof x7 === 'string') {
                tmp2 = true;
                this.pc = 167;
                continue contLoop;
              } else {
                tmp2 = false;
                this.pc = 167;
                continue contLoop;
              }
              this.pc = 167;
              continue contLoop;
            } else if (this.pc === 167) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp3 = runtime.safeCall(Predef.assert(tmp2));
              if (tmp3 instanceof runtime.EffectSig.class) {
                this.pc = 166;
                tmp3.contTrace.last.next = this;
                tmp3.contTrace.last = this;
                return tmp3
              }
              this.pc = 166;
              continue contLoop;
            } else if (this.pc === 166) {
              tmp3 = runtime.resetDepth(tmp3, curDepth1);
              tmp4 = acc + x7;
              return (tmp3 , tmp4)
            }
            break;
          }
        }
        toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
      };
      curDepth1 = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.contTrace.last.next = new Cont$func$lambda$$3.class(165);
        stackDelayRes1.contTrace.last = stackDelayRes1.contTrace.last.next;
        return stackDelayRes1
      }
      if (typeof x7 === 'string') {
        tmp2 = true;
      } else {
        tmp2 = false;
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = runtime.safeCall(Predef.assert(tmp2));
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.contTrace.last.next = new Cont$func$lambda$$3.class(166);
        tmp3.contTrace.last = tmp3.contTrace.last.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth1);
      tmp4 = acc + x7;
      return (tmp3 , tmp4)
    });
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$mkStr$Predef$_mls_L0_3107_3176$1.class(164);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    tmp = lambda;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = Predef.fold(tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = new Cont$func$mkStr$Predef$_mls_L0_3107_3176$1.class(168);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(tmp1(...xs4))
  } 
  static stringStartsWith(string, prefix) {
    let stackDelayRes, Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$1;
    Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$1 = function Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$(pc1) {
      return new Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$.class(pc1);
    };
    Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$1.class = class Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp;
        tmp = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 171) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 171) {
            this.pc = 172;
            continue contLoop;
          } else if (this.pc === 172) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(string.startsWith(prefix))
          }
          break;
        }
      }
      toString() { return "Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$1.class(171);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(string.startsWith(prefix))
  } 
  static stringGet(string1, i2) {
    let stackDelayRes, Cont$func$stringGet$Predef$_mls_L0_3249_3284$1;
    Cont$func$stringGet$Predef$_mls_L0_3249_3284$1 = function Cont$func$stringGet$Predef$_mls_L0_3249_3284$(pc1) {
      return new Cont$func$stringGet$Predef$_mls_L0_3249_3284$.class(pc1);
    };
    Cont$func$stringGet$Predef$_mls_L0_3249_3284$1.class = class Cont$func$stringGet$Predef$_mls_L0_3249_3284$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp;
        tmp = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 173) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 173) {
            this.pc = 174;
            continue contLoop;
          } else if (this.pc === 174) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(string1.at(i2))
          }
          break;
        }
      }
      toString() { return "Cont$func$stringGet$Predef$_mls_L0_3249_3284$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$stringGet$Predef$_mls_L0_3249_3284$1.class(173);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(string1.at(i2))
  } 
  static stringDrop(string2, n) {
    let stackDelayRes, Cont$func$stringDrop$Predef$_mls_L0_3290_3329$1;
    Cont$func$stringDrop$Predef$_mls_L0_3290_3329$1 = function Cont$func$stringDrop$Predef$_mls_L0_3290_3329$(pc1) {
      return new Cont$func$stringDrop$Predef$_mls_L0_3290_3329$.class(pc1);
    };
    Cont$func$stringDrop$Predef$_mls_L0_3290_3329$1.class = class Cont$func$stringDrop$Predef$_mls_L0_3290_3329$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp;
        tmp = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 175) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 175) {
            this.pc = 176;
            continue contLoop;
          } else if (this.pc === 176) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return runtime.safeCall(string2.slice(n))
          }
          break;
        }
      }
      toString() { return "Cont$func$stringDrop$Predef$_mls_L0_3290_3329$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$stringDrop$Predef$_mls_L0_3290_3329$1.class(175);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(string2.slice(n))
  } 
  static get unreachable() {
    let tmp, curDepth, stackDelayRes, Cont$func$unreachable$Predef$_mls_L0_3336_3376$1;
    Cont$func$unreachable$Predef$_mls_L0_3336_3376$1 = function Cont$func$unreachable$Predef$_mls_L0_3336_3376$(pc1) {
      return new Cont$func$unreachable$Predef$_mls_L0_3336_3376$.class(pc1);
    };
    Cont$func$unreachable$Predef$_mls_L0_3336_3376$1.class = class Cont$func$unreachable$Predef$_mls_L0_3336_3376$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp1;
        tmp1 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 177) {
          stackDelayRes = value$;
        } else if (this.pc === 178) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 177) {
            this.pc = 179;
            continue contLoop;
          } else if (this.pc === 179) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = globalThis.Error("unreachable");
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 178;
              tmp.contTrace.last.next = this;
              tmp.contTrace.last = this;
              return tmp
            }
            this.pc = 178;
            continue contLoop;
          } else if (this.pc === 178) {
            tmp = runtime.resetDepth(tmp, curDepth);
            throw tmp;
          }
          break;
        }
      }
      toString() { return "Cont$func$unreachable$Predef$_mls_L0_3336_3376$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$unreachable$Predef$_mls_L0_3336_3376$1.class(177);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = globalThis.Error("unreachable");
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = new Cont$func$unreachable$Predef$_mls_L0_3336_3376$1.class(178);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    throw tmp;
  } 
  static checkArgs(functionName, expected, isUB, got) {
    let scrut, name, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, lambda, curDepth, tmp9, stackDelayRes, Cont$func$checkArgs$Predef$_mls_L0_3382_3927$1;
    Cont$func$checkArgs$Predef$_mls_L0_3382_3927$1 = function Cont$func$checkArgs$Predef$_mls_L0_3382_3927$(pc1) {
      return new Cont$func$checkArgs$Predef$_mls_L0_3382_3927$.class(pc1);
    };
    Cont$func$checkArgs$Predef$_mls_L0_3382_3927$1.class = class Cont$func$checkArgs$Predef$_mls_L0_3382_3927$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp10;
        tmp10 = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 180) {
          stackDelayRes = value$;
        } else if (this.pc === 181) {
          tmp5 = value$;
        } else if (this.pc === 182) {
          tmp8 = value$;
        } else if (this.pc === 183) {
          tmp9 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 180) {
            tmp = got < expected;
            tmp1 = got > expected;
            tmp2 = isUB && tmp1;
            scrut = tmp || tmp2;
            if (scrut === true) {
              scrut1 = functionName.length > 0;
              if (scrut1 === true) {
                tmp3 = " '" + functionName;
                tmp4 = tmp3 + "'";
                this.pc = 189;
                continue contLoop;
              } else {
                tmp4 = "";
                this.pc = 189;
                continue contLoop;
              }
              this.pc = 189;
              continue contLoop;
            } else {
              return runtime.Unit
            }
            this.pc = 184;
            continue contLoop;
          } else if (this.pc === 184) {
            break contLoop;
          } else if (this.pc === 189) {
            name = tmp4;
            this.pc = 188;
            continue contLoop;
          } else if (this.pc === 185) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp9 = globalThis.Error(tmp8);
            if (tmp9 instanceof runtime.EffectSig.class) {
              this.pc = 183;
              tmp9.contTrace.last.next = this;
              tmp9.contTrace.last = this;
              return tmp9
            }
            this.pc = 183;
            continue contLoop;
          } else if (this.pc === 188) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp5 = Predef.fold(lambda);
            if (tmp5 instanceof runtime.EffectSig.class) {
              this.pc = 181;
              tmp5.contTrace.last.next = this;
              tmp5.contTrace.last = this;
              return tmp5
            }
            this.pc = 181;
            continue contLoop;
          } else if (this.pc === 181) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            if (isUB === true) {
              tmp6 = "";
              this.pc = 187;
              continue contLoop;
            } else {
              tmp6 = "at least ";
              this.pc = 187;
              continue contLoop;
            }
            this.pc = 187;
            continue contLoop;
          } else if (this.pc === 186) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp8 = runtime.safeCall(tmp5("Function", name, " expected ", tmp6, expected, " argument", tmp7, " but got ", got));
            if (tmp8 instanceof runtime.EffectSig.class) {
              this.pc = 182;
              tmp8.contTrace.last.next = this;
              tmp8.contTrace.last = this;
              return tmp8
            }
            this.pc = 182;
            continue contLoop;
          } else if (this.pc === 187) {
            scrut2 = expected === 1;
            if (scrut2 === true) {
              tmp7 = "";
              this.pc = 186;
              continue contLoop;
            } else {
              tmp7 = "s";
              this.pc = 186;
              continue contLoop;
            }
            this.pc = 186;
            continue contLoop;
          } else if (this.pc === 182) {
            tmp8 = runtime.resetDepth(tmp8, curDepth);
            this.pc = 185;
            continue contLoop;
          } else if (this.pc === 183) {
            tmp9 = runtime.resetDepth(tmp9, curDepth);
            throw tmp9;
          }
          break;
        }
      }
      toString() { return "Cont$func$checkArgs$Predef$_mls_L0_3382_3927$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    lambda = (undefined, function (arg11, arg2) {
      return arg11 + arg2
    });
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$checkArgs$Predef$_mls_L0_3382_3927$1.class(180);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
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
      tmp5 = Predef.fold(lambda);
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.contTrace.last.next = new Cont$func$checkArgs$Predef$_mls_L0_3382_3927$1.class(181);
        tmp5.contTrace.last = tmp5.contTrace.last.next;
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
        tmp8.contTrace.last.next = new Cont$func$checkArgs$Predef$_mls_L0_3382_3927$1.class(182);
        tmp8.contTrace.last = tmp8.contTrace.last.next;
        return tmp8
      }
      tmp8 = runtime.resetDepth(tmp8, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp9 = globalThis.Error(tmp8);
      if (tmp9 instanceof runtime.EffectSig.class) {
        tmp9.contTrace.last.next = new Cont$func$checkArgs$Predef$_mls_L0_3382_3927$1.class(183);
        tmp9.contTrace.last = tmp9.contTrace.last.next;
        return tmp9
      }
      tmp9 = runtime.resetDepth(tmp9, curDepth);
      throw tmp9;
    } else {
      return runtime.Unit
    }
  } 
  static enterHandleBlock(handler, body) {
    let stackDelayRes, Cont$func$enterHandleBlock$Predef$_mls_L0_4483_4751$1;
    Cont$func$enterHandleBlock$Predef$_mls_L0_4483_4751$1 = function Cont$func$enterHandleBlock$Predef$_mls_L0_4483_4751$(pc1) {
      return new Cont$func$enterHandleBlock$Predef$_mls_L0_4483_4751$.class(pc1);
    };
    Cont$func$enterHandleBlock$Predef$_mls_L0_4483_4751$1.class = class Cont$func$enterHandleBlock$Predef$_mls_L0_4483_4751$ extends runtime.FunctionContFrame.class {
      constructor(pc) {
        let tmp;
        tmp = super(null);
        this.pc = pc;
      }
      resume(value$) {
        if (this.pc === 190) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 190) {
            this.pc = 191;
            continue contLoop;
          } else if (this.pc === 191) {
            runtime.stackDepth = runtime.stackDepth + 1;
            return Runtime.enterHandleBlock(handler, body)
          }
          break;
        }
      }
      toString() { return "Cont$func$enterHandleBlock$Predef$_mls_L0_4483_4751$(" + globalThis.Predef.render(this.pc) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = new Cont$func$enterHandleBlock$Predef$_mls_L0_4483_4751$1.class(190);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return Runtime.enterHandleBlock(handler, body)
  }
  static toString() { return "Predef"; }
};
let Predef = Predef1; export default Predef;
