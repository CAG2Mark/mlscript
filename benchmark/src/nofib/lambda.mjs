import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./NofibPrelude.mjs";
let lambda1;
lambda1 = class lambda {
  static #myGet;
  static #incr;
  static #lfxx;
  static #fix;
  static #nMinus1;
  static #partialSum0;
  static #sum0;
  static {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, res, handleBlock$, handleBlock$1, handleBlock$2, handleBlock$3, handleBlock$4, handleBlock$5, handleBlock$6, handleBlock$7, handleBlock$8, handleBlock$9, handleBlock$10, handleBlock$11, handleBlock$12, handleBlock$13, handleBlock$14, handleBlock$15, handleBlock$16, handleBlock$17, handleBlock$18, handleBlock$19, handleBlock$20, handleBlock$21, handleBlock$22, handleBlock$23, handleBlock$24, handleBlock$25, handleBlock$26, handleBlock$27, handleBlock$28, handleBlock$29, handleBlock$30, handleBlock$31, handleBlock$32, handleBlock$33, handleBlock$34, handleBlock$35, handleBlock$36;
    this.MyState = function MyState(r1) { return new MyState.class(r1); };
    this.MyState.class = class MyState {
      constructor(r) {
        this.r = r;
      }
      toString() { return "MyState(" + globalThis.Predef.render(this.r) + ")"; }
    };
    handleBlock$36 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$ extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$ extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 384) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 384) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 385;
                    continue contLoop;
                  } else if (this.pc === 385) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(384, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 382) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 382) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 383;
              continue contLoop;
            } else if (this.pc === 383) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.MyState((s) => {
        return [
          s,
          s
        ]
      });
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(382, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp = handleBlock$36();
    if (tmp instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    lambda.#myGet = tmp;
    this.Term = class Term {
      constructor() {}
      toString() { return "Term"; }
    };
    const Incr$class = class Incr extends lambda.Term {
      constructor() {
        super();
      }
      toString() { return "Incr"; }
    };
    this.Incr = new Incr$class;
    this.Incr.class = Incr$class;
    this.Var = function Var(s1) { return new Var.class(s1); };
    this.Var.class = class Var extends lambda.Term {
      constructor(s) {
        super();
        this.s = s;
      }
      toString() { return "Var(" + globalThis.Predef.render(this.s) + ")"; }
    };
    this.Con = function Con(i1) { return new Con.class(i1); };
    this.Con.class = class Con extends lambda.Term {
      constructor(i) {
        super();
        this.i = i;
      }
      toString() { return "Con(" + globalThis.Predef.render(this.i) + ")"; }
    };
    this.Add = function Add(a1, b1) { return new Add.class(a1, b1); };
    this.Add.class = class Add extends lambda.Term {
      constructor(a, b) {
        super();
        this.a = a;
        this.b = b;
      }
      toString() { return "Add(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    this.Lam = function Lam(s1, t1) { return new Lam.class(s1, t1); };
    this.Lam.class = class Lam extends lambda.Term {
      constructor(s, t) {
        super();
        this.s = s;
        this.t = t;
      }
      toString() { return "Lam(" + globalThis.Predef.render(this.s) + ", " + globalThis.Predef.render(this.t) + ")"; }
    };
    this.App = function App(a1, b1) { return new App.class(a1, b1); };
    this.App.class = class App extends lambda.Term {
      constructor(a, b) {
        super();
        this.a = a;
        this.b = b;
      }
      toString() { return "App(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    this.IfZero = function IfZero(a1, b1, c1) { return new IfZero.class(a1, b1, c1); };
    this.IfZero.class = class IfZero extends lambda.Term {
      constructor(a, b, c) {
        super();
        this.a = a;
        this.b = b;
        this.c = c;
      }
      toString() { return "IfZero(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.c) + ")"; }
    };
    this.Thunk = function Thunk(t1, e1) { return new Thunk.class(t1, e1); };
    this.Thunk.class = class Thunk extends lambda.Term {
      constructor(t, e) {
        super();
        this.t = t;
        this.e = e;
      }
      toString() { return "Thunk(" + globalThis.Predef.render(this.t) + ", " + globalThis.Predef.render(this.e) + ")"; }
    };
    const Unit$class = class Unit {
      constructor() {}
      toString() { return "Unit"; }
    };
    this.Unit = new Unit$class;
    this.Unit.class = Unit$class;
    handleBlock$35 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$1 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$1 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 379) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 379) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 380;
                    continue contLoop;
                  } else if (this.pc === 380) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(379, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$1 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 377) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 377) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 378;
              continue contLoop;
            } else if (this.pc === 378) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.myReturn(lambda.Unit);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(377, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp1 = handleBlock$35();
    if (tmp1 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    lambda.#incr = tmp1;
    handleBlock$34 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$2 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$2 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 374) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 374) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 375;
                    continue contLoop;
                  } else if (this.pc === 375) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(374, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$2 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 372) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 372) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 373;
              continue contLoop;
            } else if (this.pc === 373) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = NofibPrelude.nofibStringToList("x");
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(372, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp2 = handleBlock$34();
    if (tmp2 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$33 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$3 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$3 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 369) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 369) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 370;
                    continue contLoop;
                  } else if (this.pc === 370) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(369, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$3 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 367) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 367) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 368;
              continue contLoop;
            } else if (this.pc === 368) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = NofibPrelude.nofibStringToList("F");
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(367, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp3 = handleBlock$33();
    if (tmp3 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$32 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$4 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$4 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 364) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 364) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 365;
                    continue contLoop;
                  } else if (this.pc === 365) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(364, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$4 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 362) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 362) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 363;
              continue contLoop;
            } else if (this.pc === 363) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Var(tmp3);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(362, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp4 = handleBlock$32();
    if (tmp4 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$31 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$5 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$5 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 359) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 359) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 360;
                    continue contLoop;
                  } else if (this.pc === 360) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(359, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$5 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 357) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 357) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 358;
              continue contLoop;
            } else if (this.pc === 358) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = NofibPrelude.nofibStringToList("x");
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(357, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp5 = handleBlock$31();
    if (tmp5 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$30 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$6 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$6 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 354) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 354) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 355;
                    continue contLoop;
                  } else if (this.pc === 355) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(354, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$6 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 352) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 352) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 353;
              continue contLoop;
            } else if (this.pc === 353) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Var(tmp5);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(352, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp6 = handleBlock$30();
    if (tmp6 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$29 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$7 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$7 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 349) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 349) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 350;
                    continue contLoop;
                  } else if (this.pc === 350) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(349, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$7 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 347) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 347) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 348;
              continue contLoop;
            } else if (this.pc === 348) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = NofibPrelude.nofibStringToList("x");
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(347, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp7 = handleBlock$29();
    if (tmp7 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$28 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$8 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$8 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 344) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 344) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 345;
                    continue contLoop;
                  } else if (this.pc === 345) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(344, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$8 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 342) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 342) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 343;
              continue contLoop;
            } else if (this.pc === 343) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Var(tmp7);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(342, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp8 = handleBlock$28();
    if (tmp8 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$27 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$9 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$9 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 339) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 339) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 340;
                    continue contLoop;
                  } else if (this.pc === 340) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(339, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$9 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 337) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 337) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 338;
              continue contLoop;
            } else if (this.pc === 338) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.App(tmp6, tmp8);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(337, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp9 = handleBlock$27();
    if (tmp9 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$26 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$10 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$10 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 334) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 334) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 335;
                    continue contLoop;
                  } else if (this.pc === 335) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(334, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$10 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 332) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 332) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 333;
              continue contLoop;
            } else if (this.pc === 333) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.App(tmp4, tmp9);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(332, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp10 = handleBlock$26();
    if (tmp10 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$25 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$11 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$11 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 329) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 329) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 330;
                    continue contLoop;
                  } else if (this.pc === 330) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(329, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$11 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 327) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 327) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 328;
              continue contLoop;
            } else if (this.pc === 328) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Lam(tmp2, tmp10);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(327, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp11 = handleBlock$25();
    if (tmp11 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    lambda.#lfxx = tmp11;
    handleBlock$24 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$12 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$12 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 324) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 324) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 325;
                    continue contLoop;
                  } else if (this.pc === 325) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(324, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$12 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 322) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 322) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 323;
              continue contLoop;
            } else if (this.pc === 323) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = NofibPrelude.nofibStringToList("F");
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(322, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp12 = handleBlock$24();
    if (tmp12 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$23 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$13 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$13 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 319) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 319) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 320;
                    continue contLoop;
                  } else if (this.pc === 320) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(319, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$13 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 317) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 317) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 318;
              continue contLoop;
            } else if (this.pc === 318) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.App(lambda.#lfxx, lambda.#lfxx);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(317, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp13 = handleBlock$23();
    if (tmp13 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$22 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$14 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$14 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 314) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 314) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 315;
                    continue contLoop;
                  } else if (this.pc === 315) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(314, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$14 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 312) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 312) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 313;
              continue contLoop;
            } else if (this.pc === 313) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Lam(tmp12, tmp13);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(312, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp14 = handleBlock$22();
    if (tmp14 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    lambda.#fix = tmp14;
    handleBlock$21 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$15 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$15 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 309) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 309) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 310;
                    continue contLoop;
                  } else if (this.pc === 310) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(309, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$15 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 307) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 307) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 308;
              continue contLoop;
            } else if (this.pc === 308) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = NofibPrelude.nofibStringToList("n");
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(307, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp15 = handleBlock$21();
    if (tmp15 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$20 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$16 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$16 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 304) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 304) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 305;
                    continue contLoop;
                  } else if (this.pc === 305) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(304, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$16 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 302) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 302) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 303;
              continue contLoop;
            } else if (this.pc === 303) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Var(tmp15);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(302, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp16 = handleBlock$20();
    if (tmp16 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    tmp17 = - 1;
    handleBlock$19 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$17 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$17 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 299) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 299) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 300;
                    continue contLoop;
                  } else if (this.pc === 300) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(299, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$17 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 297) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 297) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 298;
              continue contLoop;
            } else if (this.pc === 298) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Con(tmp17);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(297, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp18 = handleBlock$19();
    if (tmp18 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$18 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$18 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$18 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 294) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 294) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 295;
                    continue contLoop;
                  } else if (this.pc === 295) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(294, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$18 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 292) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 292) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 293;
              continue contLoop;
            } else if (this.pc === 293) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Add(tmp16, tmp18);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(292, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp19 = handleBlock$18();
    if (tmp19 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    lambda.#nMinus1 = tmp19;
    handleBlock$17 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$19 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$19 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 289) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 289) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 290;
                    continue contLoop;
                  } else if (this.pc === 290) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(289, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$19 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 287) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 287) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 288;
              continue contLoop;
            } else if (this.pc === 288) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = NofibPrelude.nofibStringToList("sum");
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(287, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp20 = handleBlock$17();
    if (tmp20 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$16 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$20 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$20 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 284) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 284) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 285;
                    continue contLoop;
                  } else if (this.pc === 285) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(284, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$20 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 282) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 282) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 283;
              continue contLoop;
            } else if (this.pc === 283) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = NofibPrelude.nofibStringToList("n");
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(282, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp21 = handleBlock$16();
    if (tmp21 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$15 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$21 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$21 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 279) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 279) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 280;
                    continue contLoop;
                  } else if (this.pc === 280) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(279, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$21 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 277) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 277) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 278;
              continue contLoop;
            } else if (this.pc === 278) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = NofibPrelude.nofibStringToList("n");
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(277, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp22 = handleBlock$15();
    if (tmp22 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$14 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$22 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$22 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 274) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 274) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 275;
                    continue contLoop;
                  } else if (this.pc === 275) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(274, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$22 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 272) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 272) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 273;
              continue contLoop;
            } else if (this.pc === 273) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Var(tmp22);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(272, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp23 = handleBlock$14();
    if (tmp23 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$13 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$23 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$23 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 269) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 269) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 270;
                    continue contLoop;
                  } else if (this.pc === 270) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(269, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$23 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 267) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 267) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 268;
              continue contLoop;
            } else if (this.pc === 268) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Con(0);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(267, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp24 = handleBlock$13();
    if (tmp24 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$12 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$24 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$24 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 264) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 264) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 265;
                    continue contLoop;
                  } else if (this.pc === 265) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(264, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$24 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 262) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 262) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 263;
              continue contLoop;
            } else if (this.pc === 263) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = NofibPrelude.nofibStringToList("n");
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(262, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp25 = handleBlock$12();
    if (tmp25 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$11 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$25 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$25 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 259) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 259) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 260;
                    continue contLoop;
                  } else if (this.pc === 260) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(259, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$25 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 257) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 257) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 258;
              continue contLoop;
            } else if (this.pc === 258) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Var(tmp25);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(257, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp26 = handleBlock$11();
    if (tmp26 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$10 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$26 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$26 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 254) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 254) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 255;
                    continue contLoop;
                  } else if (this.pc === 255) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(254, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$26 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 252) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 252) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 253;
              continue contLoop;
            } else if (this.pc === 253) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = NofibPrelude.nofibStringToList("sum");
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(252, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp27 = handleBlock$10();
    if (tmp27 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$9 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$27 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$27 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 249) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 249) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 250;
                    continue contLoop;
                  } else if (this.pc === 250) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(249, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$27 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 247) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 247) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 248;
              continue contLoop;
            } else if (this.pc === 248) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Var(tmp27);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(247, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp28 = handleBlock$9();
    if (tmp28 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$8 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$28 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$28 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 244) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 244) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 245;
                    continue contLoop;
                  } else if (this.pc === 245) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(244, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$28 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 242) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 242) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 243;
              continue contLoop;
            } else if (this.pc === 243) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.App(tmp28, lambda.#nMinus1);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(242, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp29 = handleBlock$8();
    if (tmp29 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$7 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$29 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$29 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 239) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 239) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 240;
                    continue contLoop;
                  } else if (this.pc === 240) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(239, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$29 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 237) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 237) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 238;
              continue contLoop;
            } else if (this.pc === 238) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Add(tmp26, tmp29);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(237, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp30 = handleBlock$7();
    if (tmp30 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$6 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$30 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$30 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 234) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 234) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 235;
                    continue contLoop;
                  } else if (this.pc === 235) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(234, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$30 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 232) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 232) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 233;
              continue contLoop;
            } else if (this.pc === 233) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.IfZero(tmp23, tmp24, tmp30);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(232, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp31 = handleBlock$6();
    if (tmp31 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$5 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$31 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$31 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 229) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 229) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 230;
                    continue contLoop;
                  } else if (this.pc === 230) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(229, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$31 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 227) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 227) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 228;
              continue contLoop;
            } else if (this.pc === 228) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Lam(tmp21, tmp31);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(227, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp32 = handleBlock$5();
    if (tmp32 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$4 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$32 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$32 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 224) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 224) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 225;
                    continue contLoop;
                  } else if (this.pc === 225) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(224, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$32 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 222) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 222) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 223;
              continue contLoop;
            } else if (this.pc === 223) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.Lam(tmp20, tmp32);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(222, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp33 = handleBlock$4();
    if (tmp33 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    lambda.#partialSum0 = tmp33;
    handleBlock$3 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$33 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$33 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 219) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 219) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 220;
                    continue contLoop;
                  } else if (this.pc === 220) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(219, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$33 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 217) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 217) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 218;
              continue contLoop;
            } else if (this.pc === 218) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.App(lambda.#fix, lambda.#partialSum0);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(217, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp34 = handleBlock$3();
    if (tmp34 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    lambda.#sum0 = tmp34;
    handleBlock$2 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$34 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$34 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 214) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 214) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 215;
                    continue contLoop;
                  } else if (this.pc === 215) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(214, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$34 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 212) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 212) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 213;
              continue contLoop;
            } else if (this.pc === 213) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = lambda.testLambda_nofib(80);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(212, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp35 = handleBlock$2();
    if (tmp35 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$1 = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$35 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$35 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 209) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 209) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 210;
                    continue contLoop;
                  } else if (this.pc === 210) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(209, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$35 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 207) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 207) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 208;
              continue contLoop;
            } else if (this.pc === 208) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = runtime.safeCall(tmp35.toString());
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(207, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    tmp36 = handleBlock$1();
    if (tmp36 instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    handleBlock$ = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$37, StackDelay$37;
      StackDelay$37 = class StackDelay$36 extends runtime.StackDelay {
        constructor() {
          let tmp37;
          tmp37 = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$37;
            Cont$handler$stackHandler$37 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$37.class = class Cont$handler$stackHandler$36 extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp37;
                tmp37 = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 204) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 204) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 205;
                    continue contLoop;
                  } else if (this.pc === 205) {
                    this.completed = true;
                    return res2
                  }
                  break;
                }
              }
              toString() { return "Cont$handler$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
            };
            runtime.stackOffset = runtime.stackDepth;
            res2 = resume();
            if (res2 instanceof runtime.EffectSig.class) {
              handleBlock.contHead.next = new Cont$handler$stackHandler$37.class(204, handleBlock.contHead.next);
              if (handleBlock.lastHandlerCont === null) {
                handleBlock.lastHandlerCont = handleBlock.contHead.next;
              }
              return res2
            }
            if (res2 instanceof runtime.Return.class) {
              return res2
            }
            return res2
          })
        }
        toString() { return "StackDelay$"; }
      };
      stackHandler = new StackDelay$37();
      Cont$handleBlock$stackHandler$37 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$37.class = class Cont$handleBlock$stackHandler$36 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp37;
          tmp37 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 202) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 202) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 203;
              continue contLoop;
            } else if (this.pc === 203) {
              this.completed = true;
              return res1
            }
            break;
          }
        }
        toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      runtime.stackLimit = 500;
      runtime.stackOffset = 0;
      runtime.stackDepth = 1;
      runtime.stackHandler = stackHandler;
      res1 = NofibPrelude.print(tmp36);
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$37(202, null);
        return runtime.handleBlockImpl(res1, stackHandler)
      }
      if (res1 instanceof runtime.Return.class) {
        return res1
      }
      return res1
    };
    res = handleBlock$();
    if (res instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    runtime.stackDepth = 0;
    runtime.stackHandler = null;
    res
  }
  static lookup(k, t) {
    let param0, param1, first1, first0, x, v, t1, scrut, curDepth, tmp, tmp1, stackDelayRes, Cont$func$lookup$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_76_180$1;
    Cont$func$lookup$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_76_180$1 = function Cont$func$lookup$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_76_180$(pc1, next1) { return new Cont$func$lookup$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_76_180$.class(pc1, next1); };
    Cont$func$lookup$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_76_180$1.class = class Cont$func$lookup$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_76_180$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp2;
        tmp2 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 0) {
          stackDelayRes = value$;
        } else if (this.pc === 3) {
          tmp1 = value$;
        } else if (this.pc === 2) {
          tmp = value$;
        } else if (this.pc === 1) {
          scrut = value$;
        }
        contLoop: while (true) {
          if (this.pc === 0) {
            if (t instanceof NofibPrelude.Nil.class) {
              this.completed = true;
              return NofibPrelude.None
            } else if (t instanceof NofibPrelude.Cons.class) {
              param0 = t.head;
              param1 = t.tail;
              if (globalThis.Array.isArray(param0) && param0.length === 2) {
                first0 = param0[0];
                first1 = param0[1];
                x = first0;
                v = first1;
                t1 = param1;
                runtime.stackDepth = runtime.stackDepth + 1;
                scrut = NofibPrelude.listEq(k, x);
                if (scrut instanceof runtime.EffectSig.class) {
                  this.pc = 1;
                  return scrut
                }
                this.pc = 1;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp = new globalThis.Error("match error");
                if (tmp instanceof runtime.EffectSig.class) {
                  this.pc = 2;
                  return tmp
                }
                this.pc = 2;
                continue contLoop;
              }
              this.pc = 4;
              continue contLoop;
              this.pc = 4;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = new globalThis.Error("match error");
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 3;
                return tmp1
              }
              this.pc = 3;
              continue contLoop;
            }
            this.pc = 4;
            continue contLoop;
          } else if (this.pc === 4) {
            break contLoop;
          } else if (this.pc === 3) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            throw tmp1;
          } else if (this.pc === 2) {
            tmp = runtime.resetDepth(tmp, curDepth);
            throw tmp;
          } else if (this.pc === 1) {
            scrut = runtime.resetDepth(scrut, curDepth);
            if (scrut === true) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return NofibPrelude.Some(v)
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return lambda.lookup(k, t1)
            }
            this.pc = 4;
            continue contLoop;
          }
          break;
        }
      }
      toString() { return "Cont$func$lookup$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_76_180$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$lookup$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_76_180$1.class(0, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (t instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.None
    } else if (t instanceof NofibPrelude.Cons.class) {
      param0 = t.head;
      param1 = t.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        x = first0;
        v = first1;
        t1 = param1;
        runtime.stackDepth = runtime.stackDepth + 1;
        scrut = NofibPrelude.listEq(k, x);
        if (scrut instanceof runtime.EffectSig.class) {
          scrut.tail.next = new Cont$func$lookup$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_76_180$1.class(1, null);
          scrut.tail = scrut.tail.next;
          return scrut
        }
        scrut = runtime.resetDepth(scrut, curDepth);
        if (scrut === true) {
          runtime.stackDepth = runtime.stackDepth + 1;
          return NofibPrelude.Some(v)
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          return lambda.lookup(k, t1)
        }
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp = new globalThis.Error("match error");
        if (tmp instanceof runtime.EffectSig.class) {
          tmp.tail.next = new Cont$func$lookup$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_76_180$1.class(2, null);
          tmp.tail = tmp.tail.next;
          return tmp
        }
        tmp = runtime.resetDepth(tmp, curDepth);
        throw tmp;
      }
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = new globalThis.Error("match error");
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.tail.next = new Cont$func$lookup$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_76_180$1.class(3, null);
        tmp1.tail = tmp1.tail.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      throw tmp1;
    }
  } 
  static myRunState(m, s) {
    let param0, f, tmp, curDepth, stackDelayRes, Cont$func$myRunState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_223_270$1;
    Cont$func$myRunState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_223_270$1 = function Cont$func$myRunState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_223_270$(pc1, next1) { return new Cont$func$myRunState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_223_270$.class(pc1, next1); };
    Cont$func$myRunState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_223_270$1.class = class Cont$func$myRunState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_223_270$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp1;
        tmp1 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 5) {
          stackDelayRes = value$;
        } else if (this.pc === 6) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 5) {
            if (m instanceof lambda.MyState.class) {
              param0 = m.r;
              f = param0;
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return runtime.safeCall(f(s))
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = new globalThis.Error("match error");
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 6;
                return tmp
              }
              this.pc = 6;
              continue contLoop;
            }
            this.pc = 7;
            continue contLoop;
          } else if (this.pc === 7) {
            break contLoop;
          } else if (this.pc === 6) {
            tmp = runtime.resetDepth(tmp, curDepth);
            throw tmp;
          }
          break;
        }
      }
      toString() { return "Cont$func$myRunState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_223_270$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$myRunState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_223_270$1.class(5, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (m instanceof lambda.MyState.class) {
      param0 = m.r;
      f = param0;
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f(s))
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = new globalThis.Error("match error");
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.tail.next = new Cont$func$myRunState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_223_270$1.class(6, null);
        tmp.tail = tmp.tail.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      throw tmp;
    }
  } 
  static myBind(m1, f) {
    let tmp, stackDelayRes, Cont$func$myBind$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_276_361$1;
    Cont$func$myBind$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_276_361$1 = function Cont$func$myBind$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_276_361$(pc1, next1) { return new Cont$func$myBind$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_276_361$.class(pc1, next1); };
    Cont$func$myBind$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_276_361$1.class = class Cont$func$myBind$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_276_361$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp1;
        tmp1 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 8) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 8) {
            tmp = (s1) => {
              let scrut, first1, first0, s_, a, tmp1, curDepth, tmp2, stackDelayRes1, Cont$lambda$9;
              Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$9.class = class Cont$lambda$1 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp3;
                  tmp3 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 9) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 10) {
                    scrut = value$1;
                  } else if (this.pc === 12) {
                    tmp2 = value$1;
                  } else if (this.pc === 11) {
                    tmp1 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 9) {
                      runtime.stackDepth = runtime.stackDepth + 1;
                      scrut = lambda.myRunState(m1, s1);
                      if (scrut instanceof runtime.EffectSig.class) {
                        this.pc = 10;
                        return scrut
                      }
                      this.pc = 10;
                      continue contLoop1;
                    } else if (this.pc === 10) {
                      scrut = runtime.resetDepth(scrut, curDepth);
                      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
                        first0 = scrut[0];
                        first1 = scrut[1];
                        s_ = first0;
                        a = first1;
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp1 = runtime.safeCall(f(a));
                        if (tmp1 instanceof runtime.EffectSig.class) {
                          this.pc = 11;
                          return tmp1
                        }
                        this.pc = 11;
                        continue contLoop1;
                      } else {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp2 = new globalThis.Error("match error");
                        if (tmp2 instanceof runtime.EffectSig.class) {
                          this.pc = 12;
                          return tmp2
                        }
                        this.pc = 12;
                        continue contLoop1;
                      }
                      this.pc = 13;
                      continue contLoop1;
                    } else if (this.pc === 13) {
                      break contLoop1;
                    } else if (this.pc === 12) {
                      tmp2 = runtime.resetDepth(tmp2, curDepth);
                      throw tmp2;
                    } else if (this.pc === 11) {
                      tmp1 = runtime.resetDepth(tmp1, curDepth);
                      runtime.stackDepth = runtime.stackDepth + 1;
                      this.completed = true;
                      return lambda.myRunState(tmp1, s_)
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              curDepth = runtime.stackDepth;
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$9.class(9, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              runtime.stackDepth = runtime.stackDepth + 1;
              scrut = lambda.myRunState(m1, s1);
              if (scrut instanceof runtime.EffectSig.class) {
                scrut.tail.next = new Cont$lambda$9.class(10, null);
                scrut.tail = scrut.tail.next;
                return scrut
              }
              scrut = runtime.resetDepth(scrut, curDepth);
              if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
                first0 = scrut[0];
                first1 = scrut[1];
                s_ = first0;
                a = first1;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp1 = runtime.safeCall(f(a));
                if (tmp1 instanceof runtime.EffectSig.class) {
                  tmp1.tail.next = new Cont$lambda$9.class(11, null);
                  tmp1.tail = tmp1.tail.next;
                  return tmp1
                }
                tmp1 = runtime.resetDepth(tmp1, curDepth);
                runtime.stackDepth = runtime.stackDepth + 1;
                return lambda.myRunState(tmp1, s_)
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp2 = new globalThis.Error("match error");
                if (tmp2 instanceof runtime.EffectSig.class) {
                  tmp2.tail.next = new Cont$lambda$9.class(12, null);
                  tmp2.tail = tmp2.tail.next;
                  return tmp2
                }
                tmp2 = runtime.resetDepth(tmp2, curDepth);
                throw tmp2;
              }
            };
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.MyState(tmp)
          }
          break;
        }
      }
      toString() { return "Cont$func$myBind$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_276_361$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$myBind$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_276_361$1.class(8, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    tmp = (s1) => {
      let scrut, first1, first0, s_, a, tmp1, curDepth, tmp2, stackDelayRes1, Cont$lambda$9;
      Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
      Cont$lambda$9.class = class Cont$lambda$1 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp3;
          tmp3 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 9) {
            stackDelayRes1 = value$;
          } else if (this.pc === 10) {
            scrut = value$;
          } else if (this.pc === 12) {
            tmp2 = value$;
          } else if (this.pc === 11) {
            tmp1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 9) {
              runtime.stackDepth = runtime.stackDepth + 1;
              scrut = lambda.myRunState(m1, s1);
              if (scrut instanceof runtime.EffectSig.class) {
                this.pc = 10;
                return scrut
              }
              this.pc = 10;
              continue contLoop;
            } else if (this.pc === 10) {
              scrut = runtime.resetDepth(scrut, curDepth);
              if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
                first0 = scrut[0];
                first1 = scrut[1];
                s_ = first0;
                a = first1;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp1 = runtime.safeCall(f(a));
                if (tmp1 instanceof runtime.EffectSig.class) {
                  this.pc = 11;
                  return tmp1
                }
                this.pc = 11;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp2 = new globalThis.Error("match error");
                if (tmp2 instanceof runtime.EffectSig.class) {
                  this.pc = 12;
                  return tmp2
                }
                this.pc = 12;
                continue contLoop;
              }
              this.pc = 13;
              continue contLoop;
            } else if (this.pc === 13) {
              break contLoop;
            } else if (this.pc === 12) {
              tmp2 = runtime.resetDepth(tmp2, curDepth);
              throw tmp2;
            } else if (this.pc === 11) {
              tmp1 = runtime.resetDepth(tmp1, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return lambda.myRunState(tmp1, s_)
            }
            break;
          }
        }
        toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$lambda$9.class(9, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      scrut = lambda.myRunState(m1, s1);
      if (scrut instanceof runtime.EffectSig.class) {
        scrut.tail.next = new Cont$lambda$9.class(10, null);
        scrut.tail = scrut.tail.next;
        return scrut
      }
      scrut = runtime.resetDepth(scrut, curDepth);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        s_ = first0;
        a = first1;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp1 = runtime.safeCall(f(a));
        if (tmp1 instanceof runtime.EffectSig.class) {
          tmp1.tail.next = new Cont$lambda$9.class(11, null);
          tmp1.tail = tmp1.tail.next;
          return tmp1
        }
        tmp1 = runtime.resetDepth(tmp1, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        return lambda.myRunState(tmp1, s_)
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp2 = new globalThis.Error("match error");
        if (tmp2 instanceof runtime.EffectSig.class) {
          tmp2.tail.next = new Cont$lambda$9.class(12, null);
          tmp2.tail = tmp2.tail.next;
          return tmp2
        }
        tmp2 = runtime.resetDepth(tmp2, curDepth);
        throw tmp2;
      }
    };
    runtime.stackDepth = runtime.stackDepth + 1;
    return lambda.MyState(tmp)
  } 
  static myReturn(a) {
    let stackDelayRes, Cont$func$myReturn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_367_401$1;
    Cont$func$myReturn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_367_401$1 = function Cont$func$myReturn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_367_401$(pc1, next1) { return new Cont$func$myReturn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_367_401$.class(pc1, next1); };
    Cont$func$myReturn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_367_401$1.class = class Cont$func$myReturn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_367_401$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp;
        tmp = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 14) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 14) {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.MyState((s1) => {
              return [
                s1,
                a
              ]
            })
          }
          break;
        }
      }
      toString() { return "Cont$func$myReturn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_367_401$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$myReturn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_367_401$1.class(14, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return lambda.MyState((s1) => {
      return [
        s1,
        a
      ]
    })
  } 
  static myEvalState(m2, s1) {
    let scrut, first1, first0, s_, a1, curDepth, tmp, stackDelayRes, Cont$func$myEvalState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_473_530$1;
    Cont$func$myEvalState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_473_530$1 = function Cont$func$myEvalState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_473_530$(pc1, next1) { return new Cont$func$myEvalState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_473_530$.class(pc1, next1); };
    Cont$func$myEvalState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_473_530$1.class = class Cont$func$myEvalState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_473_530$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp1;
        tmp1 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 15) {
          stackDelayRes = value$;
        } else if (this.pc === 16) {
          scrut = value$;
        } else if (this.pc === 17) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 15) {
            runtime.stackDepth = runtime.stackDepth + 1;
            scrut = lambda.myRunState(m2, s1);
            if (scrut instanceof runtime.EffectSig.class) {
              this.pc = 16;
              return scrut
            }
            this.pc = 16;
            continue contLoop;
          } else if (this.pc === 16) {
            scrut = runtime.resetDepth(scrut, curDepth);
            if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
              first0 = scrut[0];
              first1 = scrut[1];
              s_ = first0;
              a1 = first1;
              this.completed = true;
              return a1
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = new globalThis.Error("match error");
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 17;
                return tmp
              }
              this.pc = 17;
              continue contLoop;
            }
            this.pc = 18;
            continue contLoop;
          } else if (this.pc === 18) {
            break contLoop;
          } else if (this.pc === 17) {
            tmp = runtime.resetDepth(tmp, curDepth);
            throw tmp;
          }
          break;
        }
      }
      toString() { return "Cont$func$myEvalState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_473_530$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$myEvalState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_473_530$1.class(15, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    scrut = lambda.myRunState(m2, s1);
    if (scrut instanceof runtime.EffectSig.class) {
      scrut.tail.next = new Cont$func$myEvalState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_473_530$1.class(16, null);
      scrut.tail = scrut.tail.next;
      return scrut
    }
    scrut = runtime.resetDepth(scrut, curDepth);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      s_ = first0;
      a1 = first1;
      return a1
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = new globalThis.Error("match error");
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.tail.next = new Cont$func$myEvalState$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_473_530$1.class(17, null);
        tmp.tail = tmp.tail.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      throw tmp;
    }
  } 
  static eqEnv(a1, b) {
    let param0, param1, first1, first0, s11, t1, b1, param01, param11, first11, first01, s2, t2, d, scrut, scrut1, curDepth, stackDelayRes, Cont$func$eqEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_931_1079$1;
    Cont$func$eqEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_931_1079$1 = function Cont$func$eqEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_931_1079$(pc1, next1) { return new Cont$func$eqEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_931_1079$.class(pc1, next1); };
    Cont$func$eqEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_931_1079$1.class = class Cont$func$eqEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_931_1079$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp;
        tmp = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 19) {
          stackDelayRes = value$;
        } else if (this.pc === 20) {
          scrut = value$;
        } else if (this.pc === 21) {
          scrut1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 19) {
            if (a1 instanceof NofibPrelude.Nil.class) {
              if (b instanceof NofibPrelude.Nil.class) {
                this.completed = true;
                return true
              } else {
                this.completed = true;
                return false
              }
              this.pc = 22;
              continue contLoop;
            } else if (a1 instanceof NofibPrelude.Cons.class) {
              param0 = a1.head;
              param1 = a1.tail;
              if (globalThis.Array.isArray(param0) && param0.length === 2) {
                first0 = param0[0];
                first1 = param0[1];
                s11 = first0;
                t1 = first1;
                b1 = param1;
                if (b1 instanceof NofibPrelude.Cons.class) {
                  param01 = b1.head;
                  param11 = b1.tail;
                  if (globalThis.Array.isArray(param01) && param01.length === 2) {
                    first01 = param01[0];
                    first11 = param01[1];
                    s2 = first01;
                    t2 = first11;
                    d = param11;
                    runtime.stackDepth = runtime.stackDepth + 1;
                    scrut = NofibPrelude.listEq(s11, s2);
                    if (scrut instanceof runtime.EffectSig.class) {
                      this.pc = 20;
                      return scrut
                    }
                    this.pc = 20;
                    continue contLoop;
                  } else {
                    this.completed = true;
                    return false
                  }
                  this.pc = 22;
                  continue contLoop;
                } else {
                  this.completed = true;
                  return false
                }
                this.pc = 22;
                continue contLoop;
              } else {
                this.completed = true;
                return false
              }
              this.pc = 22;
              continue contLoop;
              this.pc = 22;
              continue contLoop;
            } else {
              this.completed = true;
              return false
            }
            this.pc = 22;
            continue contLoop;
          } else if (this.pc === 22) {
            break contLoop;
          } else if (this.pc === 20) {
            scrut = runtime.resetDepth(scrut, curDepth);
            if (scrut === true) {
              runtime.stackDepth = runtime.stackDepth + 1;
              scrut1 = lambda.eqTerm(t1, t2);
              if (scrut1 instanceof runtime.EffectSig.class) {
                this.pc = 21;
                return scrut1
              }
              this.pc = 21;
              continue contLoop;
            } else {
              this.completed = true;
              return false
            }
            this.pc = 22;
            continue contLoop;
          } else if (this.pc === 21) {
            scrut1 = runtime.resetDepth(scrut1, curDepth);
            if (scrut1 === true) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return lambda.eqEnv(b1, d)
            } else {
              this.completed = true;
              return false
            }
            this.pc = 22;
            continue contLoop;
          }
          break;
        }
      }
      toString() { return "Cont$func$eqEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_931_1079$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$eqEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_931_1079$1.class(19, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (a1 instanceof NofibPrelude.Nil.class) {
      if (b instanceof NofibPrelude.Nil.class) {
        return true
      } else {
        return false
      }
    } else if (a1 instanceof NofibPrelude.Cons.class) {
      param0 = a1.head;
      param1 = a1.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        s11 = first0;
        t1 = first1;
        b1 = param1;
        if (b1 instanceof NofibPrelude.Cons.class) {
          param01 = b1.head;
          param11 = b1.tail;
          if (globalThis.Array.isArray(param01) && param01.length === 2) {
            first01 = param01[0];
            first11 = param01[1];
            s2 = first01;
            t2 = first11;
            d = param11;
            runtime.stackDepth = runtime.stackDepth + 1;
            scrut = NofibPrelude.listEq(s11, s2);
            if (scrut instanceof runtime.EffectSig.class) {
              scrut.tail.next = new Cont$func$eqEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_931_1079$1.class(20, null);
              scrut.tail = scrut.tail.next;
              return scrut
            }
            scrut = runtime.resetDepth(scrut, curDepth);
            if (scrut === true) {
              runtime.stackDepth = runtime.stackDepth + 1;
              scrut1 = lambda.eqTerm(t1, t2);
              if (scrut1 instanceof runtime.EffectSig.class) {
                scrut1.tail.next = new Cont$func$eqEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_931_1079$1.class(21, null);
                scrut1.tail = scrut1.tail.next;
                return scrut1
              }
              scrut1 = runtime.resetDepth(scrut1, curDepth);
              if (scrut1 === true) {
                runtime.stackDepth = runtime.stackDepth + 1;
                return lambda.eqEnv(b1, d)
              } else {
                return false
              }
            } else {
              return false
            }
          } else {
            return false
          }
        } else {
          return false
        }
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static eqTerm(a2, b1) {
    let param0, param1, a3, b2, param01, param11, c, d, param02, param12, param2, a4, b3, c1, param03, param13, param21, d1, e, f1, param04, param14, a5, b4, param05, param15, c2, d2, param06, param16, a6, b5, param07, param17, c3, d3, param08, param18, a7, b6, param09, param19, c4, d4, param010, a8, param011, b7, param012, a9, param013, b8, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, curDepth, stackDelayRes, Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1;
    Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1 = function Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$(pc1, next1) { return new Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$.class(pc1, next1); };
    Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1.class = class Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp12;
        tmp12 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 23) {
          stackDelayRes = value$;
        } else if (this.pc === 33) {
          tmp10 = value$;
        } else if (this.pc === 34) {
          tmp11 = value$;
        } else if (this.pc === 30) {
          tmp6 = value$;
        } else if (this.pc === 31) {
          tmp7 = value$;
        } else if (this.pc === 32) {
          tmp9 = value$;
        } else if (this.pc === 28) {
          tmp4 = value$;
        } else if (this.pc === 29) {
          tmp5 = value$;
        } else if (this.pc === 26) {
          tmp2 = value$;
        } else if (this.pc === 27) {
          tmp3 = value$;
        } else if (this.pc === 24) {
          tmp = value$;
        } else if (this.pc === 25) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 23) {
            if (a2 instanceof lambda.Var.class) {
              param012 = a2.s;
              a9 = param012;
              if (b1 instanceof lambda.Var.class) {
                param013 = b1.s;
                b8 = param013;
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return NofibPrelude.listEq(a9, b8)
              } else {
                this.completed = true;
                return false
              }
              this.pc = 35;
              continue contLoop;
            } else if (a2 instanceof lambda.Con.class) {
              param010 = a2.i;
              a8 = param010;
              if (b1 instanceof lambda.Con.class) {
                param011 = b1.i;
                b7 = param011;
                this.completed = true;
                return a8 === b7
              } else {
                this.completed = true;
                return false
              }
              this.pc = 35;
              continue contLoop;
              this.pc = 35;
              continue contLoop;
            } else if (a2 instanceof lambda.Incr.class) {
              if (b1 instanceof lambda.Incr.class) {
                this.completed = true;
                return true
              } else {
                this.completed = true;
                return false
              }
              this.pc = 35;
              continue contLoop;
              this.pc = 35;
              continue contLoop;
              this.pc = 35;
              continue contLoop;
            } else {
              if (a2 instanceof lambda.Add.class) {
                param08 = a2.a;
                param18 = a2.b;
                a7 = param08;
                b6 = param18;
                if (b6 instanceof lambda.Add.class) {
                  param09 = b6.a;
                  param19 = b6.b;
                  c4 = param09;
                  d4 = param19;
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp = lambda.eqTerm(a7, c4);
                  if (tmp instanceof runtime.EffectSig.class) {
                    this.pc = 24;
                    return tmp
                  }
                  this.pc = 24;
                  continue contLoop;
                } else {
                  this.completed = true;
                  return false
                }
                this.pc = 35;
                continue contLoop;
              } else if (a2 instanceof lambda.Lam.class) {
                param06 = a2.s;
                param16 = a2.t;
                a6 = param06;
                b5 = param16;
                if (b5 instanceof lambda.Lam.class) {
                  param07 = b5.s;
                  param17 = b5.t;
                  c3 = param07;
                  d3 = param17;
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp2 = NofibPrelude.listEq(a6, c3);
                  if (tmp2 instanceof runtime.EffectSig.class) {
                    this.pc = 26;
                    return tmp2
                  }
                  this.pc = 26;
                  continue contLoop;
                } else {
                  this.completed = true;
                  return false
                }
                this.pc = 35;
                continue contLoop;
                this.pc = 35;
                continue contLoop;
              } else if (a2 instanceof lambda.App.class) {
                param04 = a2.a;
                param14 = a2.b;
                a5 = param04;
                b4 = param14;
                if (b4 instanceof lambda.App.class) {
                  param05 = b4.a;
                  param15 = b4.b;
                  c2 = param05;
                  d2 = param15;
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp4 = lambda.eqTerm(a5, c2);
                  if (tmp4 instanceof runtime.EffectSig.class) {
                    this.pc = 28;
                    return tmp4
                  }
                  this.pc = 28;
                  continue contLoop;
                } else {
                  this.completed = true;
                  return false
                }
                this.pc = 35;
                continue contLoop;
                this.pc = 35;
                continue contLoop;
                this.pc = 35;
                continue contLoop;
              } else if (a2 instanceof lambda.IfZero.class) {
                param02 = a2.a;
                param12 = a2.b;
                param2 = a2.c;
                a4 = param02;
                b3 = param12;
                c1 = param2;
                if (b3 instanceof lambda.IfZero.class) {
                  param03 = b3.a;
                  param13 = b3.b;
                  param21 = b3.c;
                  d1 = param03;
                  e = param13;
                  f1 = param21;
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp6 = lambda.eqTerm(a4, d1);
                  if (tmp6 instanceof runtime.EffectSig.class) {
                    this.pc = 30;
                    return tmp6
                  }
                  this.pc = 30;
                  continue contLoop;
                } else {
                  this.completed = true;
                  return false
                }
                this.pc = 35;
                continue contLoop;
                this.pc = 35;
                continue contLoop;
                this.pc = 35;
                continue contLoop;
                this.pc = 35;
                continue contLoop;
              } else if (a2 instanceof lambda.Thunk.class) {
                param0 = a2.t;
                param1 = a2.e;
                a3 = param0;
                b2 = param1;
                if (b2 instanceof lambda.Thunk.class) {
                  param01 = b2.t;
                  param11 = b2.e;
                  c = param01;
                  d = param11;
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp10 = lambda.eqTerm(a3, c);
                  if (tmp10 instanceof runtime.EffectSig.class) {
                    this.pc = 33;
                    return tmp10
                  }
                  this.pc = 33;
                  continue contLoop;
                } else {
                  this.completed = true;
                  return false
                }
                this.pc = 35;
                continue contLoop;
                this.pc = 35;
                continue contLoop;
                this.pc = 35;
                continue contLoop;
                this.pc = 35;
                continue contLoop;
                this.pc = 35;
                continue contLoop;
              } else {
                this.completed = true;
                return false
              }
              this.pc = 35;
              continue contLoop;
            }
            this.pc = 35;
            continue contLoop;
          } else if (this.pc === 35) {
            break contLoop;
          } else if (this.pc === 33) {
            tmp10 = runtime.resetDepth(tmp10, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp11 = lambda.eqEnv(b2, d);
            if (tmp11 instanceof runtime.EffectSig.class) {
              this.pc = 34;
              return tmp11
            }
            this.pc = 34;
            continue contLoop;
          } else if (this.pc === 34) {
            tmp11 = runtime.resetDepth(tmp11, curDepth);
            this.completed = true;
            return tmp10 && tmp11
          } else if (this.pc === 30) {
            tmp6 = runtime.resetDepth(tmp6, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp7 = lambda.eqTerm(b3, e);
            if (tmp7 instanceof runtime.EffectSig.class) {
              this.pc = 31;
              return tmp7
            }
            this.pc = 31;
            continue contLoop;
          } else if (this.pc === 31) {
            tmp7 = runtime.resetDepth(tmp7, curDepth);
            tmp8 = tmp6 && tmp7;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp9 = lambda.eqTerm(c1, f1);
            if (tmp9 instanceof runtime.EffectSig.class) {
              this.pc = 32;
              return tmp9
            }
            this.pc = 32;
            continue contLoop;
          } else if (this.pc === 32) {
            tmp9 = runtime.resetDepth(tmp9, curDepth);
            this.completed = true;
            return tmp8 && tmp9
          } else if (this.pc === 28) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp5 = lambda.eqTerm(b4, d2);
            if (tmp5 instanceof runtime.EffectSig.class) {
              this.pc = 29;
              return tmp5
            }
            this.pc = 29;
            continue contLoop;
          } else if (this.pc === 29) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            this.completed = true;
            return tmp4 && tmp5
          } else if (this.pc === 26) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = lambda.eqTerm(b5, d3);
            if (tmp3 instanceof runtime.EffectSig.class) {
              this.pc = 27;
              return tmp3
            }
            this.pc = 27;
            continue contLoop;
          } else if (this.pc === 27) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            this.completed = true;
            return tmp2 && tmp3
          } else if (this.pc === 24) {
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = lambda.eqTerm(b6, d4);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 25;
              return tmp1
            }
            this.pc = 25;
            continue contLoop;
          } else if (this.pc === 25) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            this.completed = true;
            return tmp && tmp1
          }
          break;
        }
      }
      toString() { return "Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1.class(23, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (a2 instanceof lambda.Var.class) {
      param012 = a2.s;
      a9 = param012;
      if (b1 instanceof lambda.Var.class) {
        param013 = b1.s;
        b8 = param013;
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.listEq(a9, b8)
      } else {
        return false
      }
    } else if (a2 instanceof lambda.Con.class) {
      param010 = a2.i;
      a8 = param010;
      if (b1 instanceof lambda.Con.class) {
        param011 = b1.i;
        b7 = param011;
        return a8 === b7
      } else {
        return false
      }
    } else if (a2 instanceof lambda.Incr.class) {
      if (b1 instanceof lambda.Incr.class) {
        return true
      } else {
        return false
      }
    } else if (a2 instanceof lambda.Add.class) {
      param08 = a2.a;
      param18 = a2.b;
      a7 = param08;
      b6 = param18;
      if (b6 instanceof lambda.Add.class) {
        param09 = b6.a;
        param19 = b6.b;
        c4 = param09;
        d4 = param19;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp = lambda.eqTerm(a7, c4);
        if (tmp instanceof runtime.EffectSig.class) {
          tmp.tail.next = new Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1.class(24, null);
          tmp.tail = tmp.tail.next;
          return tmp
        }
        tmp = runtime.resetDepth(tmp, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp1 = lambda.eqTerm(b6, d4);
        if (tmp1 instanceof runtime.EffectSig.class) {
          tmp1.tail.next = new Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1.class(25, null);
          tmp1.tail = tmp1.tail.next;
          return tmp1
        }
        tmp1 = runtime.resetDepth(tmp1, curDepth);
        return tmp && tmp1
      } else {
        return false
      }
    } else if (a2 instanceof lambda.Lam.class) {
      param06 = a2.s;
      param16 = a2.t;
      a6 = param06;
      b5 = param16;
      if (b5 instanceof lambda.Lam.class) {
        param07 = b5.s;
        param17 = b5.t;
        c3 = param07;
        d3 = param17;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp2 = NofibPrelude.listEq(a6, c3);
        if (tmp2 instanceof runtime.EffectSig.class) {
          tmp2.tail.next = new Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1.class(26, null);
          tmp2.tail = tmp2.tail.next;
          return tmp2
        }
        tmp2 = runtime.resetDepth(tmp2, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp3 = lambda.eqTerm(b5, d3);
        if (tmp3 instanceof runtime.EffectSig.class) {
          tmp3.tail.next = new Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1.class(27, null);
          tmp3.tail = tmp3.tail.next;
          return tmp3
        }
        tmp3 = runtime.resetDepth(tmp3, curDepth);
        return tmp2 && tmp3
      } else {
        return false
      }
    } else if (a2 instanceof lambda.App.class) {
      param04 = a2.a;
      param14 = a2.b;
      a5 = param04;
      b4 = param14;
      if (b4 instanceof lambda.App.class) {
        param05 = b4.a;
        param15 = b4.b;
        c2 = param05;
        d2 = param15;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp4 = lambda.eqTerm(a5, c2);
        if (tmp4 instanceof runtime.EffectSig.class) {
          tmp4.tail.next = new Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1.class(28, null);
          tmp4.tail = tmp4.tail.next;
          return tmp4
        }
        tmp4 = runtime.resetDepth(tmp4, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp5 = lambda.eqTerm(b4, d2);
        if (tmp5 instanceof runtime.EffectSig.class) {
          tmp5.tail.next = new Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1.class(29, null);
          tmp5.tail = tmp5.tail.next;
          return tmp5
        }
        tmp5 = runtime.resetDepth(tmp5, curDepth);
        return tmp4 && tmp5
      } else {
        return false
      }
    } else if (a2 instanceof lambda.IfZero.class) {
      param02 = a2.a;
      param12 = a2.b;
      param2 = a2.c;
      a4 = param02;
      b3 = param12;
      c1 = param2;
      if (b3 instanceof lambda.IfZero.class) {
        param03 = b3.a;
        param13 = b3.b;
        param21 = b3.c;
        d1 = param03;
        e = param13;
        f1 = param21;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp6 = lambda.eqTerm(a4, d1);
        if (tmp6 instanceof runtime.EffectSig.class) {
          tmp6.tail.next = new Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1.class(30, null);
          tmp6.tail = tmp6.tail.next;
          return tmp6
        }
        tmp6 = runtime.resetDepth(tmp6, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp7 = lambda.eqTerm(b3, e);
        if (tmp7 instanceof runtime.EffectSig.class) {
          tmp7.tail.next = new Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1.class(31, null);
          tmp7.tail = tmp7.tail.next;
          return tmp7
        }
        tmp7 = runtime.resetDepth(tmp7, curDepth);
        tmp8 = tmp6 && tmp7;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp9 = lambda.eqTerm(c1, f1);
        if (tmp9 instanceof runtime.EffectSig.class) {
          tmp9.tail.next = new Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1.class(32, null);
          tmp9.tail = tmp9.tail.next;
          return tmp9
        }
        tmp9 = runtime.resetDepth(tmp9, curDepth);
        return tmp8 && tmp9
      } else {
        return false
      }
    } else if (a2 instanceof lambda.Thunk.class) {
      param0 = a2.t;
      param1 = a2.e;
      a3 = param0;
      b2 = param1;
      if (b2 instanceof lambda.Thunk.class) {
        param01 = b2.t;
        param11 = b2.e;
        c = param01;
        d = param11;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp10 = lambda.eqTerm(a3, c);
        if (tmp10 instanceof runtime.EffectSig.class) {
          tmp10.tail.next = new Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1.class(33, null);
          tmp10.tail = tmp10.tail.next;
          return tmp10
        }
        tmp10 = runtime.resetDepth(tmp10, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp11 = lambda.eqEnv(b2, d);
        if (tmp11 instanceof runtime.EffectSig.class) {
          tmp11.tail.next = new Cont$func$eqTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1113_1603$1.class(34, null);
          tmp11.tail = tmp11.tail.next;
          return tmp11
        }
        tmp11 = runtime.resetDepth(tmp11, curDepth);
        return tmp10 && tmp11
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static myMaybe(d, f1, x) {
    let param0, x1, tmp, curDepth, stackDelayRes, Cont$func$myMaybe$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1622_1666$1;
    Cont$func$myMaybe$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1622_1666$1 = function Cont$func$myMaybe$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1622_1666$(pc1, next1) { return new Cont$func$myMaybe$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1622_1666$.class(pc1, next1); };
    Cont$func$myMaybe$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1622_1666$1.class = class Cont$func$myMaybe$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1622_1666$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp1;
        tmp1 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 36) {
          stackDelayRes = value$;
        } else if (this.pc === 37) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 36) {
            if (x instanceof NofibPrelude.Some.class) {
              param0 = x.x;
              x1 = param0;
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return runtime.safeCall(f1(x1))
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = new globalThis.Error("match error");
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 37;
                return tmp
              }
              this.pc = 37;
              continue contLoop;
            }
            this.pc = 38;
            continue contLoop;
          } else if (this.pc === 38) {
            break contLoop;
          } else if (this.pc === 37) {
            tmp = runtime.resetDepth(tmp, curDepth);
            throw tmp;
          }
          break;
        }
      }
      toString() { return "Cont$func$myMaybe$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1622_1666$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$myMaybe$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1622_1666$1.class(36, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (x instanceof NofibPrelude.Some.class) {
      param0 = x.x;
      x1 = param0;
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f1(x1))
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = new globalThis.Error("match error");
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.tail.next = new Cont$func$myMaybe$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1622_1666$1.class(37, null);
        tmp.tail = tmp.tail.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      throw tmp;
    }
  } 
  static lookupVar(v) {
    let lookup2, stackDelayRes, Cont$func$lookupVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1730_1879$1;
    Cont$func$lookupVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1730_1879$1 = function Cont$func$lookupVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1730_1879$(pc1, next1) { return new Cont$func$lookupVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1730_1879$.class(pc1, next1); };
    Cont$func$lookupVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1730_1879$1.class = class Cont$func$lookupVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1730_1879$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp;
        tmp = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 39) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 39) {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.myBind(lambda.#myGet, (env) => {
              let tmp, curDepth, stackDelayRes1, Cont$lambda$9;
              Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$9.class = class Cont$lambda$2 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp1;
                  tmp1 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 44) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 45) {
                    tmp = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 44) {
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp = lookup2(env);
                      if (tmp instanceof runtime.EffectSig.class) {
                        this.pc = 45;
                        return tmp
                      }
                      this.pc = 45;
                      continue contLoop1;
                    } else if (this.pc === 45) {
                      tmp = runtime.resetDepth(tmp, curDepth);
                      runtime.stackDepth = runtime.stackDepth + 1;
                      this.completed = true;
                      return lambda.myReturn(tmp)
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              curDepth = runtime.stackDepth;
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$9.class(44, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = lookup2(env);
              if (tmp instanceof runtime.EffectSig.class) {
                tmp.tail.next = new Cont$lambda$9.class(45, null);
                tmp.tail = tmp.tail.next;
                return tmp
              }
              tmp = runtime.resetDepth(tmp, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              return lambda.myReturn(tmp)
            })
          }
          break;
        }
      }
      toString() { return "Cont$func$lookupVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1730_1879$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    lookup2 = function lookup2(env) {
      let tmp, curDepth, stackDelayRes1, Cont$func$lookup2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1751_1832$1;
      Cont$func$lookup2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1751_1832$1 = function Cont$func$lookup2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1751_1832$(pc1, next1) { return new Cont$func$lookup2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1751_1832$.class(pc1, next1); };
      Cont$func$lookup2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1751_1832$1.class = class Cont$func$lookup2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1751_1832$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp1;
          tmp1 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 40) {
            stackDelayRes1 = value$;
          } else if (this.pc === 41) {
            tmp = value$;
          }
          contLoop: while (true) {
            if (this.pc === 40) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = lambda.lookup(v, env);
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 41;
                return tmp
              }
              this.pc = 41;
              continue contLoop;
            } else if (this.pc === 41) {
              tmp = runtime.resetDepth(tmp, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return lambda.myMaybe((dummy) => {
                let tmp1, curDepth1, stackDelayRes2, Cont$lambda$9;
                Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
                Cont$lambda$9.class = class Cont$lambda$3 extends runtime.Cont.class {
                  constructor(pc1, next1) {
                    let tmp2;
                    tmp2 = super(next1, false);
                    this.pc = pc1;
                    this.next = next1;
                  }
                  resume(value$1) {
                    if (this.pc === 42) {
                      stackDelayRes2 = value$1;
                    } else if (this.pc === 43) {
                      tmp1 = value$1;
                    }
                    contLoop1: while (true) {
                      if (this.pc === 42) {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp1 = globalThis.Error("undefined");
                        if (tmp1 instanceof runtime.EffectSig.class) {
                          this.pc = 43;
                          return tmp1
                        }
                        this.pc = 43;
                        continue contLoop1;
                      } else if (this.pc === 43) {
                        tmp1 = runtime.resetDepth(tmp1, curDepth1);
                        throw tmp1;
                      }
                      break;
                    }
                  }
                  toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
                };
                curDepth1 = runtime.stackDepth;
                stackDelayRes2 = runtime.checkDepth();
                if (stackDelayRes2 instanceof runtime.EffectSig.class) {
                  stackDelayRes2.tail.next = new Cont$lambda$9.class(42, null);
                  stackDelayRes2.tail = stackDelayRes2.tail.next;
                  return stackDelayRes2
                }
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp1 = globalThis.Error("undefined");
                if (tmp1 instanceof runtime.EffectSig.class) {
                  tmp1.tail.next = new Cont$lambda$9.class(43, null);
                  tmp1.tail = tmp1.tail.next;
                  return tmp1
                }
                tmp1 = runtime.resetDepth(tmp1, curDepth1);
                throw tmp1;
              }, (x1) => {
                return x1
              }, tmp)
            }
            break;
          }
        }
        toString() { return "Cont$func$lookup2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1751_1832$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$func$lookup2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1751_1832$1.class(40, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = lambda.lookup(v, env);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.tail.next = new Cont$func$lookup2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1751_1832$1.class(41, null);
        tmp.tail = tmp.tail.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.myMaybe((dummy) => {
        let tmp1, curDepth1, stackDelayRes2, Cont$lambda$9;
        Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
        Cont$lambda$9.class = class Cont$lambda$3 extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp2;
            tmp2 = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 42) {
              stackDelayRes2 = value$;
            } else if (this.pc === 43) {
              tmp1 = value$;
            }
            contLoop: while (true) {
              if (this.pc === 42) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp1 = globalThis.Error("undefined");
                if (tmp1 instanceof runtime.EffectSig.class) {
                  this.pc = 43;
                  return tmp1
                }
                this.pc = 43;
                continue contLoop;
              } else if (this.pc === 43) {
                tmp1 = runtime.resetDepth(tmp1, curDepth1);
                throw tmp1;
              }
              break;
            }
          }
          toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        curDepth1 = runtime.stackDepth;
        stackDelayRes2 = runtime.checkDepth();
        if (stackDelayRes2 instanceof runtime.EffectSig.class) {
          stackDelayRes2.tail.next = new Cont$lambda$9.class(42, null);
          stackDelayRes2.tail = stackDelayRes2.tail.next;
          return stackDelayRes2
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp1 = globalThis.Error("undefined");
        if (tmp1 instanceof runtime.EffectSig.class) {
          tmp1.tail.next = new Cont$lambda$9.class(43, null);
          tmp1.tail = tmp1.tail.next;
          return tmp1
        }
        tmp1 = runtime.resetDepth(tmp1, curDepth1);
        throw tmp1;
      }, (x1) => {
        return x1
      }, tmp)
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$lookupVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1730_1879$1.class(39, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return lambda.myBind(lambda.#myGet, (env) => {
      let tmp, curDepth, stackDelayRes1, Cont$lambda$9;
      Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
      Cont$lambda$9.class = class Cont$lambda$2 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp1;
          tmp1 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 44) {
            stackDelayRes1 = value$;
          } else if (this.pc === 45) {
            tmp = value$;
          }
          contLoop: while (true) {
            if (this.pc === 44) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = lookup2(env);
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 45;
                return tmp
              }
              this.pc = 45;
              continue contLoop;
            } else if (this.pc === 45) {
              tmp = runtime.resetDepth(tmp, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return lambda.myReturn(tmp)
            }
            break;
          }
        }
        toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$lambda$9.class(44, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = lookup2(env);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.tail.next = new Cont$lambda$9.class(45, null);
        tmp.tail = tmp.tail.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.myReturn(tmp)
    })
  } 
  static withEnv(tmp, m3) {
    let tmp1, curDepth, stackDelayRes, Cont$func$withEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1885_1932$1;
    Cont$func$withEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1885_1932$1 = function Cont$func$withEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1885_1932$(pc1, next1) { return new Cont$func$withEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1885_1932$.class(pc1, next1); };
    Cont$func$withEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1885_1932$1.class = class Cont$func$withEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1885_1932$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp2;
        tmp2 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 46) {
          stackDelayRes = value$;
        } else if (this.pc === 47) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 46) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = lambda.myEvalState(m3, tmp);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 47;
              return tmp1
            }
            this.pc = 47;
            continue contLoop;
          } else if (this.pc === 47) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.myReturn(tmp1)
          }
          break;
        }
      }
      toString() { return "Cont$func$withEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1885_1932$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$withEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1885_1932$1.class(46, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = lambda.myEvalState(m3, tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.tail.next = new Cont$func$withEnv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1885_1932$1.class(47, null);
      tmp1.tail = tmp1.tail.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return lambda.myReturn(tmp1)
  } 
  static pushVar(v1, t1, m4) {
    let stackDelayRes, Cont$func$pushVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1938_2004$1;
    Cont$func$pushVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1938_2004$1 = function Cont$func$pushVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1938_2004$(pc1, next1) { return new Cont$func$pushVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1938_2004$.class(pc1, next1); };
    Cont$func$pushVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1938_2004$1.class = class Cont$func$pushVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1938_2004$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp1;
        tmp1 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 48) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 48) {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.myBind(lambda.#myGet, (env) => {
              let tmp1, curDepth, stackDelayRes1, Cont$lambda$9;
              Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$9.class = class Cont$lambda$4 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp2;
                  tmp2 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 49) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 50) {
                    tmp1 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 49) {
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp1 = NofibPrelude.Cons([
                        v1,
                        t1
                      ], env);
                      if (tmp1 instanceof runtime.EffectSig.class) {
                        this.pc = 50;
                        return tmp1
                      }
                      this.pc = 50;
                      continue contLoop1;
                    } else if (this.pc === 50) {
                      tmp1 = runtime.resetDepth(tmp1, curDepth);
                      runtime.stackDepth = runtime.stackDepth + 1;
                      this.completed = true;
                      return lambda.withEnv(tmp1, m4)
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              curDepth = runtime.stackDepth;
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$9.class(49, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = NofibPrelude.Cons([
                v1,
                t1
              ], env);
              if (tmp1 instanceof runtime.EffectSig.class) {
                tmp1.tail.next = new Cont$lambda$9.class(50, null);
                tmp1.tail = tmp1.tail.next;
                return tmp1
              }
              tmp1 = runtime.resetDepth(tmp1, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              return lambda.withEnv(tmp1, m4)
            })
          }
          break;
        }
      }
      toString() { return "Cont$func$pushVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1938_2004$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$pushVar$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_1938_2004$1.class(48, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return lambda.myBind(lambda.#myGet, (env) => {
      let tmp1, curDepth, stackDelayRes1, Cont$lambda$9;
      Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
      Cont$lambda$9.class = class Cont$lambda$4 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp2;
          tmp2 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 49) {
            stackDelayRes1 = value$;
          } else if (this.pc === 50) {
            tmp1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 49) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = NofibPrelude.Cons([
                v1,
                t1
              ], env);
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 50;
                return tmp1
              }
              this.pc = 50;
              continue contLoop;
            } else if (this.pc === 50) {
              tmp1 = runtime.resetDepth(tmp1, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return lambda.withEnv(tmp1, m4)
            }
            break;
          }
        }
        toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$lambda$9.class(49, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = NofibPrelude.Cons([
        v1,
        t1
      ], env);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.tail.next = new Cont$lambda$9.class(50, null);
        tmp1.tail = tmp1.tail.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.withEnv(tmp1, m4)
    })
  } 
  static traverseTerm(t2) {
    let stackDelayRes, Cont$func$traverseTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2010_2035$1;
    Cont$func$traverseTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2010_2035$1 = function Cont$func$traverseTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2010_2035$(pc1, next1) { return new Cont$func$traverseTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2010_2035$.class(pc1, next1); };
    Cont$func$traverseTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2010_2035$1.class = class Cont$func$traverseTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2010_2035$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp1;
        tmp1 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 51) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 51) {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.eval(t2)
          }
          break;
        }
      }
      toString() { return "Cont$func$traverseTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2010_2035$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$traverseTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2010_2035$1.class(51, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return lambda.eval(t2)
  } 
  static traverseCon(t3) {
    let tmp1, tmp2, curDepth, stackDelayRes, Cont$func$traverseCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2041_2165$1;
    Cont$func$traverseCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2041_2165$1 = function Cont$func$traverseCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2041_2165$(pc1, next1) { return new Cont$func$traverseCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2041_2165$.class(pc1, next1); };
    Cont$func$traverseCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2041_2165$1.class = class Cont$func$traverseCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2041_2165$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp3;
        tmp3 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 52) {
          stackDelayRes = value$;
        } else if (this.pc === 53) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 52) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = lambda.traverseTerm(t3);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 53;
              return tmp1
            }
            this.pc = 53;
            continue contLoop;
          } else if (this.pc === 53) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            tmp2 = (_t) => {
              let param0, c, tmp3, curDepth1, stackDelayRes1, Cont$lambda$9;
              Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$9.class = class Cont$lambda$5 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp4;
                  tmp4 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 54) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 55) {
                    tmp3 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 54) {
                      if (_t instanceof lambda.Con.class) {
                        param0 = _t.i;
                        c = param0;
                        runtime.stackDepth = runtime.stackDepth + 1;
                        this.completed = true;
                        return lambda.myReturn(c)
                      } else {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp3 = globalThis.Error("Not a Con");
                        if (tmp3 instanceof runtime.EffectSig.class) {
                          this.pc = 55;
                          return tmp3
                        }
                        this.pc = 55;
                        continue contLoop1;
                      }
                      this.pc = 56;
                      continue contLoop1;
                    } else if (this.pc === 56) {
                      break contLoop1;
                    } else if (this.pc === 55) {
                      tmp3 = runtime.resetDepth(tmp3, curDepth1);
                      throw tmp3;
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              curDepth1 = runtime.stackDepth;
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$9.class(54, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              if (_t instanceof lambda.Con.class) {
                param0 = _t.i;
                c = param0;
                runtime.stackDepth = runtime.stackDepth + 1;
                return lambda.myReturn(c)
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp3 = globalThis.Error("Not a Con");
                if (tmp3 instanceof runtime.EffectSig.class) {
                  tmp3.tail.next = new Cont$lambda$9.class(55, null);
                  tmp3.tail = tmp3.tail.next;
                  return tmp3
                }
                tmp3 = runtime.resetDepth(tmp3, curDepth1);
                throw tmp3;
              }
            };
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.myBind(tmp1, tmp2)
          }
          break;
        }
      }
      toString() { return "Cont$func$traverseCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2041_2165$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$traverseCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2041_2165$1.class(52, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = lambda.traverseTerm(t3);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.tail.next = new Cont$func$traverseCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2041_2165$1.class(53, null);
      tmp1.tail = tmp1.tail.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    tmp2 = (_t) => {
      let param0, c, tmp3, curDepth1, stackDelayRes1, Cont$lambda$9;
      Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
      Cont$lambda$9.class = class Cont$lambda$5 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp4;
          tmp4 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 54) {
            stackDelayRes1 = value$;
          } else if (this.pc === 55) {
            tmp3 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 54) {
              if (_t instanceof lambda.Con.class) {
                param0 = _t.i;
                c = param0;
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return lambda.myReturn(c)
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp3 = globalThis.Error("Not a Con");
                if (tmp3 instanceof runtime.EffectSig.class) {
                  this.pc = 55;
                  return tmp3
                }
                this.pc = 55;
                continue contLoop;
              }
              this.pc = 56;
              continue contLoop;
            } else if (this.pc === 56) {
              break contLoop;
            } else if (this.pc === 55) {
              tmp3 = runtime.resetDepth(tmp3, curDepth1);
              throw tmp3;
            }
            break;
          }
        }
        toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth1 = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$lambda$9.class(54, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      if (_t instanceof lambda.Con.class) {
        param0 = _t.i;
        c = param0;
        runtime.stackDepth = runtime.stackDepth + 1;
        return lambda.myReturn(c)
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp3 = globalThis.Error("Not a Con");
        if (tmp3 instanceof runtime.EffectSig.class) {
          tmp3.tail.next = new Cont$lambda$9.class(55, null);
          tmp3.tail = tmp3.tail.next;
          return tmp3
        }
        tmp3 = runtime.resetDepth(tmp3, curDepth1);
        throw tmp3;
      }
    };
    runtime.stackDepth = runtime.stackDepth + 1;
    return lambda.myBind(tmp1, tmp2)
  } 
  static apply(t4, a3) {
    let param0, param1, param01, param11, x1, b2, e, tmp1, curDepth, tmp2, stackDelayRes, Cont$func$apply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2171_2310$1;
    Cont$func$apply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2171_2310$1 = function Cont$func$apply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2171_2310$(pc1, next1) { return new Cont$func$apply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2171_2310$.class(pc1, next1); };
    Cont$func$apply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2171_2310$1.class = class Cont$func$apply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2171_2310$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp3;
        tmp3 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 57) {
          stackDelayRes = value$;
        } else if (this.pc === 63) {
          tmp2 = value$;
        } else if (this.pc === 62) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 57) {
            if (t4 instanceof lambda.Thunk.class) {
              param0 = t4.t;
              param1 = t4.e;
              if (param0 instanceof lambda.Lam.class) {
                param01 = param0.s;
                param11 = param0.t;
                x1 = param01;
                b2 = param11;
                e = param1;
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return lambda.myBind(lambda.#myGet, (orig) => {
                  let tmp3, tmp4, tmp5, curDepth1, stackDelayRes1, Cont$lambda$9;
                  Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
                  Cont$lambda$9.class = class Cont$lambda$6 extends runtime.Cont.class {
                    constructor(pc1, next1) {
                      let tmp6;
                      tmp6 = super(next1, false);
                      this.pc = pc1;
                      this.next = next1;
                    }
                    resume(value$1) {
                      if (this.pc === 58) {
                        stackDelayRes1 = value$1;
                      } else if (this.pc === 59) {
                        tmp3 = value$1;
                      } else if (this.pc === 60) {
                        tmp4 = value$1;
                      } else if (this.pc === 61) {
                        tmp5 = value$1;
                      }
                      contLoop1: while (true) {
                        if (this.pc === 58) {
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp3 = lambda.Thunk(a3, orig);
                          if (tmp3 instanceof runtime.EffectSig.class) {
                            this.pc = 59;
                            return tmp3
                          }
                          this.pc = 59;
                          continue contLoop1;
                        } else if (this.pc === 59) {
                          tmp3 = runtime.resetDepth(tmp3, curDepth1);
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp4 = lambda.traverseTerm(b2);
                          if (tmp4 instanceof runtime.EffectSig.class) {
                            this.pc = 60;
                            return tmp4
                          }
                          this.pc = 60;
                          continue contLoop1;
                        } else if (this.pc === 60) {
                          tmp4 = runtime.resetDepth(tmp4, curDepth1);
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp5 = lambda.pushVar(x1, tmp3, tmp4);
                          if (tmp5 instanceof runtime.EffectSig.class) {
                            this.pc = 61;
                            return tmp5
                          }
                          this.pc = 61;
                          continue contLoop1;
                        } else if (this.pc === 61) {
                          tmp5 = runtime.resetDepth(tmp5, curDepth1);
                          runtime.stackDepth = runtime.stackDepth + 1;
                          this.completed = true;
                          return lambda.withEnv(e, tmp5)
                        }
                        break;
                      }
                    }
                    toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
                  };
                  curDepth1 = runtime.stackDepth;
                  stackDelayRes1 = runtime.checkDepth();
                  if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                    stackDelayRes1.tail.next = new Cont$lambda$9.class(58, null);
                    stackDelayRes1.tail = stackDelayRes1.tail.next;
                    return stackDelayRes1
                  }
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp3 = lambda.Thunk(a3, orig);
                  if (tmp3 instanceof runtime.EffectSig.class) {
                    tmp3.tail.next = new Cont$lambda$9.class(59, null);
                    tmp3.tail = tmp3.tail.next;
                    return tmp3
                  }
                  tmp3 = runtime.resetDepth(tmp3, curDepth1);
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp4 = lambda.traverseTerm(b2);
                  if (tmp4 instanceof runtime.EffectSig.class) {
                    tmp4.tail.next = new Cont$lambda$9.class(60, null);
                    tmp4.tail = tmp4.tail.next;
                    return tmp4
                  }
                  tmp4 = runtime.resetDepth(tmp4, curDepth1);
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp5 = lambda.pushVar(x1, tmp3, tmp4);
                  if (tmp5 instanceof runtime.EffectSig.class) {
                    tmp5.tail.next = new Cont$lambda$9.class(61, null);
                    tmp5.tail = tmp5.tail.next;
                    return tmp5
                  }
                  tmp5 = runtime.resetDepth(tmp5, curDepth1);
                  runtime.stackDepth = runtime.stackDepth + 1;
                  return lambda.withEnv(e, tmp5)
                })
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp1 = new globalThis.Error("match error");
                if (tmp1 instanceof runtime.EffectSig.class) {
                  this.pc = 62;
                  return tmp1
                }
                this.pc = 62;
                continue contLoop;
              }
              this.pc = 64;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp2 = new globalThis.Error("match error");
              if (tmp2 instanceof runtime.EffectSig.class) {
                this.pc = 63;
                return tmp2
              }
              this.pc = 63;
              continue contLoop;
            }
            this.pc = 64;
            continue contLoop;
          } else if (this.pc === 64) {
            break contLoop;
          } else if (this.pc === 63) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            throw tmp2;
          } else if (this.pc === 62) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            throw tmp1;
          }
          break;
        }
      }
      toString() { return "Cont$func$apply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2171_2310$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$apply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2171_2310$1.class(57, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (t4 instanceof lambda.Thunk.class) {
      param0 = t4.t;
      param1 = t4.e;
      if (param0 instanceof lambda.Lam.class) {
        param01 = param0.s;
        param11 = param0.t;
        x1 = param01;
        b2 = param11;
        e = param1;
        runtime.stackDepth = runtime.stackDepth + 1;
        return lambda.myBind(lambda.#myGet, (orig) => {
          let tmp3, tmp4, tmp5, curDepth1, stackDelayRes1, Cont$lambda$9;
          Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
          Cont$lambda$9.class = class Cont$lambda$6 extends runtime.Cont.class {
            constructor(pc, next) {
              let tmp6;
              tmp6 = super(next, false);
              this.pc = pc;
              this.next = next;
            }
            resume(value$) {
              if (this.pc === 58) {
                stackDelayRes1 = value$;
              } else if (this.pc === 59) {
                tmp3 = value$;
              } else if (this.pc === 60) {
                tmp4 = value$;
              } else if (this.pc === 61) {
                tmp5 = value$;
              }
              contLoop: while (true) {
                if (this.pc === 58) {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp3 = lambda.Thunk(a3, orig);
                  if (tmp3 instanceof runtime.EffectSig.class) {
                    this.pc = 59;
                    return tmp3
                  }
                  this.pc = 59;
                  continue contLoop;
                } else if (this.pc === 59) {
                  tmp3 = runtime.resetDepth(tmp3, curDepth1);
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp4 = lambda.traverseTerm(b2);
                  if (tmp4 instanceof runtime.EffectSig.class) {
                    this.pc = 60;
                    return tmp4
                  }
                  this.pc = 60;
                  continue contLoop;
                } else if (this.pc === 60) {
                  tmp4 = runtime.resetDepth(tmp4, curDepth1);
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp5 = lambda.pushVar(x1, tmp3, tmp4);
                  if (tmp5 instanceof runtime.EffectSig.class) {
                    this.pc = 61;
                    return tmp5
                  }
                  this.pc = 61;
                  continue contLoop;
                } else if (this.pc === 61) {
                  tmp5 = runtime.resetDepth(tmp5, curDepth1);
                  runtime.stackDepth = runtime.stackDepth + 1;
                  this.completed = true;
                  return lambda.withEnv(e, tmp5)
                }
                break;
              }
            }
            toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
          };
          curDepth1 = runtime.stackDepth;
          stackDelayRes1 = runtime.checkDepth();
          if (stackDelayRes1 instanceof runtime.EffectSig.class) {
            stackDelayRes1.tail.next = new Cont$lambda$9.class(58, null);
            stackDelayRes1.tail = stackDelayRes1.tail.next;
            return stackDelayRes1
          }
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp3 = lambda.Thunk(a3, orig);
          if (tmp3 instanceof runtime.EffectSig.class) {
            tmp3.tail.next = new Cont$lambda$9.class(59, null);
            tmp3.tail = tmp3.tail.next;
            return tmp3
          }
          tmp3 = runtime.resetDepth(tmp3, curDepth1);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp4 = lambda.traverseTerm(b2);
          if (tmp4 instanceof runtime.EffectSig.class) {
            tmp4.tail.next = new Cont$lambda$9.class(60, null);
            tmp4.tail = tmp4.tail.next;
            return tmp4
          }
          tmp4 = runtime.resetDepth(tmp4, curDepth1);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp5 = lambda.pushVar(x1, tmp3, tmp4);
          if (tmp5 instanceof runtime.EffectSig.class) {
            tmp5.tail.next = new Cont$lambda$9.class(61, null);
            tmp5.tail = tmp5.tail.next;
            return tmp5
          }
          tmp5 = runtime.resetDepth(tmp5, curDepth1);
          runtime.stackDepth = runtime.stackDepth + 1;
          return lambda.withEnv(e, tmp5)
        })
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp1 = new globalThis.Error("match error");
        if (tmp1 instanceof runtime.EffectSig.class) {
          tmp1.tail.next = new Cont$func$apply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2171_2310$1.class(62, null);
          tmp1.tail = tmp1.tail.next;
          return tmp1
        }
        tmp1 = runtime.resetDepth(tmp1, curDepth);
        throw tmp1;
      }
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = new globalThis.Error("match error");
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.tail.next = new Cont$func$apply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2171_2310$1.class(63, null);
        tmp2.tail = tmp2.tail.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      throw tmp2;
    }
  } 
  static eval(ter) {
    let param0, i, param01, param1, param2, c, a4, b2, param02, param11, u, v2, param03, param12, x1, b3, param04, param13, t5, e, param05, param14, u1, v3, param06, x2, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, curDepth, tmp7, stackDelayRes, Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$1;
    Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$1 = function Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$(pc1, next1) { return new Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$.class(pc1, next1); };
    Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$1.class = class Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp8;
        tmp8 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 65) {
          stackDelayRes = value$;
        } else if (this.pc === 88) {
          tmp7 = value$;
        } else if (this.pc === 85) {
          tmp6 = value$;
        } else if (this.pc === 80) {
          tmp4 = value$;
        } else if (this.pc === 78) {
          tmp3 = value$;
        } else if (this.pc === 74) {
          tmp2 = value$;
        } else if (this.pc === 69) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 65) {
            if (ter instanceof lambda.Var.class) {
              param06 = ter.s;
              x2 = param06;
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return lambda.myBind(lambda.#myGet, (e1) => {
                let tmp8, curDepth1, stackDelayRes1, Cont$lambda$9;
                Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
                Cont$lambda$9.class = class Cont$lambda$13 extends runtime.Cont.class {
                  constructor(pc1, next1) {
                    let tmp9;
                    tmp9 = super(next1, false);
                    this.pc = pc1;
                    this.next = next1;
                  }
                  resume(value$1) {
                    if (this.pc === 66) {
                      stackDelayRes1 = value$1;
                    } else if (this.pc === 67) {
                      tmp8 = value$1;
                    }
                    contLoop1: while (true) {
                      if (this.pc === 66) {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp8 = lambda.lookupVar(x2);
                        if (tmp8 instanceof runtime.EffectSig.class) {
                          this.pc = 67;
                          return tmp8
                        }
                        this.pc = 67;
                        continue contLoop1;
                      } else if (this.pc === 67) {
                        tmp8 = runtime.resetDepth(tmp8, curDepth1);
                        runtime.stackDepth = runtime.stackDepth + 1;
                        this.completed = true;
                        return lambda.myBind(tmp8, (t6) => {
                          let stackDelayRes2, Cont$lambda$17;
                          Cont$lambda$17 = function Cont$lambda$(pc3, next3) { return new Cont$lambda$.class(pc3, next3); };
                          Cont$lambda$17.class = class Cont$lambda$8 extends runtime.Cont.class {
                            constructor(pc2, next2) {
                              let tmp9;
                              tmp9 = super(next2, false);
                              this.pc = pc2;
                              this.next = next2;
                            }
                            resume(value$2) {
                              if (this.pc === 68) {
                                stackDelayRes2 = value$2;
                              }
                              contLoop2: while (true) {
                                if (this.pc === 68) {
                                  runtime.stackDepth = runtime.stackDepth + 1;
                                  this.completed = true;
                                  return lambda.traverseTerm(t6)
                                }
                                break;
                              }
                            }
                            toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
                          };
                          stackDelayRes2 = runtime.checkDepth();
                          if (stackDelayRes2 instanceof runtime.EffectSig.class) {
                            stackDelayRes2.tail.next = new Cont$lambda$17.class(68, null);
                            stackDelayRes2.tail = stackDelayRes2.tail.next;
                            return stackDelayRes2
                          }
                          runtime.stackDepth = runtime.stackDepth + 1;
                          return lambda.traverseTerm(t6)
                        })
                      }
                      break;
                    }
                  }
                  toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
                };
                curDepth1 = runtime.stackDepth;
                stackDelayRes1 = runtime.checkDepth();
                if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                  stackDelayRes1.tail.next = new Cont$lambda$9.class(66, null);
                  stackDelayRes1.tail = stackDelayRes1.tail.next;
                  return stackDelayRes1
                }
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp8 = lambda.lookupVar(x2);
                if (tmp8 instanceof runtime.EffectSig.class) {
                  tmp8.tail.next = new Cont$lambda$9.class(67, null);
                  tmp8.tail = tmp8.tail.next;
                  return tmp8
                }
                tmp8 = runtime.resetDepth(tmp8, curDepth1);
                runtime.stackDepth = runtime.stackDepth + 1;
                return lambda.myBind(tmp8, (t6) => {
                  let stackDelayRes2, Cont$lambda$17;
                  Cont$lambda$17 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
                  Cont$lambda$17.class = class Cont$lambda$8 extends runtime.Cont.class {
                    constructor(pc1, next1) {
                      let tmp9;
                      tmp9 = super(next1, false);
                      this.pc = pc1;
                      this.next = next1;
                    }
                    resume(value$1) {
                      if (this.pc === 68) {
                        stackDelayRes2 = value$1;
                      }
                      contLoop1: while (true) {
                        if (this.pc === 68) {
                          runtime.stackDepth = runtime.stackDepth + 1;
                          this.completed = true;
                          return lambda.traverseTerm(t6)
                        }
                        break;
                      }
                    }
                    toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
                  };
                  stackDelayRes2 = runtime.checkDepth();
                  if (stackDelayRes2 instanceof runtime.EffectSig.class) {
                    stackDelayRes2.tail.next = new Cont$lambda$17.class(68, null);
                    stackDelayRes2.tail = stackDelayRes2.tail.next;
                    return stackDelayRes2
                  }
                  runtime.stackDepth = runtime.stackDepth + 1;
                  return lambda.traverseTerm(t6)
                })
              })
            } else if (ter instanceof lambda.Add.class) {
              param05 = ter.a;
              param14 = ter.b;
              u1 = param05;
              v3 = param14;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = lambda.traverseCon(u1);
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 69;
                return tmp1
              }
              this.pc = 69;
              continue contLoop;
              this.pc = 89;
              continue contLoop;
            } else if (ter instanceof lambda.Thunk.class) {
              param04 = ter.t;
              param13 = ter.e;
              t5 = param04;
              e = param13;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp2 = lambda.traverseTerm(t5);
              if (tmp2 instanceof runtime.EffectSig.class) {
                this.pc = 74;
                return tmp2
              }
              this.pc = 74;
              continue contLoop;
              this.pc = 89;
              continue contLoop;
              this.pc = 89;
              continue contLoop;
            } else {
              if (ter instanceof lambda.Lam.class) {
                param03 = ter.s;
                param12 = ter.t;
                x1 = param03;
                b3 = param12;
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return lambda.myBind(lambda.#myGet, (env) => {
                  let tmp8, tmp9, curDepth1, stackDelayRes1, Cont$lambda$9;
                  Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
                  Cont$lambda$9.class = class Cont$lambda$12 extends runtime.Cont.class {
                    constructor(pc1, next1) {
                      let tmp10;
                      tmp10 = super(next1, false);
                      this.pc = pc1;
                      this.next = next1;
                    }
                    resume(value$1) {
                      if (this.pc === 75) {
                        stackDelayRes1 = value$1;
                      } else if (this.pc === 76) {
                        tmp8 = value$1;
                      } else if (this.pc === 77) {
                        tmp9 = value$1;
                      }
                      contLoop1: while (true) {
                        if (this.pc === 75) {
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp8 = lambda.Lam(x1, b3);
                          if (tmp8 instanceof runtime.EffectSig.class) {
                            this.pc = 76;
                            return tmp8
                          }
                          this.pc = 76;
                          continue contLoop1;
                        } else if (this.pc === 76) {
                          tmp8 = runtime.resetDepth(tmp8, curDepth1);
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp9 = lambda.Thunk(tmp8, env);
                          if (tmp9 instanceof runtime.EffectSig.class) {
                            this.pc = 77;
                            return tmp9
                          }
                          this.pc = 77;
                          continue contLoop1;
                        } else if (this.pc === 77) {
                          tmp9 = runtime.resetDepth(tmp9, curDepth1);
                          runtime.stackDepth = runtime.stackDepth + 1;
                          this.completed = true;
                          return lambda.myReturn(tmp9)
                        }
                        break;
                      }
                    }
                    toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
                  };
                  curDepth1 = runtime.stackDepth;
                  stackDelayRes1 = runtime.checkDepth();
                  if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                    stackDelayRes1.tail.next = new Cont$lambda$9.class(75, null);
                    stackDelayRes1.tail = stackDelayRes1.tail.next;
                    return stackDelayRes1
                  }
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp8 = lambda.Lam(x1, b3);
                  if (tmp8 instanceof runtime.EffectSig.class) {
                    tmp8.tail.next = new Cont$lambda$9.class(76, null);
                    tmp8.tail = tmp8.tail.next;
                    return tmp8
                  }
                  tmp8 = runtime.resetDepth(tmp8, curDepth1);
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp9 = lambda.Thunk(tmp8, env);
                  if (tmp9 instanceof runtime.EffectSig.class) {
                    tmp9.tail.next = new Cont$lambda$9.class(77, null);
                    tmp9.tail = tmp9.tail.next;
                    return tmp9
                  }
                  tmp9 = runtime.resetDepth(tmp9, curDepth1);
                  runtime.stackDepth = runtime.stackDepth + 1;
                  return lambda.myReturn(tmp9)
                })
              } else if (ter instanceof lambda.App.class) {
                param02 = ter.a;
                param11 = ter.b;
                u = param02;
                v2 = param11;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp3 = lambda.traverseTerm(u);
                if (tmp3 instanceof runtime.EffectSig.class) {
                  this.pc = 78;
                  return tmp3
                }
                this.pc = 78;
                continue contLoop;
                this.pc = 89;
                continue contLoop;
              } else if (ter instanceof lambda.IfZero.class) {
                param01 = ter.a;
                param1 = ter.b;
                param2 = ter.c;
                c = param01;
                a4 = param1;
                b2 = param2;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp4 = lambda.traverseTerm(c);
                if (tmp4 instanceof runtime.EffectSig.class) {
                  this.pc = 80;
                  return tmp4
                }
                this.pc = 80;
                continue contLoop;
                this.pc = 89;
                continue contLoop;
                this.pc = 89;
                continue contLoop;
              } else if (ter instanceof lambda.Con.class) {
                param0 = ter.i;
                i = param0;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp6 = lambda.Con(i);
                if (tmp6 instanceof runtime.EffectSig.class) {
                  this.pc = 85;
                  return tmp6
                }
                this.pc = 85;
                continue contLoop;
                this.pc = 89;
                continue contLoop;
                this.pc = 89;
                continue contLoop;
                this.pc = 89;
                continue contLoop;
              } else if (ter instanceof lambda.Incr.class) {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return lambda.myBind(lambda.#incr, (_dummy) => {
                  let tmp8, curDepth1, stackDelayRes1, Cont$lambda$9;
                  Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
                  Cont$lambda$9.class = class Cont$lambda$10 extends runtime.Cont.class {
                    constructor(pc1, next1) {
                      let tmp9;
                      tmp9 = super(next1, false);
                      this.pc = pc1;
                      this.next = next1;
                    }
                    resume(value$1) {
                      if (this.pc === 86) {
                        stackDelayRes1 = value$1;
                      } else if (this.pc === 87) {
                        tmp8 = value$1;
                      }
                      contLoop1: while (true) {
                        if (this.pc === 86) {
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp8 = lambda.Con(0);
                          if (tmp8 instanceof runtime.EffectSig.class) {
                            this.pc = 87;
                            return tmp8
                          }
                          this.pc = 87;
                          continue contLoop1;
                        } else if (this.pc === 87) {
                          tmp8 = runtime.resetDepth(tmp8, curDepth1);
                          runtime.stackDepth = runtime.stackDepth + 1;
                          this.completed = true;
                          return lambda.myReturn(tmp8)
                        }
                        break;
                      }
                    }
                    toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
                  };
                  curDepth1 = runtime.stackDepth;
                  stackDelayRes1 = runtime.checkDepth();
                  if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                    stackDelayRes1.tail.next = new Cont$lambda$9.class(86, null);
                    stackDelayRes1.tail = stackDelayRes1.tail.next;
                    return stackDelayRes1
                  }
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp8 = lambda.Con(0);
                  if (tmp8 instanceof runtime.EffectSig.class) {
                    tmp8.tail.next = new Cont$lambda$9.class(87, null);
                    tmp8.tail = tmp8.tail.next;
                    return tmp8
                  }
                  tmp8 = runtime.resetDepth(tmp8, curDepth1);
                  runtime.stackDepth = runtime.stackDepth + 1;
                  return lambda.myReturn(tmp8)
                });
                this.pc = 89;
                continue contLoop;
                this.pc = 89;
                continue contLoop;
                this.pc = 89;
                continue contLoop;
                this.pc = 89;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp7 = new globalThis.Error("match error");
                if (tmp7 instanceof runtime.EffectSig.class) {
                  this.pc = 88;
                  return tmp7
                }
                this.pc = 88;
                continue contLoop;
              }
              this.pc = 89;
              continue contLoop;
            }
            this.pc = 89;
            continue contLoop;
          } else if (this.pc === 89) {
            break contLoop;
          } else if (this.pc === 88) {
            tmp7 = runtime.resetDepth(tmp7, curDepth);
            throw tmp7;
          } else if (this.pc === 85) {
            tmp6 = runtime.resetDepth(tmp6, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.myReturn(tmp6)
          } else if (this.pc === 80) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            tmp5 = (vall) => {
              let scrut, tmp8, curDepth1, stackDelayRes1, Cont$lambda$9;
              Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$9.class = class Cont$lambda$11 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp9;
                  tmp9 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 81) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 82) {
                    tmp8 = value$1;
                  } else if (this.pc === 83) {
                    scrut = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 81) {
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp8 = lambda.Con(0);
                      if (tmp8 instanceof runtime.EffectSig.class) {
                        this.pc = 82;
                        return tmp8
                      }
                      this.pc = 82;
                      continue contLoop1;
                    } else if (this.pc === 82) {
                      tmp8 = runtime.resetDepth(tmp8, curDepth1);
                      runtime.stackDepth = runtime.stackDepth + 1;
                      scrut = lambda.eqTerm(vall, tmp8);
                      if (scrut instanceof runtime.EffectSig.class) {
                        this.pc = 83;
                        return scrut
                      }
                      this.pc = 83;
                      continue contLoop1;
                    } else if (this.pc === 83) {
                      scrut = runtime.resetDepth(scrut, curDepth1);
                      if (scrut === true) {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        this.completed = true;
                        return lambda.traverseTerm(a4)
                      } else {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        this.completed = true;
                        return lambda.traverseTerm(b2)
                      }
                      this.pc = 84;
                      continue contLoop1;
                    } else if (this.pc === 84) {
                      break contLoop1;
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              curDepth1 = runtime.stackDepth;
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$9.class(81, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp8 = lambda.Con(0);
              if (tmp8 instanceof runtime.EffectSig.class) {
                tmp8.tail.next = new Cont$lambda$9.class(82, null);
                tmp8.tail = tmp8.tail.next;
                return tmp8
              }
              tmp8 = runtime.resetDepth(tmp8, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              scrut = lambda.eqTerm(vall, tmp8);
              if (scrut instanceof runtime.EffectSig.class) {
                scrut.tail.next = new Cont$lambda$9.class(83, null);
                scrut.tail = scrut.tail.next;
                return scrut
              }
              scrut = runtime.resetDepth(scrut, curDepth1);
              if (scrut === true) {
                runtime.stackDepth = runtime.stackDepth + 1;
                return lambda.traverseTerm(a4)
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                return lambda.traverseTerm(b2)
              }
            };
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.myBind(tmp4, tmp5)
          } else if (this.pc === 78) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.myBind(tmp3, (u_) => {
              let stackDelayRes1, Cont$lambda$9;
              Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$9.class = class Cont$lambda$7 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp8;
                  tmp8 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 79) {
                    stackDelayRes1 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 79) {
                      runtime.stackDepth = runtime.stackDepth + 1;
                      this.completed = true;
                      return lambda.apply(u_, v2)
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$9.class(79, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              runtime.stackDepth = runtime.stackDepth + 1;
              return lambda.apply(u_, v2)
            })
          } else if (this.pc === 74) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.withEnv(e, tmp2)
          } else if (this.pc === 69) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.myBind(tmp1, (u_) => {
              let tmp8, curDepth1, stackDelayRes1, Cont$lambda$9;
              Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$9.class = class Cont$lambda$ extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp9;
                  tmp9 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 70) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 71) {
                    tmp8 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 70) {
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp8 = lambda.traverseCon(v3);
                      if (tmp8 instanceof runtime.EffectSig.class) {
                        this.pc = 71;
                        return tmp8
                      }
                      this.pc = 71;
                      continue contLoop1;
                    } else if (this.pc === 71) {
                      tmp8 = runtime.resetDepth(tmp8, curDepth1);
                      runtime.stackDepth = runtime.stackDepth + 1;
                      this.completed = true;
                      return lambda.myBind(tmp8, (v_) => {
                        let tmp9, tmp10, curDepth2, stackDelayRes2, Cont$lambda$17;
                        Cont$lambda$17 = function Cont$lambda$(pc3, next3) { return new Cont$lambda$.class(pc3, next3); };
                        Cont$lambda$17.class = class Cont$lambda$14 extends runtime.Cont.class {
                          constructor(pc2, next2) {
                            let tmp11;
                            tmp11 = super(next2, false);
                            this.pc = pc2;
                            this.next = next2;
                          }
                          resume(value$2) {
                            if (this.pc === 72) {
                              stackDelayRes2 = value$2;
                            } else if (this.pc === 73) {
                              tmp10 = value$2;
                            }
                            contLoop2: while (true) {
                              if (this.pc === 72) {
                                tmp9 = u_ + v_;
                                runtime.stackDepth = runtime.stackDepth + 1;
                                tmp10 = lambda.Con(tmp9);
                                if (tmp10 instanceof runtime.EffectSig.class) {
                                  this.pc = 73;
                                  return tmp10
                                }
                                this.pc = 73;
                                continue contLoop2;
                              } else if (this.pc === 73) {
                                tmp10 = runtime.resetDepth(tmp10, curDepth2);
                                runtime.stackDepth = runtime.stackDepth + 1;
                                this.completed = true;
                                return lambda.myReturn(tmp10)
                              }
                              break;
                            }
                          }
                          toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
                        };
                        curDepth2 = runtime.stackDepth;
                        stackDelayRes2 = runtime.checkDepth();
                        if (stackDelayRes2 instanceof runtime.EffectSig.class) {
                          stackDelayRes2.tail.next = new Cont$lambda$17.class(72, null);
                          stackDelayRes2.tail = stackDelayRes2.tail.next;
                          return stackDelayRes2
                        }
                        tmp9 = u_ + v_;
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp10 = lambda.Con(tmp9);
                        if (tmp10 instanceof runtime.EffectSig.class) {
                          tmp10.tail.next = new Cont$lambda$17.class(73, null);
                          tmp10.tail = tmp10.tail.next;
                          return tmp10
                        }
                        tmp10 = runtime.resetDepth(tmp10, curDepth2);
                        runtime.stackDepth = runtime.stackDepth + 1;
                        return lambda.myReturn(tmp10)
                      })
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              curDepth1 = runtime.stackDepth;
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$9.class(70, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp8 = lambda.traverseCon(v3);
              if (tmp8 instanceof runtime.EffectSig.class) {
                tmp8.tail.next = new Cont$lambda$9.class(71, null);
                tmp8.tail = tmp8.tail.next;
                return tmp8
              }
              tmp8 = runtime.resetDepth(tmp8, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              return lambda.myBind(tmp8, (v_) => {
                let tmp9, tmp10, curDepth2, stackDelayRes2, Cont$lambda$17;
                Cont$lambda$17 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
                Cont$lambda$17.class = class Cont$lambda$14 extends runtime.Cont.class {
                  constructor(pc1, next1) {
                    let tmp11;
                    tmp11 = super(next1, false);
                    this.pc = pc1;
                    this.next = next1;
                  }
                  resume(value$1) {
                    if (this.pc === 72) {
                      stackDelayRes2 = value$1;
                    } else if (this.pc === 73) {
                      tmp10 = value$1;
                    }
                    contLoop1: while (true) {
                      if (this.pc === 72) {
                        tmp9 = u_ + v_;
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp10 = lambda.Con(tmp9);
                        if (tmp10 instanceof runtime.EffectSig.class) {
                          this.pc = 73;
                          return tmp10
                        }
                        this.pc = 73;
                        continue contLoop1;
                      } else if (this.pc === 73) {
                        tmp10 = runtime.resetDepth(tmp10, curDepth2);
                        runtime.stackDepth = runtime.stackDepth + 1;
                        this.completed = true;
                        return lambda.myReturn(tmp10)
                      }
                      break;
                    }
                  }
                  toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
                };
                curDepth2 = runtime.stackDepth;
                stackDelayRes2 = runtime.checkDepth();
                if (stackDelayRes2 instanceof runtime.EffectSig.class) {
                  stackDelayRes2.tail.next = new Cont$lambda$17.class(72, null);
                  stackDelayRes2.tail = stackDelayRes2.tail.next;
                  return stackDelayRes2
                }
                tmp9 = u_ + v_;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp10 = lambda.Con(tmp9);
                if (tmp10 instanceof runtime.EffectSig.class) {
                  tmp10.tail.next = new Cont$lambda$17.class(73, null);
                  tmp10.tail = tmp10.tail.next;
                  return tmp10
                }
                tmp10 = runtime.resetDepth(tmp10, curDepth2);
                runtime.stackDepth = runtime.stackDepth + 1;
                return lambda.myReturn(tmp10)
              })
            })
          }
          break;
        }
      }
      toString() { return "Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$1.class(65, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (ter instanceof lambda.Var.class) {
      param06 = ter.s;
      x2 = param06;
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.myBind(lambda.#myGet, (e1) => {
        let tmp8, curDepth1, stackDelayRes1, Cont$lambda$9;
        Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
        Cont$lambda$9.class = class Cont$lambda$13 extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp9;
            tmp9 = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 66) {
              stackDelayRes1 = value$;
            } else if (this.pc === 67) {
              tmp8 = value$;
            }
            contLoop: while (true) {
              if (this.pc === 66) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp8 = lambda.lookupVar(x2);
                if (tmp8 instanceof runtime.EffectSig.class) {
                  this.pc = 67;
                  return tmp8
                }
                this.pc = 67;
                continue contLoop;
              } else if (this.pc === 67) {
                tmp8 = runtime.resetDepth(tmp8, curDepth1);
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return lambda.myBind(tmp8, (t6) => {
                  let stackDelayRes2, Cont$lambda$17;
                  Cont$lambda$17 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
                  Cont$lambda$17.class = class Cont$lambda$8 extends runtime.Cont.class {
                    constructor(pc1, next1) {
                      let tmp9;
                      tmp9 = super(next1, false);
                      this.pc = pc1;
                      this.next = next1;
                    }
                    resume(value$1) {
                      if (this.pc === 68) {
                        stackDelayRes2 = value$1;
                      }
                      contLoop1: while (true) {
                        if (this.pc === 68) {
                          runtime.stackDepth = runtime.stackDepth + 1;
                          this.completed = true;
                          return lambda.traverseTerm(t6)
                        }
                        break;
                      }
                    }
                    toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
                  };
                  stackDelayRes2 = runtime.checkDepth();
                  if (stackDelayRes2 instanceof runtime.EffectSig.class) {
                    stackDelayRes2.tail.next = new Cont$lambda$17.class(68, null);
                    stackDelayRes2.tail = stackDelayRes2.tail.next;
                    return stackDelayRes2
                  }
                  runtime.stackDepth = runtime.stackDepth + 1;
                  return lambda.traverseTerm(t6)
                })
              }
              break;
            }
          }
          toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        curDepth1 = runtime.stackDepth;
        stackDelayRes1 = runtime.checkDepth();
        if (stackDelayRes1 instanceof runtime.EffectSig.class) {
          stackDelayRes1.tail.next = new Cont$lambda$9.class(66, null);
          stackDelayRes1.tail = stackDelayRes1.tail.next;
          return stackDelayRes1
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp8 = lambda.lookupVar(x2);
        if (tmp8 instanceof runtime.EffectSig.class) {
          tmp8.tail.next = new Cont$lambda$9.class(67, null);
          tmp8.tail = tmp8.tail.next;
          return tmp8
        }
        tmp8 = runtime.resetDepth(tmp8, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        return lambda.myBind(tmp8, (t6) => {
          let stackDelayRes2, Cont$lambda$17;
          Cont$lambda$17 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
          Cont$lambda$17.class = class Cont$lambda$8 extends runtime.Cont.class {
            constructor(pc, next) {
              let tmp9;
              tmp9 = super(next, false);
              this.pc = pc;
              this.next = next;
            }
            resume(value$) {
              if (this.pc === 68) {
                stackDelayRes2 = value$;
              }
              contLoop: while (true) {
                if (this.pc === 68) {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  this.completed = true;
                  return lambda.traverseTerm(t6)
                }
                break;
              }
            }
            toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
          };
          stackDelayRes2 = runtime.checkDepth();
          if (stackDelayRes2 instanceof runtime.EffectSig.class) {
            stackDelayRes2.tail.next = new Cont$lambda$17.class(68, null);
            stackDelayRes2.tail = stackDelayRes2.tail.next;
            return stackDelayRes2
          }
          runtime.stackDepth = runtime.stackDepth + 1;
          return lambda.traverseTerm(t6)
        })
      })
    } else if (ter instanceof lambda.Add.class) {
      param05 = ter.a;
      param14 = ter.b;
      u1 = param05;
      v3 = param14;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = lambda.traverseCon(u1);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.tail.next = new Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$1.class(69, null);
        tmp1.tail = tmp1.tail.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.myBind(tmp1, (u_) => {
        let tmp8, curDepth1, stackDelayRes1, Cont$lambda$9;
        Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
        Cont$lambda$9.class = class Cont$lambda$ extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp9;
            tmp9 = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 70) {
              stackDelayRes1 = value$;
            } else if (this.pc === 71) {
              tmp8 = value$;
            }
            contLoop: while (true) {
              if (this.pc === 70) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp8 = lambda.traverseCon(v3);
                if (tmp8 instanceof runtime.EffectSig.class) {
                  this.pc = 71;
                  return tmp8
                }
                this.pc = 71;
                continue contLoop;
              } else if (this.pc === 71) {
                tmp8 = runtime.resetDepth(tmp8, curDepth1);
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return lambda.myBind(tmp8, (v_) => {
                  let tmp9, tmp10, curDepth2, stackDelayRes2, Cont$lambda$17;
                  Cont$lambda$17 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
                  Cont$lambda$17.class = class Cont$lambda$14 extends runtime.Cont.class {
                    constructor(pc1, next1) {
                      let tmp11;
                      tmp11 = super(next1, false);
                      this.pc = pc1;
                      this.next = next1;
                    }
                    resume(value$1) {
                      if (this.pc === 72) {
                        stackDelayRes2 = value$1;
                      } else if (this.pc === 73) {
                        tmp10 = value$1;
                      }
                      contLoop1: while (true) {
                        if (this.pc === 72) {
                          tmp9 = u_ + v_;
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp10 = lambda.Con(tmp9);
                          if (tmp10 instanceof runtime.EffectSig.class) {
                            this.pc = 73;
                            return tmp10
                          }
                          this.pc = 73;
                          continue contLoop1;
                        } else if (this.pc === 73) {
                          tmp10 = runtime.resetDepth(tmp10, curDepth2);
                          runtime.stackDepth = runtime.stackDepth + 1;
                          this.completed = true;
                          return lambda.myReturn(tmp10)
                        }
                        break;
                      }
                    }
                    toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
                  };
                  curDepth2 = runtime.stackDepth;
                  stackDelayRes2 = runtime.checkDepth();
                  if (stackDelayRes2 instanceof runtime.EffectSig.class) {
                    stackDelayRes2.tail.next = new Cont$lambda$17.class(72, null);
                    stackDelayRes2.tail = stackDelayRes2.tail.next;
                    return stackDelayRes2
                  }
                  tmp9 = u_ + v_;
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp10 = lambda.Con(tmp9);
                  if (tmp10 instanceof runtime.EffectSig.class) {
                    tmp10.tail.next = new Cont$lambda$17.class(73, null);
                    tmp10.tail = tmp10.tail.next;
                    return tmp10
                  }
                  tmp10 = runtime.resetDepth(tmp10, curDepth2);
                  runtime.stackDepth = runtime.stackDepth + 1;
                  return lambda.myReturn(tmp10)
                })
              }
              break;
            }
          }
          toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        curDepth1 = runtime.stackDepth;
        stackDelayRes1 = runtime.checkDepth();
        if (stackDelayRes1 instanceof runtime.EffectSig.class) {
          stackDelayRes1.tail.next = new Cont$lambda$9.class(70, null);
          stackDelayRes1.tail = stackDelayRes1.tail.next;
          return stackDelayRes1
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp8 = lambda.traverseCon(v3);
        if (tmp8 instanceof runtime.EffectSig.class) {
          tmp8.tail.next = new Cont$lambda$9.class(71, null);
          tmp8.tail = tmp8.tail.next;
          return tmp8
        }
        tmp8 = runtime.resetDepth(tmp8, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        return lambda.myBind(tmp8, (v_) => {
          let tmp9, tmp10, curDepth2, stackDelayRes2, Cont$lambda$17;
          Cont$lambda$17 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
          Cont$lambda$17.class = class Cont$lambda$14 extends runtime.Cont.class {
            constructor(pc, next) {
              let tmp11;
              tmp11 = super(next, false);
              this.pc = pc;
              this.next = next;
            }
            resume(value$) {
              if (this.pc === 72) {
                stackDelayRes2 = value$;
              } else if (this.pc === 73) {
                tmp10 = value$;
              }
              contLoop: while (true) {
                if (this.pc === 72) {
                  tmp9 = u_ + v_;
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp10 = lambda.Con(tmp9);
                  if (tmp10 instanceof runtime.EffectSig.class) {
                    this.pc = 73;
                    return tmp10
                  }
                  this.pc = 73;
                  continue contLoop;
                } else if (this.pc === 73) {
                  tmp10 = runtime.resetDepth(tmp10, curDepth2);
                  runtime.stackDepth = runtime.stackDepth + 1;
                  this.completed = true;
                  return lambda.myReturn(tmp10)
                }
                break;
              }
            }
            toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
          };
          curDepth2 = runtime.stackDepth;
          stackDelayRes2 = runtime.checkDepth();
          if (stackDelayRes2 instanceof runtime.EffectSig.class) {
            stackDelayRes2.tail.next = new Cont$lambda$17.class(72, null);
            stackDelayRes2.tail = stackDelayRes2.tail.next;
            return stackDelayRes2
          }
          tmp9 = u_ + v_;
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp10 = lambda.Con(tmp9);
          if (tmp10 instanceof runtime.EffectSig.class) {
            tmp10.tail.next = new Cont$lambda$17.class(73, null);
            tmp10.tail = tmp10.tail.next;
            return tmp10
          }
          tmp10 = runtime.resetDepth(tmp10, curDepth2);
          runtime.stackDepth = runtime.stackDepth + 1;
          return lambda.myReturn(tmp10)
        })
      })
    } else if (ter instanceof lambda.Thunk.class) {
      param04 = ter.t;
      param13 = ter.e;
      t5 = param04;
      e = param13;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = lambda.traverseTerm(t5);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.tail.next = new Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$1.class(74, null);
        tmp2.tail = tmp2.tail.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.withEnv(e, tmp2)
    } else if (ter instanceof lambda.Lam.class) {
      param03 = ter.s;
      param12 = ter.t;
      x1 = param03;
      b3 = param12;
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.myBind(lambda.#myGet, (env) => {
        let tmp8, tmp9, curDepth1, stackDelayRes1, Cont$lambda$9;
        Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
        Cont$lambda$9.class = class Cont$lambda$12 extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp10;
            tmp10 = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 75) {
              stackDelayRes1 = value$;
            } else if (this.pc === 76) {
              tmp8 = value$;
            } else if (this.pc === 77) {
              tmp9 = value$;
            }
            contLoop: while (true) {
              if (this.pc === 75) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp8 = lambda.Lam(x1, b3);
                if (tmp8 instanceof runtime.EffectSig.class) {
                  this.pc = 76;
                  return tmp8
                }
                this.pc = 76;
                continue contLoop;
              } else if (this.pc === 76) {
                tmp8 = runtime.resetDepth(tmp8, curDepth1);
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp9 = lambda.Thunk(tmp8, env);
                if (tmp9 instanceof runtime.EffectSig.class) {
                  this.pc = 77;
                  return tmp9
                }
                this.pc = 77;
                continue contLoop;
              } else if (this.pc === 77) {
                tmp9 = runtime.resetDepth(tmp9, curDepth1);
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return lambda.myReturn(tmp9)
              }
              break;
            }
          }
          toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        curDepth1 = runtime.stackDepth;
        stackDelayRes1 = runtime.checkDepth();
        if (stackDelayRes1 instanceof runtime.EffectSig.class) {
          stackDelayRes1.tail.next = new Cont$lambda$9.class(75, null);
          stackDelayRes1.tail = stackDelayRes1.tail.next;
          return stackDelayRes1
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp8 = lambda.Lam(x1, b3);
        if (tmp8 instanceof runtime.EffectSig.class) {
          tmp8.tail.next = new Cont$lambda$9.class(76, null);
          tmp8.tail = tmp8.tail.next;
          return tmp8
        }
        tmp8 = runtime.resetDepth(tmp8, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp9 = lambda.Thunk(tmp8, env);
        if (tmp9 instanceof runtime.EffectSig.class) {
          tmp9.tail.next = new Cont$lambda$9.class(77, null);
          tmp9.tail = tmp9.tail.next;
          return tmp9
        }
        tmp9 = runtime.resetDepth(tmp9, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        return lambda.myReturn(tmp9)
      })
    } else if (ter instanceof lambda.App.class) {
      param02 = ter.a;
      param11 = ter.b;
      u = param02;
      v2 = param11;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = lambda.traverseTerm(u);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.tail.next = new Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$1.class(78, null);
        tmp3.tail = tmp3.tail.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.myBind(tmp3, (u_) => {
        let stackDelayRes1, Cont$lambda$9;
        Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
        Cont$lambda$9.class = class Cont$lambda$7 extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp8;
            tmp8 = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 79) {
              stackDelayRes1 = value$;
            }
            contLoop: while (true) {
              if (this.pc === 79) {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return lambda.apply(u_, v2)
              }
              break;
            }
          }
          toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        stackDelayRes1 = runtime.checkDepth();
        if (stackDelayRes1 instanceof runtime.EffectSig.class) {
          stackDelayRes1.tail.next = new Cont$lambda$9.class(79, null);
          stackDelayRes1.tail = stackDelayRes1.tail.next;
          return stackDelayRes1
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        return lambda.apply(u_, v2)
      })
    } else if (ter instanceof lambda.IfZero.class) {
      param01 = ter.a;
      param1 = ter.b;
      param2 = ter.c;
      c = param01;
      a4 = param1;
      b2 = param2;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = lambda.traverseTerm(c);
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.tail.next = new Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$1.class(80, null);
        tmp4.tail = tmp4.tail.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      tmp5 = (vall) => {
        let scrut, tmp8, curDepth1, stackDelayRes1, Cont$lambda$9;
        Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
        Cont$lambda$9.class = class Cont$lambda$11 extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp9;
            tmp9 = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 81) {
              stackDelayRes1 = value$;
            } else if (this.pc === 82) {
              tmp8 = value$;
            } else if (this.pc === 83) {
              scrut = value$;
            }
            contLoop: while (true) {
              if (this.pc === 81) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp8 = lambda.Con(0);
                if (tmp8 instanceof runtime.EffectSig.class) {
                  this.pc = 82;
                  return tmp8
                }
                this.pc = 82;
                continue contLoop;
              } else if (this.pc === 82) {
                tmp8 = runtime.resetDepth(tmp8, curDepth1);
                runtime.stackDepth = runtime.stackDepth + 1;
                scrut = lambda.eqTerm(vall, tmp8);
                if (scrut instanceof runtime.EffectSig.class) {
                  this.pc = 83;
                  return scrut
                }
                this.pc = 83;
                continue contLoop;
              } else if (this.pc === 83) {
                scrut = runtime.resetDepth(scrut, curDepth1);
                if (scrut === true) {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  this.completed = true;
                  return lambda.traverseTerm(a4)
                } else {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  this.completed = true;
                  return lambda.traverseTerm(b2)
                }
                this.pc = 84;
                continue contLoop;
              } else if (this.pc === 84) {
                break contLoop;
              }
              break;
            }
          }
          toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        curDepth1 = runtime.stackDepth;
        stackDelayRes1 = runtime.checkDepth();
        if (stackDelayRes1 instanceof runtime.EffectSig.class) {
          stackDelayRes1.tail.next = new Cont$lambda$9.class(81, null);
          stackDelayRes1.tail = stackDelayRes1.tail.next;
          return stackDelayRes1
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp8 = lambda.Con(0);
        if (tmp8 instanceof runtime.EffectSig.class) {
          tmp8.tail.next = new Cont$lambda$9.class(82, null);
          tmp8.tail = tmp8.tail.next;
          return tmp8
        }
        tmp8 = runtime.resetDepth(tmp8, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        scrut = lambda.eqTerm(vall, tmp8);
        if (scrut instanceof runtime.EffectSig.class) {
          scrut.tail.next = new Cont$lambda$9.class(83, null);
          scrut.tail = scrut.tail.next;
          return scrut
        }
        scrut = runtime.resetDepth(scrut, curDepth1);
        if (scrut === true) {
          runtime.stackDepth = runtime.stackDepth + 1;
          return lambda.traverseTerm(a4)
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          return lambda.traverseTerm(b2)
        }
      };
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.myBind(tmp4, tmp5)
    } else if (ter instanceof lambda.Con.class) {
      param0 = ter.i;
      i = param0;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp6 = lambda.Con(i);
      if (tmp6 instanceof runtime.EffectSig.class) {
        tmp6.tail.next = new Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$1.class(85, null);
        tmp6.tail = tmp6.tail.next;
        return tmp6
      }
      tmp6 = runtime.resetDepth(tmp6, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.myReturn(tmp6)
    } else if (ter instanceof lambda.Incr.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.myBind(lambda.#incr, (_dummy) => {
        let tmp8, curDepth1, stackDelayRes1, Cont$lambda$9;
        Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
        Cont$lambda$9.class = class Cont$lambda$10 extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp9;
            tmp9 = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 86) {
              stackDelayRes1 = value$;
            } else if (this.pc === 87) {
              tmp8 = value$;
            }
            contLoop: while (true) {
              if (this.pc === 86) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp8 = lambda.Con(0);
                if (tmp8 instanceof runtime.EffectSig.class) {
                  this.pc = 87;
                  return tmp8
                }
                this.pc = 87;
                continue contLoop;
              } else if (this.pc === 87) {
                tmp8 = runtime.resetDepth(tmp8, curDepth1);
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return lambda.myReturn(tmp8)
              }
              break;
            }
          }
          toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        curDepth1 = runtime.stackDepth;
        stackDelayRes1 = runtime.checkDepth();
        if (stackDelayRes1 instanceof runtime.EffectSig.class) {
          stackDelayRes1.tail.next = new Cont$lambda$9.class(86, null);
          stackDelayRes1.tail = stackDelayRes1.tail.next;
          return stackDelayRes1
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp8 = lambda.Con(0);
        if (tmp8 instanceof runtime.EffectSig.class) {
          tmp8.tail.next = new Cont$lambda$9.class(87, null);
          tmp8.tail = tmp8.tail.next;
          return tmp8
        }
        tmp8 = runtime.resetDepth(tmp8, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        return lambda.myReturn(tmp8)
      })
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp7 = new globalThis.Error("match error");
      if (tmp7 instanceof runtime.EffectSig.class) {
        tmp7.tail.next = new Cont$func$eval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2316_2950$1.class(88, null);
        tmp7.tail = tmp7.tail.next;
        return tmp7
      }
      tmp7 = runtime.resetDepth(tmp7, curDepth);
      throw tmp7;
    }
  } 
  static simpleEval(env, ter1) {
    let param0, param1, t5, e, param01, param11, param2, c, a4, b2, val_, scrut, param02, param12, u, v2, u_, param03, param13, x1, b3, param04, param14, u1, v3, u_1, v_, param05, e1, param06, v4, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, tmp10, stackDelayRes, Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1;
    Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1 = function Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$(pc1, next1) { return new Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$.class(pc1, next1); };
    Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1.class = class Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp11;
        tmp11 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 90) {
          stackDelayRes = value$;
        } else if (this.pc === 102) {
          tmp10 = value$;
        } else if (this.pc === 99) {
          tmp8 = value$;
        } else if (this.pc === 100) {
          tmp9 = value$;
        } else if (this.pc === 101) {
          scrut = value$;
        } else if (this.pc === 98) {
          tmp7 = value$;
        } else if (this.pc === 97) {
          tmp6 = value$;
        } else if (this.pc === 95) {
          tmp3 = value$;
        } else if (this.pc === 96) {
          tmp4 = value$;
        } else if (this.pc === 91) {
          tmp1 = value$;
        } else if (this.pc === 94) {
          tmp2 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 90) {
            if (ter1 instanceof lambda.Var.class) {
              param06 = ter1.s;
              v4 = param06;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = lambda.lookup(v4, env);
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 91;
                return tmp1
              }
              this.pc = 91;
              continue contLoop;
            } else if (ter1 instanceof lambda.Con.class) {
              param05 = ter1.i;
              e1 = param05;
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return lambda.Con(e1);
              this.pc = 103;
              continue contLoop;
            } else if (ter1 instanceof lambda.Incr.class) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return lambda.Con(0);
              this.pc = 103;
              continue contLoop;
              this.pc = 103;
              continue contLoop;
            } else {
              if (ter1 instanceof lambda.Add.class) {
                param04 = ter1.a;
                param14 = ter1.b;
                u1 = param04;
                v3 = param14;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp3 = lambda.simpleEvalCon(env, u1);
                if (tmp3 instanceof runtime.EffectSig.class) {
                  this.pc = 95;
                  return tmp3
                }
                this.pc = 95;
                continue contLoop;
              } else if (ter1 instanceof lambda.Lam.class) {
                param03 = ter1.s;
                param13 = ter1.t;
                x1 = param03;
                b3 = param13;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp6 = lambda.Lam(x1, b3);
                if (tmp6 instanceof runtime.EffectSig.class) {
                  this.pc = 97;
                  return tmp6
                }
                this.pc = 97;
                continue contLoop;
                this.pc = 103;
                continue contLoop;
              } else if (ter1 instanceof lambda.App.class) {
                param02 = ter1.a;
                param12 = ter1.b;
                u = param02;
                v2 = param12;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp7 = lambda.simpleEval(env, u);
                if (tmp7 instanceof runtime.EffectSig.class) {
                  this.pc = 98;
                  return tmp7
                }
                this.pc = 98;
                continue contLoop;
                this.pc = 103;
                continue contLoop;
                this.pc = 103;
                continue contLoop;
              } else if (ter1 instanceof lambda.IfZero.class) {
                param01 = ter1.a;
                param11 = ter1.b;
                param2 = ter1.c;
                c = param01;
                a4 = param11;
                b2 = param2;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp8 = lambda.simpleEval(env, c);
                if (tmp8 instanceof runtime.EffectSig.class) {
                  this.pc = 99;
                  return tmp8
                }
                this.pc = 99;
                continue contLoop;
                this.pc = 103;
                continue contLoop;
                this.pc = 103;
                continue contLoop;
                this.pc = 103;
                continue contLoop;
              } else if (ter1 instanceof lambda.Thunk.class) {
                param0 = ter1.t;
                param1 = ter1.e;
                t5 = param0;
                e = param1;
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return lambda.simpleEval(e, t5);
                this.pc = 103;
                continue contLoop;
                this.pc = 103;
                continue contLoop;
                this.pc = 103;
                continue contLoop;
                this.pc = 103;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp10 = globalThis.Error(ter1);
                if (tmp10 instanceof runtime.EffectSig.class) {
                  this.pc = 102;
                  return tmp10
                }
                this.pc = 102;
                continue contLoop;
              }
              this.pc = 103;
              continue contLoop;
            }
            this.pc = 103;
            continue contLoop;
          } else if (this.pc === 103) {
            break contLoop;
          } else if (this.pc === 102) {
            tmp10 = runtime.resetDepth(tmp10, curDepth);
            throw tmp10;
          } else if (this.pc === 99) {
            tmp8 = runtime.resetDepth(tmp8, curDepth);
            val_ = tmp8;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp9 = lambda.Con(0);
            if (tmp9 instanceof runtime.EffectSig.class) {
              this.pc = 100;
              return tmp9
            }
            this.pc = 100;
            continue contLoop;
          } else if (this.pc === 100) {
            tmp9 = runtime.resetDepth(tmp9, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            scrut = lambda.eqTerm(val_, tmp9);
            if (scrut instanceof runtime.EffectSig.class) {
              this.pc = 101;
              return scrut
            }
            this.pc = 101;
            continue contLoop;
          } else if (this.pc === 101) {
            scrut = runtime.resetDepth(scrut, curDepth);
            if (scrut === true) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return lambda.simpleEval(env, a4)
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return lambda.simpleEval(env, b2)
            }
            this.pc = 103;
            continue contLoop;
          } else if (this.pc === 98) {
            tmp7 = runtime.resetDepth(tmp7, curDepth);
            u_ = tmp7;
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.simpleApply(env, u_, v2)
          } else if (this.pc === 97) {
            tmp6 = runtime.resetDepth(tmp6, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.Thunk(tmp6, env)
          } else if (this.pc === 95) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            u_1 = tmp3;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = lambda.simpleEvalCon(env, v3);
            if (tmp4 instanceof runtime.EffectSig.class) {
              this.pc = 96;
              return tmp4
            }
            this.pc = 96;
            continue contLoop;
          } else if (this.pc === 96) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            v_ = tmp4;
            tmp5 = u_1 + v_;
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.Con(tmp5)
          } else if (this.pc === 91) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = lambda.myMaybe((dummy) => {
              let tmp11, curDepth1, stackDelayRes1, Cont$lambda$9;
              Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$9.class = class Cont$lambda$15 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp12;
                  tmp12 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 92) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 93) {
                    tmp11 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 92) {
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp11 = globalThis.Error("undefined var");
                      if (tmp11 instanceof runtime.EffectSig.class) {
                        this.pc = 93;
                        return tmp11
                      }
                      this.pc = 93;
                      continue contLoop1;
                    } else if (this.pc === 93) {
                      tmp11 = runtime.resetDepth(tmp11, curDepth1);
                      throw tmp11;
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              curDepth1 = runtime.stackDepth;
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$9.class(92, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp11 = globalThis.Error("undefined var");
              if (tmp11 instanceof runtime.EffectSig.class) {
                tmp11.tail.next = new Cont$lambda$9.class(93, null);
                tmp11.tail = tmp11.tail.next;
                return tmp11
              }
              tmp11 = runtime.resetDepth(tmp11, curDepth1);
              throw tmp11;
            }, (x2) => {
              return x2
            }, tmp1);
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 94;
              return tmp2
            }
            this.pc = 94;
            continue contLoop;
          } else if (this.pc === 94) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.simpleEval(env, tmp2)
          }
          break;
        }
      }
      toString() { return "Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1.class(90, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (ter1 instanceof lambda.Var.class) {
      param06 = ter1.s;
      v4 = param06;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = lambda.lookup(v4, env);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.tail.next = new Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1.class(91, null);
        tmp1.tail = tmp1.tail.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = lambda.myMaybe((dummy) => {
        let tmp11, curDepth1, stackDelayRes1, Cont$lambda$9;
        Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
        Cont$lambda$9.class = class Cont$lambda$15 extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp12;
            tmp12 = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 92) {
              stackDelayRes1 = value$;
            } else if (this.pc === 93) {
              tmp11 = value$;
            }
            contLoop: while (true) {
              if (this.pc === 92) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp11 = globalThis.Error("undefined var");
                if (tmp11 instanceof runtime.EffectSig.class) {
                  this.pc = 93;
                  return tmp11
                }
                this.pc = 93;
                continue contLoop;
              } else if (this.pc === 93) {
                tmp11 = runtime.resetDepth(tmp11, curDepth1);
                throw tmp11;
              }
              break;
            }
          }
          toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        curDepth1 = runtime.stackDepth;
        stackDelayRes1 = runtime.checkDepth();
        if (stackDelayRes1 instanceof runtime.EffectSig.class) {
          stackDelayRes1.tail.next = new Cont$lambda$9.class(92, null);
          stackDelayRes1.tail = stackDelayRes1.tail.next;
          return stackDelayRes1
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp11 = globalThis.Error("undefined var");
        if (tmp11 instanceof runtime.EffectSig.class) {
          tmp11.tail.next = new Cont$lambda$9.class(93, null);
          tmp11.tail = tmp11.tail.next;
          return tmp11
        }
        tmp11 = runtime.resetDepth(tmp11, curDepth1);
        throw tmp11;
      }, (x2) => {
        return x2
      }, tmp1);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.tail.next = new Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1.class(94, null);
        tmp2.tail = tmp2.tail.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.simpleEval(env, tmp2)
    } else if (ter1 instanceof lambda.Con.class) {
      param05 = ter1.i;
      e1 = param05;
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.Con(e1)
    } else if (ter1 instanceof lambda.Incr.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.Con(0)
    } else if (ter1 instanceof lambda.Add.class) {
      param04 = ter1.a;
      param14 = ter1.b;
      u1 = param04;
      v3 = param14;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = lambda.simpleEvalCon(env, u1);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.tail.next = new Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1.class(95, null);
        tmp3.tail = tmp3.tail.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      u_1 = tmp3;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = lambda.simpleEvalCon(env, v3);
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.tail.next = new Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1.class(96, null);
        tmp4.tail = tmp4.tail.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      v_ = tmp4;
      tmp5 = u_1 + v_;
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.Con(tmp5)
    } else if (ter1 instanceof lambda.Lam.class) {
      param03 = ter1.s;
      param13 = ter1.t;
      x1 = param03;
      b3 = param13;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp6 = lambda.Lam(x1, b3);
      if (tmp6 instanceof runtime.EffectSig.class) {
        tmp6.tail.next = new Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1.class(97, null);
        tmp6.tail = tmp6.tail.next;
        return tmp6
      }
      tmp6 = runtime.resetDepth(tmp6, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.Thunk(tmp6, env)
    } else if (ter1 instanceof lambda.App.class) {
      param02 = ter1.a;
      param12 = ter1.b;
      u = param02;
      v2 = param12;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp7 = lambda.simpleEval(env, u);
      if (tmp7 instanceof runtime.EffectSig.class) {
        tmp7.tail.next = new Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1.class(98, null);
        tmp7.tail = tmp7.tail.next;
        return tmp7
      }
      tmp7 = runtime.resetDepth(tmp7, curDepth);
      u_ = tmp7;
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.simpleApply(env, u_, v2)
    } else if (ter1 instanceof lambda.IfZero.class) {
      param01 = ter1.a;
      param11 = ter1.b;
      param2 = ter1.c;
      c = param01;
      a4 = param11;
      b2 = param2;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp8 = lambda.simpleEval(env, c);
      if (tmp8 instanceof runtime.EffectSig.class) {
        tmp8.tail.next = new Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1.class(99, null);
        tmp8.tail = tmp8.tail.next;
        return tmp8
      }
      tmp8 = runtime.resetDepth(tmp8, curDepth);
      val_ = tmp8;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp9 = lambda.Con(0);
      if (tmp9 instanceof runtime.EffectSig.class) {
        tmp9.tail.next = new Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1.class(100, null);
        tmp9.tail = tmp9.tail.next;
        return tmp9
      }
      tmp9 = runtime.resetDepth(tmp9, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      scrut = lambda.eqTerm(val_, tmp9);
      if (scrut instanceof runtime.EffectSig.class) {
        scrut.tail.next = new Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1.class(101, null);
        scrut.tail = scrut.tail.next;
        return scrut
      }
      scrut = runtime.resetDepth(scrut, curDepth);
      if (scrut === true) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return lambda.simpleEval(env, a4)
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        return lambda.simpleEval(env, b2)
      }
    } else if (ter1 instanceof lambda.Thunk.class) {
      param0 = ter1.t;
      param1 = ter1.e;
      t5 = param0;
      e = param1;
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.simpleEval(e, t5)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp10 = globalThis.Error(ter1);
      if (tmp10 instanceof runtime.EffectSig.class) {
        tmp10.tail.next = new Cont$func$simpleEval$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_2956_3543$1.class(102, null);
        tmp10.tail = tmp10.tail.next;
        return tmp10
      }
      tmp10 = runtime.resetDepth(tmp10, curDepth);
      throw tmp10;
    }
  } 
  static simpleApply(env1, t5, a4) {
    let param0, param1, param01, param11, x1, b2, e, tmp1, tmp2, curDepth, tmp3, tmp4, stackDelayRes, Cont$func$simpleApply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3549_3685$1;
    Cont$func$simpleApply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3549_3685$1 = function Cont$func$simpleApply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3549_3685$(pc1, next1) { return new Cont$func$simpleApply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3549_3685$.class(pc1, next1); };
    Cont$func$simpleApply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3549_3685$1.class = class Cont$func$simpleApply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3549_3685$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp5;
        tmp5 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 104) {
          stackDelayRes = value$;
        } else if (this.pc === 108) {
          tmp4 = value$;
        } else if (this.pc === 107) {
          tmp3 = value$;
        } else if (this.pc === 105) {
          tmp1 = value$;
        } else if (this.pc === 106) {
          tmp2 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 104) {
            if (t5 instanceof lambda.Thunk.class) {
              param0 = t5.t;
              param1 = t5.e;
              if (param0 instanceof lambda.Lam.class) {
                param01 = param0.s;
                param11 = param0.t;
                x1 = param01;
                b2 = param11;
                e = param1;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp1 = lambda.Thunk(a4, env1);
                if (tmp1 instanceof runtime.EffectSig.class) {
                  this.pc = 105;
                  return tmp1
                }
                this.pc = 105;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp3 = globalThis.Error("bad application");
                if (tmp3 instanceof runtime.EffectSig.class) {
                  this.pc = 107;
                  return tmp3
                }
                this.pc = 107;
                continue contLoop;
              }
              this.pc = 109;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp4 = globalThis.Error("bad application");
              if (tmp4 instanceof runtime.EffectSig.class) {
                this.pc = 108;
                return tmp4
              }
              this.pc = 108;
              continue contLoop;
            }
            this.pc = 109;
            continue contLoop;
          } else if (this.pc === 109) {
            break contLoop;
          } else if (this.pc === 108) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            throw tmp4;
          } else if (this.pc === 107) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            throw tmp3;
          } else if (this.pc === 105) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = NofibPrelude.Cons([
              x1,
              tmp1
            ], e);
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 106;
              return tmp2
            }
            this.pc = 106;
            continue contLoop;
          } else if (this.pc === 106) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.simpleEval(tmp2, b2)
          }
          break;
        }
      }
      toString() { return "Cont$func$simpleApply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3549_3685$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$simpleApply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3549_3685$1.class(104, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (t5 instanceof lambda.Thunk.class) {
      param0 = t5.t;
      param1 = t5.e;
      if (param0 instanceof lambda.Lam.class) {
        param01 = param0.s;
        param11 = param0.t;
        x1 = param01;
        b2 = param11;
        e = param1;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp1 = lambda.Thunk(a4, env1);
        if (tmp1 instanceof runtime.EffectSig.class) {
          tmp1.tail.next = new Cont$func$simpleApply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3549_3685$1.class(105, null);
          tmp1.tail = tmp1.tail.next;
          return tmp1
        }
        tmp1 = runtime.resetDepth(tmp1, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp2 = NofibPrelude.Cons([
          x1,
          tmp1
        ], e);
        if (tmp2 instanceof runtime.EffectSig.class) {
          tmp2.tail.next = new Cont$func$simpleApply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3549_3685$1.class(106, null);
          tmp2.tail = tmp2.tail.next;
          return tmp2
        }
        tmp2 = runtime.resetDepth(tmp2, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        return lambda.simpleEval(tmp2, b2)
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp3 = globalThis.Error("bad application");
        if (tmp3 instanceof runtime.EffectSig.class) {
          tmp3.tail.next = new Cont$func$simpleApply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3549_3685$1.class(107, null);
          tmp3.tail = tmp3.tail.next;
          return tmp3
        }
        tmp3 = runtime.resetDepth(tmp3, curDepth);
        throw tmp3;
      }
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = globalThis.Error("bad application");
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.tail.next = new Cont$func$simpleApply$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3549_3685$1.class(108, null);
        tmp4.tail = tmp4.tail.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      throw tmp4;
    }
  } 
  static simpleEvalCon(env2, e) {
    let e_, param0, c, tmp1, curDepth, tmp2, stackDelayRes, Cont$func$simpleEvalCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3691_3799$1;
    Cont$func$simpleEvalCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3691_3799$1 = function Cont$func$simpleEvalCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3691_3799$(pc1, next1) { return new Cont$func$simpleEvalCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3691_3799$.class(pc1, next1); };
    Cont$func$simpleEvalCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3691_3799$1.class = class Cont$func$simpleEvalCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3691_3799$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp3;
        tmp3 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 110) {
          stackDelayRes = value$;
        } else if (this.pc === 111) {
          tmp1 = value$;
        } else if (this.pc === 112) {
          tmp2 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 110) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = lambda.simpleEval(env2, e);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 111;
              return tmp1
            }
            this.pc = 111;
            continue contLoop;
          } else if (this.pc === 111) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            e_ = tmp1;
            if (e_ instanceof lambda.Con.class) {
              param0 = e_.i;
              c = param0;
              this.completed = true;
              return c
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp2 = globalThis.Error("Not a Con");
              if (tmp2 instanceof runtime.EffectSig.class) {
                this.pc = 112;
                return tmp2
              }
              this.pc = 112;
              continue contLoop;
            }
            this.pc = 113;
            continue contLoop;
          } else if (this.pc === 113) {
            break contLoop;
          } else if (this.pc === 112) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            throw tmp2;
          }
          break;
        }
      }
      toString() { return "Cont$func$simpleEvalCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3691_3799$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$simpleEvalCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3691_3799$1.class(110, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = lambda.simpleEval(env2, e);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.tail.next = new Cont$func$simpleEvalCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3691_3799$1.class(111, null);
      tmp1.tail = tmp1.tail.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    e_ = tmp1;
    if (e_ instanceof lambda.Con.class) {
      param0 = e_.i;
      c = param0;
      return c
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = globalThis.Error("Not a Con");
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.tail.next = new Cont$func$simpleEvalCon$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3691_3799$1.class(112, null);
        tmp2.tail = tmp2.tail.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      throw tmp2;
    }
  } 
  static bracket(ot, ths, t6) {
    let scrut, tmp1, tmp2, curDepth, stackDelayRes, Cont$func$bracket$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3805_3888$1;
    Cont$func$bracket$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3805_3888$1 = function Cont$func$bracket$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3805_3888$(pc1, next1) { return new Cont$func$bracket$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3805_3888$.class(pc1, next1); };
    Cont$func$bracket$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3805_3888$1.class = class Cont$func$bracket$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3805_3888$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp3;
        tmp3 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 114) {
          stackDelayRes = value$;
        } else if (this.pc === 115) {
          tmp1 = value$;
        } else if (this.pc === 116) {
          tmp2 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 114) {
            scrut = ths <= ot;
            if (scrut === true) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = NofibPrelude.nofibStringToList(")");
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 115;
                return tmp1
              }
              this.pc = 115;
              continue contLoop;
            } else {
              this.completed = true;
              return t6
            }
            this.pc = 117;
            continue contLoop;
          } else if (this.pc === 117) {
            break contLoop;
          } else if (this.pc === 115) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = NofibPrelude.append(t6, tmp1);
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 116;
              return tmp2
            }
            this.pc = 116;
            continue contLoop;
          } else if (this.pc === 116) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return NofibPrelude.Cons("(", tmp2)
          }
          break;
        }
      }
      toString() { return "Cont$func$bracket$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3805_3888$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$bracket$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3805_3888$1.class(114, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    scrut = ths <= ot;
    if (scrut === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = NofibPrelude.nofibStringToList(")");
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.tail.next = new Cont$func$bracket$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3805_3888$1.class(115, null);
        tmp1.tail = tmp1.tail.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = NofibPrelude.append(t6, tmp1);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.tail.next = new Cont$func$bracket$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3805_3888$1.class(116, null);
        tmp2.tail = tmp2.tail.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.Cons("(", tmp2)
    } else {
      return t6
    }
  } 
  static ppn(n, ter2) {
    let param0, param1, t7, e1, param01, param11, param2, c, a5, b2, param02, param12, a6, b3, param03, param13, a7, b4, param04, param14, v2, t8, param05, i, param06, v3, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, curDepth, tmp34, stackDelayRes, Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1;
    Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1 = function Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$(pc1, next1) { return new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$.class(pc1, next1); };
    Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class = class Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp35;
        tmp35 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 118) {
          stackDelayRes = value$;
        } else if (this.pc === 151) {
          tmp34 = value$;
        } else if (this.pc === 146) {
          tmp29 = value$;
        } else if (this.pc === 147) {
          tmp30 = value$;
        } else if (this.pc === 148) {
          tmp31 = value$;
        } else if (this.pc === 149) {
          tmp32 = value$;
        } else if (this.pc === 150) {
          tmp33 = value$;
        } else if (this.pc === 135) {
          tmp18 = value$;
        } else if (this.pc === 136) {
          tmp19 = value$;
        } else if (this.pc === 137) {
          tmp20 = value$;
        } else if (this.pc === 138) {
          tmp21 = value$;
        } else if (this.pc === 139) {
          tmp22 = value$;
        } else if (this.pc === 140) {
          tmp23 = value$;
        } else if (this.pc === 141) {
          tmp24 = value$;
        } else if (this.pc === 142) {
          tmp25 = value$;
        } else if (this.pc === 143) {
          tmp26 = value$;
        } else if (this.pc === 144) {
          tmp27 = value$;
        } else if (this.pc === 145) {
          tmp28 = value$;
        } else if (this.pc === 130) {
          tmp13 = value$;
        } else if (this.pc === 131) {
          tmp14 = value$;
        } else if (this.pc === 132) {
          tmp15 = value$;
        } else if (this.pc === 133) {
          tmp16 = value$;
        } else if (this.pc === 134) {
          tmp17 = value$;
        } else if (this.pc === 125) {
          tmp8 = value$;
        } else if (this.pc === 126) {
          tmp9 = value$;
        } else if (this.pc === 127) {
          tmp10 = value$;
        } else if (this.pc === 128) {
          tmp11 = value$;
        } else if (this.pc === 129) {
          tmp12 = value$;
        } else if (this.pc === 120) {
          tmp2 = value$;
        } else if (this.pc === 121) {
          tmp4 = value$;
        } else if (this.pc === 122) {
          tmp5 = value$;
        } else if (this.pc === 123) {
          tmp6 = value$;
        } else if (this.pc === 124) {
          tmp7 = value$;
        } else if (this.pc === 119) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 118) {
            if (ter2 instanceof lambda.Var.class) {
              param06 = ter2.s;
              v3 = param06;
              this.completed = true;
              return v3
            } else if (ter2 instanceof lambda.Con.class) {
              param05 = ter2.i;
              i = param05;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = NofibPrelude.stringOfInt(i);
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 119;
                return tmp1
              }
              this.pc = 119;
              continue contLoop;
              this.pc = 152;
              continue contLoop;
            } else if (ter2 instanceof lambda.Incr.class) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return NofibPrelude.nofibStringToList("INCR");
              this.pc = 152;
              continue contLoop;
              this.pc = 152;
              continue contLoop;
            } else {
              if (ter2 instanceof lambda.Lam.class) {
                param04 = ter2.s;
                param14 = ter2.t;
                v2 = param04;
                t8 = param14;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp2 = NofibPrelude.nofibStringToList(". ");
                if (tmp2 instanceof runtime.EffectSig.class) {
                  this.pc = 120;
                  return tmp2
                }
                this.pc = 120;
                continue contLoop;
              } else if (ter2 instanceof lambda.Add.class) {
                param03 = ter2.a;
                param13 = ter2.b;
                a7 = param03;
                b4 = param13;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp8 = lambda.ppn(1, a7);
                if (tmp8 instanceof runtime.EffectSig.class) {
                  this.pc = 125;
                  return tmp8
                }
                this.pc = 125;
                continue contLoop;
                this.pc = 152;
                continue contLoop;
              } else if (ter2 instanceof lambda.App.class) {
                param02 = ter2.a;
                param12 = ter2.b;
                a6 = param02;
                b3 = param12;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp13 = lambda.ppn(2, a6);
                if (tmp13 instanceof runtime.EffectSig.class) {
                  this.pc = 130;
                  return tmp13
                }
                this.pc = 130;
                continue contLoop;
                this.pc = 152;
                continue contLoop;
                this.pc = 152;
                continue contLoop;
              } else if (ter2 instanceof lambda.IfZero.class) {
                param01 = ter2.a;
                param11 = ter2.b;
                param2 = ter2.c;
                c = param01;
                a5 = param11;
                b2 = param2;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp18 = NofibPrelude.nofibStringToList("IF ");
                if (tmp18 instanceof runtime.EffectSig.class) {
                  this.pc = 135;
                  return tmp18
                }
                this.pc = 135;
                continue contLoop;
                this.pc = 152;
                continue contLoop;
                this.pc = 152;
                continue contLoop;
                this.pc = 152;
                continue contLoop;
              } else if (ter2 instanceof lambda.Thunk.class) {
                param0 = ter2.t;
                param1 = ter2.e;
                t7 = param0;
                e1 = param1;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp29 = lambda.ppn(3, t7);
                if (tmp29 instanceof runtime.EffectSig.class) {
                  this.pc = 146;
                  return tmp29
                }
                this.pc = 146;
                continue contLoop;
                this.pc = 152;
                continue contLoop;
                this.pc = 152;
                continue contLoop;
                this.pc = 152;
                continue contLoop;
                this.pc = 152;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp34 = new globalThis.Error("match error");
                if (tmp34 instanceof runtime.EffectSig.class) {
                  this.pc = 151;
                  return tmp34
                }
                this.pc = 151;
                continue contLoop;
              }
              this.pc = 152;
              continue contLoop;
            }
            this.pc = 152;
            continue contLoop;
          } else if (this.pc === 152) {
            break contLoop;
          } else if (this.pc === 151) {
            tmp34 = runtime.resetDepth(tmp34, curDepth);
            throw tmp34;
          } else if (this.pc === 146) {
            tmp29 = runtime.resetDepth(tmp29, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp30 = NofibPrelude.nofibStringToList("::");
            if (tmp30 instanceof runtime.EffectSig.class) {
              this.pc = 147;
              return tmp30
            }
            this.pc = 147;
            continue contLoop;
          } else if (this.pc === 147) {
            tmp30 = runtime.resetDepth(tmp30, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp31 = lambda.ppenv(e1);
            if (tmp31 instanceof runtime.EffectSig.class) {
              this.pc = 148;
              return tmp31
            }
            this.pc = 148;
            continue contLoop;
          } else if (this.pc === 148) {
            tmp31 = runtime.resetDepth(tmp31, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp32 = NofibPrelude.append(tmp30, tmp31);
            if (tmp32 instanceof runtime.EffectSig.class) {
              this.pc = 149;
              return tmp32
            }
            this.pc = 149;
            continue contLoop;
          } else if (this.pc === 149) {
            tmp32 = runtime.resetDepth(tmp32, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp33 = NofibPrelude.append(tmp29, tmp32);
            if (tmp33 instanceof runtime.EffectSig.class) {
              this.pc = 150;
              return tmp33
            }
            this.pc = 150;
            continue contLoop;
          } else if (this.pc === 150) {
            tmp33 = runtime.resetDepth(tmp33, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.bracket(n, 0, tmp33)
          } else if (this.pc === 135) {
            tmp18 = runtime.resetDepth(tmp18, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp19 = lambda.ppn(0, c);
            if (tmp19 instanceof runtime.EffectSig.class) {
              this.pc = 136;
              return tmp19
            }
            this.pc = 136;
            continue contLoop;
          } else if (this.pc === 136) {
            tmp19 = runtime.resetDepth(tmp19, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp20 = NofibPrelude.nofibStringToList(" THEN ");
            if (tmp20 instanceof runtime.EffectSig.class) {
              this.pc = 137;
              return tmp20
            }
            this.pc = 137;
            continue contLoop;
          } else if (this.pc === 137) {
            tmp20 = runtime.resetDepth(tmp20, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp21 = lambda.ppn(0, a5);
            if (tmp21 instanceof runtime.EffectSig.class) {
              this.pc = 138;
              return tmp21
            }
            this.pc = 138;
            continue contLoop;
          } else if (this.pc === 138) {
            tmp21 = runtime.resetDepth(tmp21, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp22 = NofibPrelude.nofibStringToList(" ELSE ");
            if (tmp22 instanceof runtime.EffectSig.class) {
              this.pc = 139;
              return tmp22
            }
            this.pc = 139;
            continue contLoop;
          } else if (this.pc === 139) {
            tmp22 = runtime.resetDepth(tmp22, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp23 = lambda.ppn(0, b2);
            if (tmp23 instanceof runtime.EffectSig.class) {
              this.pc = 140;
              return tmp23
            }
            this.pc = 140;
            continue contLoop;
          } else if (this.pc === 140) {
            tmp23 = runtime.resetDepth(tmp23, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp24 = NofibPrelude.append(tmp22, tmp23);
            if (tmp24 instanceof runtime.EffectSig.class) {
              this.pc = 141;
              return tmp24
            }
            this.pc = 141;
            continue contLoop;
          } else if (this.pc === 141) {
            tmp24 = runtime.resetDepth(tmp24, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp25 = NofibPrelude.append(tmp21, tmp24);
            if (tmp25 instanceof runtime.EffectSig.class) {
              this.pc = 142;
              return tmp25
            }
            this.pc = 142;
            continue contLoop;
          } else if (this.pc === 142) {
            tmp25 = runtime.resetDepth(tmp25, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp26 = NofibPrelude.append(tmp20, tmp25);
            if (tmp26 instanceof runtime.EffectSig.class) {
              this.pc = 143;
              return tmp26
            }
            this.pc = 143;
            continue contLoop;
          } else if (this.pc === 143) {
            tmp26 = runtime.resetDepth(tmp26, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp27 = NofibPrelude.append(tmp19, tmp26);
            if (tmp27 instanceof runtime.EffectSig.class) {
              this.pc = 144;
              return tmp27
            }
            this.pc = 144;
            continue contLoop;
          } else if (this.pc === 144) {
            tmp27 = runtime.resetDepth(tmp27, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp28 = NofibPrelude.append(tmp18, tmp27);
            if (tmp28 instanceof runtime.EffectSig.class) {
              this.pc = 145;
              return tmp28
            }
            this.pc = 145;
            continue contLoop;
          } else if (this.pc === 145) {
            tmp28 = runtime.resetDepth(tmp28, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.bracket(n, 0, tmp28)
          } else if (this.pc === 130) {
            tmp13 = runtime.resetDepth(tmp13, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp14 = NofibPrelude.nofibStringToList(" ");
            if (tmp14 instanceof runtime.EffectSig.class) {
              this.pc = 131;
              return tmp14
            }
            this.pc = 131;
            continue contLoop;
          } else if (this.pc === 131) {
            tmp14 = runtime.resetDepth(tmp14, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp15 = lambda.ppn(2, b3);
            if (tmp15 instanceof runtime.EffectSig.class) {
              this.pc = 132;
              return tmp15
            }
            this.pc = 132;
            continue contLoop;
          } else if (this.pc === 132) {
            tmp15 = runtime.resetDepth(tmp15, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp16 = NofibPrelude.append(tmp14, tmp15);
            if (tmp16 instanceof runtime.EffectSig.class) {
              this.pc = 133;
              return tmp16
            }
            this.pc = 133;
            continue contLoop;
          } else if (this.pc === 133) {
            tmp16 = runtime.resetDepth(tmp16, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp17 = NofibPrelude.append(tmp13, tmp16);
            if (tmp17 instanceof runtime.EffectSig.class) {
              this.pc = 134;
              return tmp17
            }
            this.pc = 134;
            continue contLoop;
          } else if (this.pc === 134) {
            tmp17 = runtime.resetDepth(tmp17, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.bracket(n, 2, tmp17)
          } else if (this.pc === 125) {
            tmp8 = runtime.resetDepth(tmp8, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp9 = NofibPrelude.nofibStringToList(" + ");
            if (tmp9 instanceof runtime.EffectSig.class) {
              this.pc = 126;
              return tmp9
            }
            this.pc = 126;
            continue contLoop;
          } else if (this.pc === 126) {
            tmp9 = runtime.resetDepth(tmp9, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp10 = lambda.ppn(1, b4);
            if (tmp10 instanceof runtime.EffectSig.class) {
              this.pc = 127;
              return tmp10
            }
            this.pc = 127;
            continue contLoop;
          } else if (this.pc === 127) {
            tmp10 = runtime.resetDepth(tmp10, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp11 = NofibPrelude.append(tmp9, tmp10);
            if (tmp11 instanceof runtime.EffectSig.class) {
              this.pc = 128;
              return tmp11
            }
            this.pc = 128;
            continue contLoop;
          } else if (this.pc === 128) {
            tmp11 = runtime.resetDepth(tmp11, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp12 = NofibPrelude.append(tmp8, tmp11);
            if (tmp12 instanceof runtime.EffectSig.class) {
              this.pc = 129;
              return tmp12
            }
            this.pc = 129;
            continue contLoop;
          } else if (this.pc === 129) {
            tmp12 = runtime.resetDepth(tmp12, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.bracket(n, 1, tmp12)
          } else if (this.pc === 120) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            tmp3 = 0 - 1;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = lambda.ppn(tmp3, t8);
            if (tmp4 instanceof runtime.EffectSig.class) {
              this.pc = 121;
              return tmp4
            }
            this.pc = 121;
            continue contLoop;
          } else if (this.pc === 121) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp5 = NofibPrelude.append(tmp2, tmp4);
            if (tmp5 instanceof runtime.EffectSig.class) {
              this.pc = 122;
              return tmp5
            }
            this.pc = 122;
            continue contLoop;
          } else if (this.pc === 122) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp6 = NofibPrelude.append(v2, tmp5);
            if (tmp6 instanceof runtime.EffectSig.class) {
              this.pc = 123;
              return tmp6
            }
            this.pc = 123;
            continue contLoop;
          } else if (this.pc === 123) {
            tmp6 = runtime.resetDepth(tmp6, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp7 = NofibPrelude.Cons("@", tmp6);
            if (tmp7 instanceof runtime.EffectSig.class) {
              this.pc = 124;
              return tmp7
            }
            this.pc = 124;
            continue contLoop;
          } else if (this.pc === 124) {
            tmp7 = runtime.resetDepth(tmp7, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.bracket(n, 0, tmp7)
          } else if (this.pc === 119) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return NofibPrelude.nofibStringToList(tmp1)
          }
          break;
        }
      }
      toString() { return "Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(118, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (ter2 instanceof lambda.Var.class) {
      param06 = ter2.s;
      v3 = param06;
      return v3
    } else if (ter2 instanceof lambda.Con.class) {
      param05 = ter2.i;
      i = param05;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = NofibPrelude.stringOfInt(i);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(119, null);
        tmp1.tail = tmp1.tail.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.nofibStringToList(tmp1)
    } else if (ter2 instanceof lambda.Incr.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.nofibStringToList("INCR")
    } else if (ter2 instanceof lambda.Lam.class) {
      param04 = ter2.s;
      param14 = ter2.t;
      v2 = param04;
      t8 = param14;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = NofibPrelude.nofibStringToList(". ");
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(120, null);
        tmp2.tail = tmp2.tail.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      tmp3 = 0 - 1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = lambda.ppn(tmp3, t8);
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(121, null);
        tmp4.tail = tmp4.tail.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp5 = NofibPrelude.append(tmp2, tmp4);
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(122, null);
        tmp5.tail = tmp5.tail.next;
        return tmp5
      }
      tmp5 = runtime.resetDepth(tmp5, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp6 = NofibPrelude.append(v2, tmp5);
      if (tmp6 instanceof runtime.EffectSig.class) {
        tmp6.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(123, null);
        tmp6.tail = tmp6.tail.next;
        return tmp6
      }
      tmp6 = runtime.resetDepth(tmp6, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp7 = NofibPrelude.Cons("@", tmp6);
      if (tmp7 instanceof runtime.EffectSig.class) {
        tmp7.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(124, null);
        tmp7.tail = tmp7.tail.next;
        return tmp7
      }
      tmp7 = runtime.resetDepth(tmp7, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.bracket(n, 0, tmp7)
    } else if (ter2 instanceof lambda.Add.class) {
      param03 = ter2.a;
      param13 = ter2.b;
      a7 = param03;
      b4 = param13;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp8 = lambda.ppn(1, a7);
      if (tmp8 instanceof runtime.EffectSig.class) {
        tmp8.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(125, null);
        tmp8.tail = tmp8.tail.next;
        return tmp8
      }
      tmp8 = runtime.resetDepth(tmp8, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp9 = NofibPrelude.nofibStringToList(" + ");
      if (tmp9 instanceof runtime.EffectSig.class) {
        tmp9.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(126, null);
        tmp9.tail = tmp9.tail.next;
        return tmp9
      }
      tmp9 = runtime.resetDepth(tmp9, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp10 = lambda.ppn(1, b4);
      if (tmp10 instanceof runtime.EffectSig.class) {
        tmp10.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(127, null);
        tmp10.tail = tmp10.tail.next;
        return tmp10
      }
      tmp10 = runtime.resetDepth(tmp10, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp11 = NofibPrelude.append(tmp9, tmp10);
      if (tmp11 instanceof runtime.EffectSig.class) {
        tmp11.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(128, null);
        tmp11.tail = tmp11.tail.next;
        return tmp11
      }
      tmp11 = runtime.resetDepth(tmp11, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp12 = NofibPrelude.append(tmp8, tmp11);
      if (tmp12 instanceof runtime.EffectSig.class) {
        tmp12.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(129, null);
        tmp12.tail = tmp12.tail.next;
        return tmp12
      }
      tmp12 = runtime.resetDepth(tmp12, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.bracket(n, 1, tmp12)
    } else if (ter2 instanceof lambda.App.class) {
      param02 = ter2.a;
      param12 = ter2.b;
      a6 = param02;
      b3 = param12;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp13 = lambda.ppn(2, a6);
      if (tmp13 instanceof runtime.EffectSig.class) {
        tmp13.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(130, null);
        tmp13.tail = tmp13.tail.next;
        return tmp13
      }
      tmp13 = runtime.resetDepth(tmp13, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp14 = NofibPrelude.nofibStringToList(" ");
      if (tmp14 instanceof runtime.EffectSig.class) {
        tmp14.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(131, null);
        tmp14.tail = tmp14.tail.next;
        return tmp14
      }
      tmp14 = runtime.resetDepth(tmp14, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp15 = lambda.ppn(2, b3);
      if (tmp15 instanceof runtime.EffectSig.class) {
        tmp15.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(132, null);
        tmp15.tail = tmp15.tail.next;
        return tmp15
      }
      tmp15 = runtime.resetDepth(tmp15, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp16 = NofibPrelude.append(tmp14, tmp15);
      if (tmp16 instanceof runtime.EffectSig.class) {
        tmp16.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(133, null);
        tmp16.tail = tmp16.tail.next;
        return tmp16
      }
      tmp16 = runtime.resetDepth(tmp16, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp17 = NofibPrelude.append(tmp13, tmp16);
      if (tmp17 instanceof runtime.EffectSig.class) {
        tmp17.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(134, null);
        tmp17.tail = tmp17.tail.next;
        return tmp17
      }
      tmp17 = runtime.resetDepth(tmp17, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.bracket(n, 2, tmp17)
    } else if (ter2 instanceof lambda.IfZero.class) {
      param01 = ter2.a;
      param11 = ter2.b;
      param2 = ter2.c;
      c = param01;
      a5 = param11;
      b2 = param2;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp18 = NofibPrelude.nofibStringToList("IF ");
      if (tmp18 instanceof runtime.EffectSig.class) {
        tmp18.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(135, null);
        tmp18.tail = tmp18.tail.next;
        return tmp18
      }
      tmp18 = runtime.resetDepth(tmp18, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp19 = lambda.ppn(0, c);
      if (tmp19 instanceof runtime.EffectSig.class) {
        tmp19.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(136, null);
        tmp19.tail = tmp19.tail.next;
        return tmp19
      }
      tmp19 = runtime.resetDepth(tmp19, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp20 = NofibPrelude.nofibStringToList(" THEN ");
      if (tmp20 instanceof runtime.EffectSig.class) {
        tmp20.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(137, null);
        tmp20.tail = tmp20.tail.next;
        return tmp20
      }
      tmp20 = runtime.resetDepth(tmp20, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp21 = lambda.ppn(0, a5);
      if (tmp21 instanceof runtime.EffectSig.class) {
        tmp21.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(138, null);
        tmp21.tail = tmp21.tail.next;
        return tmp21
      }
      tmp21 = runtime.resetDepth(tmp21, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp22 = NofibPrelude.nofibStringToList(" ELSE ");
      if (tmp22 instanceof runtime.EffectSig.class) {
        tmp22.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(139, null);
        tmp22.tail = tmp22.tail.next;
        return tmp22
      }
      tmp22 = runtime.resetDepth(tmp22, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp23 = lambda.ppn(0, b2);
      if (tmp23 instanceof runtime.EffectSig.class) {
        tmp23.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(140, null);
        tmp23.tail = tmp23.tail.next;
        return tmp23
      }
      tmp23 = runtime.resetDepth(tmp23, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp24 = NofibPrelude.append(tmp22, tmp23);
      if (tmp24 instanceof runtime.EffectSig.class) {
        tmp24.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(141, null);
        tmp24.tail = tmp24.tail.next;
        return tmp24
      }
      tmp24 = runtime.resetDepth(tmp24, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp25 = NofibPrelude.append(tmp21, tmp24);
      if (tmp25 instanceof runtime.EffectSig.class) {
        tmp25.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(142, null);
        tmp25.tail = tmp25.tail.next;
        return tmp25
      }
      tmp25 = runtime.resetDepth(tmp25, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp26 = NofibPrelude.append(tmp20, tmp25);
      if (tmp26 instanceof runtime.EffectSig.class) {
        tmp26.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(143, null);
        tmp26.tail = tmp26.tail.next;
        return tmp26
      }
      tmp26 = runtime.resetDepth(tmp26, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp27 = NofibPrelude.append(tmp19, tmp26);
      if (tmp27 instanceof runtime.EffectSig.class) {
        tmp27.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(144, null);
        tmp27.tail = tmp27.tail.next;
        return tmp27
      }
      tmp27 = runtime.resetDepth(tmp27, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp28 = NofibPrelude.append(tmp18, tmp27);
      if (tmp28 instanceof runtime.EffectSig.class) {
        tmp28.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(145, null);
        tmp28.tail = tmp28.tail.next;
        return tmp28
      }
      tmp28 = runtime.resetDepth(tmp28, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.bracket(n, 0, tmp28)
    } else if (ter2 instanceof lambda.Thunk.class) {
      param0 = ter2.t;
      param1 = ter2.e;
      t7 = param0;
      e1 = param1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp29 = lambda.ppn(3, t7);
      if (tmp29 instanceof runtime.EffectSig.class) {
        tmp29.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(146, null);
        tmp29.tail = tmp29.tail.next;
        return tmp29
      }
      tmp29 = runtime.resetDepth(tmp29, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp30 = NofibPrelude.nofibStringToList("::");
      if (tmp30 instanceof runtime.EffectSig.class) {
        tmp30.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(147, null);
        tmp30.tail = tmp30.tail.next;
        return tmp30
      }
      tmp30 = runtime.resetDepth(tmp30, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp31 = lambda.ppenv(e1);
      if (tmp31 instanceof runtime.EffectSig.class) {
        tmp31.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(148, null);
        tmp31.tail = tmp31.tail.next;
        return tmp31
      }
      tmp31 = runtime.resetDepth(tmp31, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp32 = NofibPrelude.append(tmp30, tmp31);
      if (tmp32 instanceof runtime.EffectSig.class) {
        tmp32.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(149, null);
        tmp32.tail = tmp32.tail.next;
        return tmp32
      }
      tmp32 = runtime.resetDepth(tmp32, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp33 = NofibPrelude.append(tmp29, tmp32);
      if (tmp33 instanceof runtime.EffectSig.class) {
        tmp33.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(150, null);
        tmp33.tail = tmp33.tail.next;
        return tmp33
      }
      tmp33 = runtime.resetDepth(tmp33, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.bracket(n, 0, tmp33)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp34 = new globalThis.Error("match error");
      if (tmp34 instanceof runtime.EffectSig.class) {
        tmp34.tail.next = new Cont$func$ppn$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_3894_4515$1.class(151, null);
        tmp34.tail = tmp34.tail.next;
        return tmp34
      }
      tmp34 = runtime.resetDepth(tmp34, curDepth);
      throw tmp34;
    }
  } 
  static pp(t7) {
    let stackDelayRes, Cont$func$pp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4521_4538$1;
    Cont$func$pp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4521_4538$1 = function Cont$func$pp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4521_4538$(pc1, next1) { return new Cont$func$pp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4521_4538$.class(pc1, next1); };
    Cont$func$pp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4521_4538$1.class = class Cont$func$pp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4521_4538$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp1;
        tmp1 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 153) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 153) {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.ppn(0, t7)
          }
          break;
        }
      }
      toString() { return "Cont$func$pp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4521_4538$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$pp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4521_4538$1.class(153, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return lambda.ppn(0, t7)
  } 
  static ppenv(env3) {
    let tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, Cont$func$ppenv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4544_4724$1;
    Cont$func$ppenv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4544_4724$1 = function Cont$func$ppenv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4544_4724$(pc1, next1) { return new Cont$func$ppenv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4544_4724$.class(pc1, next1); };
    Cont$func$ppenv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4544_4724$1.class = class Cont$func$ppenv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4544_4724$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp6;
        tmp6 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 154) {
          stackDelayRes = value$;
        } else if (this.pc === 155) {
          tmp1 = value$;
        } else if (this.pc === 164) {
          tmp3 = value$;
        } else if (this.pc === 165) {
          tmp4 = value$;
        } else if (this.pc === 166) {
          tmp5 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 154) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = NofibPrelude.nofibStringToList("[");
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 155;
              return tmp1
            }
            this.pc = 155;
            continue contLoop;
          } else if (this.pc === 155) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            tmp2 = (caseScrut) => {
              let first1, first0, v2, t8, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth1, tmp11, stackDelayRes1, Cont$lambda$9;
              Cont$lambda$9 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$9.class = class Cont$lambda$16 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp12;
                  tmp12 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 156) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 162) {
                    tmp11 = value$1;
                  } else if (this.pc === 157) {
                    tmp6 = value$1;
                  } else if (this.pc === 158) {
                    tmp7 = value$1;
                  } else if (this.pc === 159) {
                    tmp8 = value$1;
                  } else if (this.pc === 160) {
                    tmp9 = value$1;
                  } else if (this.pc === 161) {
                    tmp10 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 156) {
                      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                        first0 = caseScrut[0];
                        first1 = caseScrut[1];
                        v2 = first0;
                        t8 = first1;
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp6 = NofibPrelude.nofibStringToList("=");
                        if (tmp6 instanceof runtime.EffectSig.class) {
                          this.pc = 157;
                          return tmp6
                        }
                        this.pc = 157;
                        continue contLoop1;
                      } else {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp11 = new globalThis.Error("match error");
                        if (tmp11 instanceof runtime.EffectSig.class) {
                          this.pc = 162;
                          return tmp11
                        }
                        this.pc = 162;
                        continue contLoop1;
                      }
                      this.pc = 163;
                      continue contLoop1;
                    } else if (this.pc === 163) {
                      break contLoop1;
                    } else if (this.pc === 162) {
                      tmp11 = runtime.resetDepth(tmp11, curDepth1);
                      throw tmp11;
                    } else if (this.pc === 157) {
                      tmp6 = runtime.resetDepth(tmp6, curDepth1);
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp7 = lambda.pp(t8);
                      if (tmp7 instanceof runtime.EffectSig.class) {
                        this.pc = 158;
                        return tmp7
                      }
                      this.pc = 158;
                      continue contLoop1;
                    } else if (this.pc === 158) {
                      tmp7 = runtime.resetDepth(tmp7, curDepth1);
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp8 = NofibPrelude.nofibStringToList(", ");
                      if (tmp8 instanceof runtime.EffectSig.class) {
                        this.pc = 159;
                        return tmp8
                      }
                      this.pc = 159;
                      continue contLoop1;
                    } else if (this.pc === 159) {
                      tmp8 = runtime.resetDepth(tmp8, curDepth1);
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp9 = NofibPrelude.append(tmp7, tmp8);
                      if (tmp9 instanceof runtime.EffectSig.class) {
                        this.pc = 160;
                        return tmp9
                      }
                      this.pc = 160;
                      continue contLoop1;
                    } else if (this.pc === 160) {
                      tmp9 = runtime.resetDepth(tmp9, curDepth1);
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp10 = NofibPrelude.append(tmp6, tmp9);
                      if (tmp10 instanceof runtime.EffectSig.class) {
                        this.pc = 161;
                        return tmp10
                      }
                      this.pc = 161;
                      continue contLoop1;
                    } else if (this.pc === 161) {
                      tmp10 = runtime.resetDepth(tmp10, curDepth1);
                      runtime.stackDepth = runtime.stackDepth + 1;
                      this.completed = true;
                      return NofibPrelude.append(v2, tmp10)
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              curDepth1 = runtime.stackDepth;
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$9.class(156, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                first0 = caseScrut[0];
                first1 = caseScrut[1];
                v2 = first0;
                t8 = first1;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp6 = NofibPrelude.nofibStringToList("=");
                if (tmp6 instanceof runtime.EffectSig.class) {
                  tmp6.tail.next = new Cont$lambda$9.class(157, null);
                  tmp6.tail = tmp6.tail.next;
                  return tmp6
                }
                tmp6 = runtime.resetDepth(tmp6, curDepth1);
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp7 = lambda.pp(t8);
                if (tmp7 instanceof runtime.EffectSig.class) {
                  tmp7.tail.next = new Cont$lambda$9.class(158, null);
                  tmp7.tail = tmp7.tail.next;
                  return tmp7
                }
                tmp7 = runtime.resetDepth(tmp7, curDepth1);
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp8 = NofibPrelude.nofibStringToList(", ");
                if (tmp8 instanceof runtime.EffectSig.class) {
                  tmp8.tail.next = new Cont$lambda$9.class(159, null);
                  tmp8.tail = tmp8.tail.next;
                  return tmp8
                }
                tmp8 = runtime.resetDepth(tmp8, curDepth1);
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp9 = NofibPrelude.append(tmp7, tmp8);
                if (tmp9 instanceof runtime.EffectSig.class) {
                  tmp9.tail.next = new Cont$lambda$9.class(160, null);
                  tmp9.tail = tmp9.tail.next;
                  return tmp9
                }
                tmp9 = runtime.resetDepth(tmp9, curDepth1);
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp10 = NofibPrelude.append(tmp6, tmp9);
                if (tmp10 instanceof runtime.EffectSig.class) {
                  tmp10.tail.next = new Cont$lambda$9.class(161, null);
                  tmp10.tail = tmp10.tail.next;
                  return tmp10
                }
                tmp10 = runtime.resetDepth(tmp10, curDepth1);
                runtime.stackDepth = runtime.stackDepth + 1;
                return NofibPrelude.append(v2, tmp10)
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp11 = new globalThis.Error("match error");
                if (tmp11 instanceof runtime.EffectSig.class) {
                  tmp11.tail.next = new Cont$lambda$9.class(162, null);
                  tmp11.tail = tmp11.tail.next;
                  return tmp11
                }
                tmp11 = runtime.resetDepth(tmp11, curDepth1);
                throw tmp11;
              }
            };
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = NofibPrelude.flatMap(tmp2, env3);
            if (tmp3 instanceof runtime.EffectSig.class) {
              this.pc = 164;
              return tmp3
            }
            this.pc = 164;
            continue contLoop;
          } else if (this.pc === 164) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = NofibPrelude.nofibStringToList("]");
            if (tmp4 instanceof runtime.EffectSig.class) {
              this.pc = 165;
              return tmp4
            }
            this.pc = 165;
            continue contLoop;
          } else if (this.pc === 165) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp5 = NofibPrelude.append(tmp3, tmp4);
            if (tmp5 instanceof runtime.EffectSig.class) {
              this.pc = 166;
              return tmp5
            }
            this.pc = 166;
            continue contLoop;
          } else if (this.pc === 166) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return NofibPrelude.append(tmp1, tmp5)
          }
          break;
        }
      }
      toString() { return "Cont$func$ppenv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4544_4724$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$ppenv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4544_4724$1.class(154, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = NofibPrelude.nofibStringToList("[");
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.tail.next = new Cont$func$ppenv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4544_4724$1.class(155, null);
      tmp1.tail = tmp1.tail.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    tmp2 = (caseScrut) => {
      let first1, first0, v2, t8, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth1, tmp11, stackDelayRes1, Cont$lambda$9;
      Cont$lambda$9 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
      Cont$lambda$9.class = class Cont$lambda$16 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp12;
          tmp12 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 156) {
            stackDelayRes1 = value$;
          } else if (this.pc === 162) {
            tmp11 = value$;
          } else if (this.pc === 157) {
            tmp6 = value$;
          } else if (this.pc === 158) {
            tmp7 = value$;
          } else if (this.pc === 159) {
            tmp8 = value$;
          } else if (this.pc === 160) {
            tmp9 = value$;
          } else if (this.pc === 161) {
            tmp10 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 156) {
              if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                first0 = caseScrut[0];
                first1 = caseScrut[1];
                v2 = first0;
                t8 = first1;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp6 = NofibPrelude.nofibStringToList("=");
                if (tmp6 instanceof runtime.EffectSig.class) {
                  this.pc = 157;
                  return tmp6
                }
                this.pc = 157;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp11 = new globalThis.Error("match error");
                if (tmp11 instanceof runtime.EffectSig.class) {
                  this.pc = 162;
                  return tmp11
                }
                this.pc = 162;
                continue contLoop;
              }
              this.pc = 163;
              continue contLoop;
            } else if (this.pc === 163) {
              break contLoop;
            } else if (this.pc === 162) {
              tmp11 = runtime.resetDepth(tmp11, curDepth1);
              throw tmp11;
            } else if (this.pc === 157) {
              tmp6 = runtime.resetDepth(tmp6, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp7 = lambda.pp(t8);
              if (tmp7 instanceof runtime.EffectSig.class) {
                this.pc = 158;
                return tmp7
              }
              this.pc = 158;
              continue contLoop;
            } else if (this.pc === 158) {
              tmp7 = runtime.resetDepth(tmp7, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp8 = NofibPrelude.nofibStringToList(", ");
              if (tmp8 instanceof runtime.EffectSig.class) {
                this.pc = 159;
                return tmp8
              }
              this.pc = 159;
              continue contLoop;
            } else if (this.pc === 159) {
              tmp8 = runtime.resetDepth(tmp8, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp9 = NofibPrelude.append(tmp7, tmp8);
              if (tmp9 instanceof runtime.EffectSig.class) {
                this.pc = 160;
                return tmp9
              }
              this.pc = 160;
              continue contLoop;
            } else if (this.pc === 160) {
              tmp9 = runtime.resetDepth(tmp9, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp10 = NofibPrelude.append(tmp6, tmp9);
              if (tmp10 instanceof runtime.EffectSig.class) {
                this.pc = 161;
                return tmp10
              }
              this.pc = 161;
              continue contLoop;
            } else if (this.pc === 161) {
              tmp10 = runtime.resetDepth(tmp10, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return NofibPrelude.append(v2, tmp10)
            }
            break;
          }
        }
        toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth1 = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$lambda$9.class(156, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        v2 = first0;
        t8 = first1;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp6 = NofibPrelude.nofibStringToList("=");
        if (tmp6 instanceof runtime.EffectSig.class) {
          tmp6.tail.next = new Cont$lambda$9.class(157, null);
          tmp6.tail = tmp6.tail.next;
          return tmp6
        }
        tmp6 = runtime.resetDepth(tmp6, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp7 = lambda.pp(t8);
        if (tmp7 instanceof runtime.EffectSig.class) {
          tmp7.tail.next = new Cont$lambda$9.class(158, null);
          tmp7.tail = tmp7.tail.next;
          return tmp7
        }
        tmp7 = runtime.resetDepth(tmp7, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp8 = NofibPrelude.nofibStringToList(", ");
        if (tmp8 instanceof runtime.EffectSig.class) {
          tmp8.tail.next = new Cont$lambda$9.class(159, null);
          tmp8.tail = tmp8.tail.next;
          return tmp8
        }
        tmp8 = runtime.resetDepth(tmp8, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp9 = NofibPrelude.append(tmp7, tmp8);
        if (tmp9 instanceof runtime.EffectSig.class) {
          tmp9.tail.next = new Cont$lambda$9.class(160, null);
          tmp9.tail = tmp9.tail.next;
          return tmp9
        }
        tmp9 = runtime.resetDepth(tmp9, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp10 = NofibPrelude.append(tmp6, tmp9);
        if (tmp10 instanceof runtime.EffectSig.class) {
          tmp10.tail.next = new Cont$lambda$9.class(161, null);
          tmp10.tail = tmp10.tail.next;
          return tmp10
        }
        tmp10 = runtime.resetDepth(tmp10, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.append(v2, tmp10)
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp11 = new globalThis.Error("match error");
        if (tmp11 instanceof runtime.EffectSig.class) {
          tmp11.tail.next = new Cont$lambda$9.class(162, null);
          tmp11.tail = tmp11.tail.next;
          return tmp11
        }
        tmp11 = runtime.resetDepth(tmp11, curDepth1);
        throw tmp11;
      }
    };
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp3 = NofibPrelude.flatMap(tmp2, env3);
    if (tmp3 instanceof runtime.EffectSig.class) {
      tmp3.tail.next = new Cont$func$ppenv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4544_4724$1.class(164, null);
      tmp3.tail = tmp3.tail.next;
      return tmp3
    }
    tmp3 = runtime.resetDepth(tmp3, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp4 = NofibPrelude.nofibStringToList("]");
    if (tmp4 instanceof runtime.EffectSig.class) {
      tmp4.tail.next = new Cont$func$ppenv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4544_4724$1.class(165, null);
      tmp4.tail = tmp4.tail.next;
      return tmp4
    }
    tmp4 = runtime.resetDepth(tmp4, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp5 = NofibPrelude.append(tmp3, tmp4);
    if (tmp5 instanceof runtime.EffectSig.class) {
      tmp5.tail.next = new Cont$func$ppenv$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_4544_4724$1.class(166, null);
      tmp5.tail = tmp5.tail.next;
      return tmp5
    }
    tmp5 = runtime.resetDepth(tmp5, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.append(tmp1, tmp5)
  } 
  static showTerm(t8) {
    let param0, a5, tmp1, tmp2, tmp3, curDepth, tmp4, stackDelayRes, Cont$func$showTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5886_5982$1;
    Cont$func$showTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5886_5982$1 = function Cont$func$showTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5886_5982$(pc1, next1) { return new Cont$func$showTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5886_5982$.class(pc1, next1); };
    Cont$func$showTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5886_5982$1.class = class Cont$func$showTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5886_5982$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp5;
        tmp5 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 167) {
          stackDelayRes = value$;
        } else if (this.pc === 171) {
          tmp4 = value$;
        } else if (this.pc === 168) {
          tmp1 = value$;
        } else if (this.pc === 169) {
          tmp2 = value$;
        } else if (this.pc === 170) {
          tmp3 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 167) {
            if (t8 instanceof lambda.Con.class) {
              param0 = t8.i;
              a5 = param0;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = NofibPrelude.nofibStringToList("Con ");
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 168;
                return tmp1
              }
              this.pc = 168;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp4 = new globalThis.Error("match error");
              if (tmp4 instanceof runtime.EffectSig.class) {
                this.pc = 171;
                return tmp4
              }
              this.pc = 171;
              continue contLoop;
            }
            this.pc = 172;
            continue contLoop;
          } else if (this.pc === 172) {
            break contLoop;
          } else if (this.pc === 171) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            throw tmp4;
          } else if (this.pc === 168) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = NofibPrelude.stringOfInt(a5);
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 169;
              return tmp2
            }
            this.pc = 169;
            continue contLoop;
          } else if (this.pc === 169) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = NofibPrelude.nofibStringToList(tmp2);
            if (tmp3 instanceof runtime.EffectSig.class) {
              this.pc = 170;
              return tmp3
            }
            this.pc = 170;
            continue contLoop;
          } else if (this.pc === 170) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return NofibPrelude.append(tmp1, tmp3)
          }
          break;
        }
      }
      toString() { return "Cont$func$showTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5886_5982$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$showTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5886_5982$1.class(167, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (t8 instanceof lambda.Con.class) {
      param0 = t8.i;
      a5 = param0;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = NofibPrelude.nofibStringToList("Con ");
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.tail.next = new Cont$func$showTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5886_5982$1.class(168, null);
        tmp1.tail = tmp1.tail.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = NofibPrelude.stringOfInt(a5);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.tail.next = new Cont$func$showTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5886_5982$1.class(169, null);
        tmp2.tail = tmp2.tail.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = NofibPrelude.nofibStringToList(tmp2);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.tail.next = new Cont$func$showTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5886_5982$1.class(170, null);
        tmp3.tail = tmp3.tail.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.append(tmp1, tmp3)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = new globalThis.Error("match error");
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.tail.next = new Cont$func$showTerm$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5886_5982$1.class(171, null);
        tmp4.tail = tmp4.tail.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      throw tmp4;
    }
  } 
  static ev(t9) {
    let envt2, first1, first0, env4, t21, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, curDepth, tmp7, stackDelayRes, Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$1;
    Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$1 = function Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$(pc1, next1) { return new Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$.class(pc1, next1); };
    Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$1.class = class Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp8;
        tmp8 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 173) {
          stackDelayRes = value$;
        } else if (this.pc === 174) {
          tmp1 = value$;
        } else if (this.pc === 175) {
          tmp2 = value$;
        } else if (this.pc === 180) {
          tmp7 = value$;
        } else if (this.pc === 176) {
          tmp3 = value$;
        } else if (this.pc === 177) {
          tmp4 = value$;
        } else if (this.pc === 178) {
          tmp5 = value$;
        } else if (this.pc === 179) {
          tmp6 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 173) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = lambda.traverseTerm(t9);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 174;
              return tmp1
            }
            this.pc = 174;
            continue contLoop;
          } else if (this.pc === 174) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = lambda.myRunState(tmp1, NofibPrelude.Nil);
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 175;
              return tmp2
            }
            this.pc = 175;
            continue contLoop;
          } else if (this.pc === 175) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            envt2 = tmp2;
            if (globalThis.Array.isArray(envt2) && envt2.length === 2) {
              first0 = envt2[0];
              first1 = envt2[1];
              env4 = first0;
              t21 = first1;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp3 = lambda.pp(t21);
              if (tmp3 instanceof runtime.EffectSig.class) {
                this.pc = 176;
                return tmp3
              }
              this.pc = 176;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp7 = new globalThis.Error("match error");
              if (tmp7 instanceof runtime.EffectSig.class) {
                this.pc = 180;
                return tmp7
              }
              this.pc = 180;
              continue contLoop;
            }
            this.pc = 181;
            continue contLoop;
          } else if (this.pc === 181) {
            break contLoop;
          } else if (this.pc === 180) {
            tmp7 = runtime.resetDepth(tmp7, curDepth);
            throw tmp7;
          } else if (this.pc === 176) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = NofibPrelude.nofibStringToList("  ");
            if (tmp4 instanceof runtime.EffectSig.class) {
              this.pc = 177;
              return tmp4
            }
            this.pc = 177;
            continue contLoop;
          } else if (this.pc === 177) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp5 = lambda.ppenv(env4);
            if (tmp5 instanceof runtime.EffectSig.class) {
              this.pc = 178;
              return tmp5
            }
            this.pc = 178;
            continue contLoop;
          } else if (this.pc === 178) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp6 = NofibPrelude.append(tmp4, tmp5);
            if (tmp6 instanceof runtime.EffectSig.class) {
              this.pc = 179;
              return tmp6
            }
            this.pc = 179;
            continue contLoop;
          } else if (this.pc === 179) {
            tmp6 = runtime.resetDepth(tmp6, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return NofibPrelude.append(tmp3, tmp6)
          }
          break;
        }
      }
      toString() { return "Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$1.class(173, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = lambda.traverseTerm(t9);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.tail.next = new Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$1.class(174, null);
      tmp1.tail = tmp1.tail.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = lambda.myRunState(tmp1, NofibPrelude.Nil);
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.tail.next = new Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$1.class(175, null);
      tmp2.tail = tmp2.tail.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    envt2 = tmp2;
    if (globalThis.Array.isArray(envt2) && envt2.length === 2) {
      first0 = envt2[0];
      first1 = envt2[1];
      env4 = first0;
      t21 = first1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = lambda.pp(t21);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.tail.next = new Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$1.class(176, null);
        tmp3.tail = tmp3.tail.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = NofibPrelude.nofibStringToList("  ");
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.tail.next = new Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$1.class(177, null);
        tmp4.tail = tmp4.tail.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp5 = lambda.ppenv(env4);
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.tail.next = new Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$1.class(178, null);
        tmp5.tail = tmp5.tail.next;
        return tmp5
      }
      tmp5 = runtime.resetDepth(tmp5, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp6 = NofibPrelude.append(tmp4, tmp5);
      if (tmp6 instanceof runtime.EffectSig.class) {
        tmp6.tail.next = new Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$1.class(179, null);
        tmp6.tail = tmp6.tail.next;
        return tmp6
      }
      tmp6 = runtime.resetDepth(tmp6, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.append(tmp3, tmp6)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp7 = new globalThis.Error("match error");
      if (tmp7 instanceof runtime.EffectSig.class) {
        tmp7.tail.next = new Cont$func$ev$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_5988_6119$1.class(180, null);
        tmp7.tail = tmp7.tail.next;
        return tmp7
      }
      tmp7 = runtime.resetDepth(tmp7, curDepth);
      throw tmp7;
    }
  } 
  static mainSimple(args) {
    let scrut, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$1;
    Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$1 = function Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$(pc1, next1) { return new Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$.class(pc1, next1); };
    Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$1.class = class Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp6;
        tmp6 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 182) {
          stackDelayRes = value$;
        } else if (this.pc === 183) {
          scrut = value$;
        } else if (this.pc === 185) {
          tmp1 = value$;
        } else if (this.pc === 186) {
          tmp2 = value$;
        } else if (this.pc === 187) {
          tmp3 = value$;
        } else if (this.pc === 188) {
          tmp4 = value$;
        } else if (this.pc === 184) {
          tmp5 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 182) {
            runtime.stackDepth = runtime.stackDepth + 1;
            scrut = NofibPrelude.null_(args);
            if (scrut instanceof runtime.EffectSig.class) {
              this.pc = 183;
              return scrut
            }
            this.pc = 183;
            continue contLoop;
          } else if (this.pc === 183) {
            scrut = runtime.resetDepth(scrut, curDepth);
            if (scrut === true) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp5 = globalThis.Error("Args: number-to-sum-up-to");
              if (tmp5 instanceof runtime.EffectSig.class) {
                this.pc = 184;
                return tmp5
              }
              this.pc = 184;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = NofibPrelude.head(args);
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 185;
                return tmp1
              }
              this.pc = 185;
              continue contLoop;
            }
            this.pc = 189;
            continue contLoop;
          } else if (this.pc === 189) {
            break contLoop;
          } else if (this.pc === 185) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = lambda.Con(tmp1);
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 186;
              return tmp2
            }
            this.pc = 186;
            continue contLoop;
          } else if (this.pc === 186) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = lambda.App(lambda.#sum0, tmp2);
            if (tmp3 instanceof runtime.EffectSig.class) {
              this.pc = 187;
              return tmp3
            }
            this.pc = 187;
            continue contLoop;
          } else if (this.pc === 187) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = lambda.simpleEval(NofibPrelude.Nil, tmp3);
            if (tmp4 instanceof runtime.EffectSig.class) {
              this.pc = 188;
              return tmp4
            }
            this.pc = 188;
            continue contLoop;
          } else if (this.pc === 188) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.showTerm(tmp4)
          } else if (this.pc === 184) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            throw tmp5;
          }
          break;
        }
      }
      toString() { return "Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$1.class(182, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    scrut = NofibPrelude.null_(args);
    if (scrut instanceof runtime.EffectSig.class) {
      scrut.tail.next = new Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$1.class(183, null);
      scrut.tail = scrut.tail.next;
      return scrut
    }
    scrut = runtime.resetDepth(scrut, curDepth);
    if (scrut === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp5 = globalThis.Error("Args: number-to-sum-up-to");
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.tail.next = new Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$1.class(184, null);
        tmp5.tail = tmp5.tail.next;
        return tmp5
      }
      tmp5 = runtime.resetDepth(tmp5, curDepth);
      throw tmp5;
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = NofibPrelude.head(args);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.tail.next = new Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$1.class(185, null);
        tmp1.tail = tmp1.tail.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = lambda.Con(tmp1);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.tail.next = new Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$1.class(186, null);
        tmp2.tail = tmp2.tail.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = lambda.App(lambda.#sum0, tmp2);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.tail.next = new Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$1.class(187, null);
        tmp3.tail = tmp3.tail.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = lambda.simpleEval(NofibPrelude.Nil, tmp3);
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.tail.next = new Cont$func$mainSimple$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6125_6269$1.class(188, null);
        tmp4.tail = tmp4.tail.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.showTerm(tmp4)
    }
  } 
  static mainMonad(args1) {
    let scrut, tmp1, tmp2, tmp3, curDepth, tmp4, stackDelayRes, Cont$func$mainMonad$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6275_6395$1;
    Cont$func$mainMonad$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6275_6395$1 = function Cont$func$mainMonad$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6275_6395$(pc1, next1) { return new Cont$func$mainMonad$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6275_6395$.class(pc1, next1); };
    Cont$func$mainMonad$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6275_6395$1.class = class Cont$func$mainMonad$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6275_6395$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp5;
        tmp5 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 190) {
          stackDelayRes = value$;
        } else if (this.pc === 191) {
          scrut = value$;
        } else if (this.pc === 193) {
          tmp1 = value$;
        } else if (this.pc === 194) {
          tmp2 = value$;
        } else if (this.pc === 195) {
          tmp3 = value$;
        } else if (this.pc === 192) {
          tmp4 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 190) {
            runtime.stackDepth = runtime.stackDepth + 1;
            scrut = NofibPrelude.null_(args1);
            if (scrut instanceof runtime.EffectSig.class) {
              this.pc = 191;
              return scrut
            }
            this.pc = 191;
            continue contLoop;
          } else if (this.pc === 191) {
            scrut = runtime.resetDepth(scrut, curDepth);
            if (scrut === true) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp4 = globalThis.Error("Args: number-to-sum-up-to");
              if (tmp4 instanceof runtime.EffectSig.class) {
                this.pc = 192;
                return tmp4
              }
              this.pc = 192;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = NofibPrelude.head(args1);
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 193;
                return tmp1
              }
              this.pc = 193;
              continue contLoop;
            }
            this.pc = 196;
            continue contLoop;
          } else if (this.pc === 196) {
            break contLoop;
          } else if (this.pc === 193) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = lambda.Con(tmp1);
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 194;
              return tmp2
            }
            this.pc = 194;
            continue contLoop;
          } else if (this.pc === 194) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = lambda.App(lambda.#sum0, tmp2);
            if (tmp3 instanceof runtime.EffectSig.class) {
              this.pc = 195;
              return tmp3
            }
            this.pc = 195;
            continue contLoop;
          } else if (this.pc === 195) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lambda.ev(tmp3)
          } else if (this.pc === 192) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            throw tmp4;
          }
          break;
        }
      }
      toString() { return "Cont$func$mainMonad$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6275_6395$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$mainMonad$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6275_6395$1.class(190, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    scrut = NofibPrelude.null_(args1);
    if (scrut instanceof runtime.EffectSig.class) {
      scrut.tail.next = new Cont$func$mainMonad$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6275_6395$1.class(191, null);
      scrut.tail = scrut.tail.next;
      return scrut
    }
    scrut = runtime.resetDepth(scrut, curDepth);
    if (scrut === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = globalThis.Error("Args: number-to-sum-up-to");
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.tail.next = new Cont$func$mainMonad$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6275_6395$1.class(192, null);
        tmp4.tail = tmp4.tail.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      throw tmp4;
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = NofibPrelude.head(args1);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.tail.next = new Cont$func$mainMonad$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6275_6395$1.class(193, null);
        tmp1.tail = tmp1.tail.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = lambda.Con(tmp1);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.tail.next = new Cont$func$mainMonad$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6275_6395$1.class(194, null);
        tmp2.tail = tmp2.tail.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = lambda.App(lambda.#sum0, tmp2);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.tail.next = new Cont$func$mainMonad$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6275_6395$1.class(195, null);
        tmp3.tail = tmp3.tail.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lambda.ev(tmp3)
    }
  } 
  static testLambda_nofib(n1) {
    let tmp1, tmp2, tmp3, tmp4, curDepth, stackDelayRes, Cont$func$testLambda_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6401_6466$1;
    Cont$func$testLambda_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6401_6466$1 = function Cont$func$testLambda_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6401_6466$(pc1, next1) { return new Cont$func$testLambda_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6401_6466$.class(pc1, next1); };
    Cont$func$testLambda_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6401_6466$1.class = class Cont$func$testLambda_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6401_6466$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp5;
        tmp5 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 197) {
          stackDelayRes = value$;
        } else if (this.pc === 198) {
          tmp1 = value$;
        } else if (this.pc === 199) {
          tmp2 = value$;
        } else if (this.pc === 200) {
          tmp3 = value$;
        } else if (this.pc === 201) {
          tmp4 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 197) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = NofibPrelude.Cons(n1, NofibPrelude.Nil);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 198;
              return tmp1
            }
            this.pc = 198;
            continue contLoop;
          } else if (this.pc === 198) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = lambda.mainSimple(tmp1);
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 199;
              return tmp2
            }
            this.pc = 199;
            continue contLoop;
          } else if (this.pc === 199) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = NofibPrelude.Cons(n1, NofibPrelude.Nil);
            if (tmp3 instanceof runtime.EffectSig.class) {
              this.pc = 200;
              return tmp3
            }
            this.pc = 200;
            continue contLoop;
          } else if (this.pc === 200) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = lambda.mainMonad(tmp3);
            if (tmp4 instanceof runtime.EffectSig.class) {
              this.pc = 201;
              return tmp4
            }
            this.pc = 201;
            continue contLoop;
          } else if (this.pc === 201) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            this.completed = true;
            return [
              tmp2,
              tmp4
            ]
          }
          break;
        }
      }
      toString() { return "Cont$func$testLambda_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6401_6466$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$testLambda_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6401_6466$1.class(197, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = NofibPrelude.Cons(n1, NofibPrelude.Nil);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.tail.next = new Cont$func$testLambda_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6401_6466$1.class(198, null);
      tmp1.tail = tmp1.tail.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = lambda.mainSimple(tmp1);
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.tail.next = new Cont$func$testLambda_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6401_6466$1.class(199, null);
      tmp2.tail = tmp2.tail.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp3 = NofibPrelude.Cons(n1, NofibPrelude.Nil);
    if (tmp3 instanceof runtime.EffectSig.class) {
      tmp3.tail.next = new Cont$func$testLambda_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6401_6466$1.class(200, null);
      tmp3.tail = tmp3.tail.next;
      return tmp3
    }
    tmp3 = runtime.resetDepth(tmp3, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp4 = lambda.mainMonad(tmp3);
    if (tmp4 instanceof runtime.EffectSig.class) {
      tmp4.tail.next = new Cont$func$testLambda_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_lambda$_mls_L0_6401_6466$1.class(201, null);
      tmp4.tail = tmp4.tail.next;
      return tmp4
    }
    tmp4 = runtime.resetDepth(tmp4, curDepth);
    return [
      tmp2,
      tmp4
    ]
  }
  static toString() { return "lambda"; }
};
let lambda = lambda1; export default lambda;
