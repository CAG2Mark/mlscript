import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import fs from "fs";
import NofibPrelude from "./NofibPrelude.mjs";
import BenchmarkPrelude from "./BenchmarkPrelude.mjs";
let treejoin1;
treejoin1 = class treejoin {
  static {
    let res, handleBlock$;
    this.Tree = class Tree {
      constructor() {}
      toString() { return "Tree"; }
    };
    this.Node = function Node(k1, l1, r1) { return new Node.class(k1, l1, r1); };
    this.Node.class = class Node extends treejoin.Tree {
      constructor(k, l, r) {
        super();
        this.k = k;
        this.l = l;
        this.r = r;
      }
      toString() { return "Node(" + globalThis.Predef.render(this.k) + ", " + globalThis.Predef.render(this.l) + ", " + globalThis.Predef.render(this.r) + ")"; }
    };
    this.Leaf = function Leaf(k1, e1) { return new Leaf.class(k1, e1); };
    this.Leaf.class = class Leaf extends treejoin.Tree {
      constructor(k, e) {
        super();
        this.k = k;
        this.e = e;
      }
      toString() { return "Leaf(" + globalThis.Predef.render(this.k) + ", " + globalThis.Predef.render(this.e) + ")"; }
    };
    const Empty$class = class Empty extends treejoin.Tree {
      constructor() {
        super();
      }
      toString() { return "Empty"; }
    };
    this.Empty = new Empty$class;
    this.Empty.class = Empty$class;
    handleBlock$ = function handleBlock$() {
      let stackHandler, res1, Cont$handleBlock$stackHandler$1, StackDelay$1;
      StackDelay$1 = class StackDelay$ extends runtime.StackDelay {
        constructor() {
          let tmp;
          tmp = super();
        }
        perform() {
          return runtime.mkEffect(stackHandler, (resume, handleBlock) => {
            let res2, Cont$handler$stackHandler$1;
            Cont$handler$stackHandler$1 = function Cont$handler$stackHandler$(pc1, next1) { return new Cont$handler$stackHandler$.class(pc1, next1); };
            Cont$handler$stackHandler$1.class = class Cont$handler$stackHandler$ extends runtime.Cont.class {
              constructor(pc, next) {
                let tmp;
                tmp = super(next, false);
                this.pc = pc;
                this.next = next;
              }
              resume(value$) {
                if (this.pc === 59) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 59) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 60;
                    continue contLoop;
                  } else if (this.pc === 60) {
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
              handleBlock.contHead.next = new Cont$handler$stackHandler$1.class(59, handleBlock.contHead.next);
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
      stackHandler = new StackDelay$1();
      Cont$handleBlock$stackHandler$1 = function Cont$handleBlock$stackHandler$(pc1, next1) { return new Cont$handleBlock$stackHandler$.class(pc1, next1); };
      Cont$handleBlock$stackHandler$1.class = class Cont$handleBlock$stackHandler$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp;
          tmp = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 57) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 57) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 58;
              continue contLoop;
            } else if (this.pc === 58) {
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
      res1 = BenchmarkPrelude.benchmark(() => {
        let tmp, curDepth, stackDelayRes, Cont$lambda$2;
        Cont$lambda$2 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
        Cont$lambda$2.class = class Cont$lambda$ extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp1;
            tmp1 = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 55) {
              stackDelayRes = value$;
            } else if (this.pc === 56) {
              tmp = value$;
            }
            contLoop: while (true) {
              if (this.pc === 55) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp = treejoin.testTreejoin_nofib(0);
                if (tmp instanceof runtime.EffectSig.class) {
                  this.pc = 56;
                  return tmp
                }
                this.pc = 56;
                continue contLoop;
              } else if (this.pc === 56) {
                tmp = runtime.resetDepth(tmp, curDepth);
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return runtime.safeCall(tmp.toString())
              }
              break;
            }
          }
          toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        curDepth = runtime.stackDepth;
        stackDelayRes = runtime.checkDepth();
        if (stackDelayRes instanceof runtime.EffectSig.class) {
          stackDelayRes.tail.next = new Cont$lambda$2.class(55, null);
          stackDelayRes.tail = stackDelayRes.tail.next;
          return stackDelayRes
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp = treejoin.testTreejoin_nofib(0);
        if (tmp instanceof runtime.EffectSig.class) {
          tmp.tail.next = new Cont$lambda$2.class(56, null);
          tmp.tail = tmp.tail.next;
          return tmp
        }
        tmp = runtime.resetDepth(tmp, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(tmp.toString())
      });
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$1(57, null);
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
  static isSpace(c) {
    let tmp, tmp1;
    tmp = c === " ";
    tmp1 = c === "\n";
    return tmp || tmp1
  } 
  static isDigit(c1) {
    let n, tmp, tmp1, tmp2, curDepth, stackDelayRes, Cont$func$isDigit$treejoin$_mls_L0_185_248$1;
    Cont$func$isDigit$treejoin$_mls_L0_185_248$1 = function Cont$func$isDigit$treejoin$_mls_L0_185_248$(pc1, next1) { return new Cont$func$isDigit$treejoin$_mls_L0_185_248$.class(pc1, next1); };
    Cont$func$isDigit$treejoin$_mls_L0_185_248$1.class = class Cont$func$isDigit$treejoin$_mls_L0_185_248$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp3;
        tmp3 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 0) {
          stackDelayRes = value$;
        } else if (this.pc === 1) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 0) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = runtime.safeCall(c1.codePointAt(0));
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 1;
              return tmp
            }
            this.pc = 1;
            continue contLoop;
          } else if (this.pc === 1) {
            tmp = runtime.resetDepth(tmp, curDepth);
            n = tmp;
            tmp1 = n >= 48;
            tmp2 = n <= 57;
            this.completed = true;
            return tmp1 && tmp2
          }
          break;
        }
      }
      toString() { return "Cont$func$isDigit$treejoin$_mls_L0_185_248$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$isDigit$treejoin$_mls_L0_185_248$1.class(0, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = runtime.safeCall(c1.codePointAt(0));
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.tail.next = new Cont$func$isDigit$treejoin$_mls_L0_185_248$1.class(1, null);
      tmp.tail = tmp.tail.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    n = tmp;
    tmp1 = n >= 48;
    tmp2 = n <= 57;
    return tmp1 && tmp2
  } 
  static insertT(k, e, t) {
    let param0, param1, k_, k__, l_, scrut, scrut1, param01, param11, param2, k_1, l, r, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, stackDelayRes, Cont$func$insertT$treejoin$_mls_L0_431_769$1;
    Cont$func$insertT$treejoin$_mls_L0_431_769$1 = function Cont$func$insertT$treejoin$_mls_L0_431_769$(pc1, next1) { return new Cont$func$insertT$treejoin$_mls_L0_431_769$.class(pc1, next1); };
    Cont$func$insertT$treejoin$_mls_L0_431_769$1.class = class Cont$func$insertT$treejoin$_mls_L0_431_769$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp7;
        tmp7 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 2) {
          stackDelayRes = value$;
        } else if (this.pc === 9) {
          tmp6 = value$;
        } else if (this.pc === 5) {
          tmp2 = value$;
        } else if (this.pc === 8) {
          tmp5 = value$;
        } else if (this.pc === 7) {
          tmp4 = value$;
        } else if (this.pc === 6) {
          tmp3 = value$;
        } else if (this.pc === 4) {
          tmp1 = value$;
        } else if (this.pc === 3) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 2) {
            if (t instanceof treejoin.Node.class) {
              param01 = t.k;
              param11 = t.l;
              param2 = t.r;
              k_1 = param01;
              l = param11;
              r = param2;
              scrut2 = k <= k_1;
              if (scrut2 === true) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp = treejoin.insertT(k, e, l);
                if (tmp instanceof runtime.EffectSig.class) {
                  this.pc = 3;
                  return tmp
                }
                this.pc = 3;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp1 = treejoin.insertT(k, e, r);
                if (tmp1 instanceof runtime.EffectSig.class) {
                  this.pc = 4;
                  return tmp1
                }
                this.pc = 4;
                continue contLoop;
              }
              this.pc = 10;
              continue contLoop;
            } else if (t instanceof treejoin.Leaf.class) {
              param0 = t.k;
              param1 = t.e;
              k_ = param0;
              k__ = param1;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp2 = treejoin.Leaf(k, e);
              if (tmp2 instanceof runtime.EffectSig.class) {
                this.pc = 5;
                return tmp2
              }
              this.pc = 5;
              continue contLoop;
              this.pc = 10;
              continue contLoop;
            } else if (t instanceof treejoin.Empty.class) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return treejoin.Leaf(k, e);
              this.pc = 10;
              continue contLoop;
              this.pc = 10;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp6 = new globalThis.Error("match error");
              if (tmp6 instanceof runtime.EffectSig.class) {
                this.pc = 9;
                return tmp6
              }
              this.pc = 9;
              continue contLoop;
            }
            this.pc = 10;
            continue contLoop;
          } else if (this.pc === 10) {
            break contLoop;
          } else if (this.pc === 9) {
            tmp6 = runtime.resetDepth(tmp6, curDepth);
            throw tmp6;
          } else if (this.pc === 5) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            l_ = tmp2;
            scrut1 = k < k_;
            if (scrut1 === true) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp3 = treejoin.Leaf(k_, k__);
              if (tmp3 instanceof runtime.EffectSig.class) {
                this.pc = 6;
                return tmp3
              }
              this.pc = 6;
              continue contLoop;
            } else {
              scrut = k > k_;
              if (scrut === true) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp4 = treejoin.Leaf(k_, k__);
                if (tmp4 instanceof runtime.EffectSig.class) {
                  this.pc = 7;
                  return tmp4
                }
                this.pc = 7;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp5 = globalThis.Error("already exist");
                if (tmp5 instanceof runtime.EffectSig.class) {
                  this.pc = 8;
                  return tmp5
                }
                this.pc = 8;
                continue contLoop;
              }
              this.pc = 10;
              continue contLoop;
            }
            this.pc = 10;
            continue contLoop;
          } else if (this.pc === 8) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            throw tmp5;
          } else if (this.pc === 7) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return treejoin.Node(k_, tmp4, l_)
          } else if (this.pc === 6) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return treejoin.Node(k, l_, tmp3)
          } else if (this.pc === 4) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return treejoin.Node(k_1, l, tmp1)
          } else if (this.pc === 3) {
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return treejoin.Node(k_1, tmp, r)
          }
          break;
        }
      }
      toString() { return "Cont$func$insertT$treejoin$_mls_L0_431_769$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$insertT$treejoin$_mls_L0_431_769$1.class(2, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (t instanceof treejoin.Node.class) {
      param01 = t.k;
      param11 = t.l;
      param2 = t.r;
      k_1 = param01;
      l = param11;
      r = param2;
      scrut2 = k <= k_1;
      if (scrut2 === true) {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp = treejoin.insertT(k, e, l);
        if (tmp instanceof runtime.EffectSig.class) {
          tmp.tail.next = new Cont$func$insertT$treejoin$_mls_L0_431_769$1.class(3, null);
          tmp.tail = tmp.tail.next;
          return tmp
        }
        tmp = runtime.resetDepth(tmp, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        return treejoin.Node(k_1, tmp, r)
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp1 = treejoin.insertT(k, e, r);
        if (tmp1 instanceof runtime.EffectSig.class) {
          tmp1.tail.next = new Cont$func$insertT$treejoin$_mls_L0_431_769$1.class(4, null);
          tmp1.tail = tmp1.tail.next;
          return tmp1
        }
        tmp1 = runtime.resetDepth(tmp1, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        return treejoin.Node(k_1, l, tmp1)
      }
    } else if (t instanceof treejoin.Leaf.class) {
      param0 = t.k;
      param1 = t.e;
      k_ = param0;
      k__ = param1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = treejoin.Leaf(k, e);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.tail.next = new Cont$func$insertT$treejoin$_mls_L0_431_769$1.class(5, null);
        tmp2.tail = tmp2.tail.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      l_ = tmp2;
      scrut1 = k < k_;
      if (scrut1 === true) {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp3 = treejoin.Leaf(k_, k__);
        if (tmp3 instanceof runtime.EffectSig.class) {
          tmp3.tail.next = new Cont$func$insertT$treejoin$_mls_L0_431_769$1.class(6, null);
          tmp3.tail = tmp3.tail.next;
          return tmp3
        }
        tmp3 = runtime.resetDepth(tmp3, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        return treejoin.Node(k, l_, tmp3)
      } else {
        scrut = k > k_;
        if (scrut === true) {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp4 = treejoin.Leaf(k_, k__);
          if (tmp4 instanceof runtime.EffectSig.class) {
            tmp4.tail.next = new Cont$func$insertT$treejoin$_mls_L0_431_769$1.class(7, null);
            tmp4.tail = tmp4.tail.next;
            return tmp4
          }
          tmp4 = runtime.resetDepth(tmp4, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          return treejoin.Node(k_, tmp4, l_)
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp5 = globalThis.Error("already exist");
          if (tmp5 instanceof runtime.EffectSig.class) {
            tmp5.tail.next = new Cont$func$insertT$treejoin$_mls_L0_431_769$1.class(8, null);
            tmp5.tail = tmp5.tail.next;
            return tmp5
          }
          tmp5 = runtime.resetDepth(tmp5, curDepth);
          throw tmp5;
        }
      }
    } else if (t instanceof treejoin.Empty.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      return treejoin.Leaf(k, e)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp6 = new globalThis.Error("match error");
      if (tmp6 instanceof runtime.EffectSig.class) {
        tmp6.tail.next = new Cont$func$insertT$treejoin$_mls_L0_431_769$1.class(9, null);
        tmp6.tail = tmp6.tail.next;
        return tmp6
      }
      tmp6 = runtime.resetDepth(tmp6, curDepth);
      throw tmp6;
    }
  } 
  static lookupT(k1, t1) {
    let param0, param1, k_, e1, scrut, param01, param11, param2, k_1, l, r, scrut1, tmp, curDepth, stackDelayRes, Cont$func$lookupT$treejoin$_mls_L0_775_945$1;
    Cont$func$lookupT$treejoin$_mls_L0_775_945$1 = function Cont$func$lookupT$treejoin$_mls_L0_775_945$(pc1, next1) { return new Cont$func$lookupT$treejoin$_mls_L0_775_945$.class(pc1, next1); };
    Cont$func$lookupT$treejoin$_mls_L0_775_945$1.class = class Cont$func$lookupT$treejoin$_mls_L0_775_945$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp1;
        tmp1 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 11) {
          stackDelayRes = value$;
        } else if (this.pc === 12) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 11) {
            if (t1 instanceof treejoin.Node.class) {
              param01 = t1.k;
              param11 = t1.l;
              param2 = t1.r;
              k_1 = param01;
              l = param11;
              r = param2;
              scrut1 = k1 <= k_1;
              if (scrut1 === true) {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return treejoin.lookupT(k1, l)
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return treejoin.lookupT(k1, r)
              }
              this.pc = 13;
              continue contLoop;
            } else if (t1 instanceof treejoin.Leaf.class) {
              param0 = t1.k;
              param1 = t1.e;
              k_ = param0;
              e1 = param1;
              scrut = k1 === k_;
              if (scrut === true) {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return NofibPrelude.Some(e1)
              } else {
                this.completed = true;
                return NofibPrelude.None
              }
              this.pc = 13;
              continue contLoop;
              this.pc = 13;
              continue contLoop;
            } else if (t1 instanceof treejoin.Empty.class) {
              this.completed = true;
              return NofibPrelude.None;
              this.pc = 13;
              continue contLoop;
              this.pc = 13;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = new globalThis.Error("match error");
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 12;
                return tmp
              }
              this.pc = 12;
              continue contLoop;
            }
            this.pc = 13;
            continue contLoop;
          } else if (this.pc === 13) {
            break contLoop;
          } else if (this.pc === 12) {
            tmp = runtime.resetDepth(tmp, curDepth);
            throw tmp;
          }
          break;
        }
      }
      toString() { return "Cont$func$lookupT$treejoin$_mls_L0_775_945$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$lookupT$treejoin$_mls_L0_775_945$1.class(11, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (t1 instanceof treejoin.Node.class) {
      param01 = t1.k;
      param11 = t1.l;
      param2 = t1.r;
      k_1 = param01;
      l = param11;
      r = param2;
      scrut1 = k1 <= k_1;
      if (scrut1 === true) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return treejoin.lookupT(k1, l)
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        return treejoin.lookupT(k1, r)
      }
    } else if (t1 instanceof treejoin.Leaf.class) {
      param0 = t1.k;
      param1 = t1.e;
      k_ = param0;
      e1 = param1;
      scrut = k1 === k_;
      if (scrut === true) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Some(e1)
      } else {
        return NofibPrelude.None
      }
    } else if (t1 instanceof treejoin.Empty.class) {
      return NofibPrelude.None
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = new globalThis.Error("match error");
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.tail.next = new Cont$func$lookupT$treejoin$_mls_L0_775_945$1.class(12, null);
        tmp.tail = tmp.tail.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      throw tmp;
    }
  } 
  static readInt(s) {
    let readInt_, stackDelayRes, Cont$func$readInt$treejoin$_mls_L0_951_1215$1;
    Cont$func$readInt$treejoin$_mls_L0_951_1215$1 = function Cont$func$readInt$treejoin$_mls_L0_951_1215$(pc1, next1) { return new Cont$func$readInt$treejoin$_mls_L0_951_1215$.class(pc1, next1); };
    Cont$func$readInt$treejoin$_mls_L0_951_1215$1.class = class Cont$func$readInt$treejoin$_mls_L0_951_1215$ extends runtime.Cont.class {
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
            return readInt_(0, s)
          }
          break;
        }
      }
      toString() { return "Cont$func$readInt$treejoin$_mls_L0_951_1215$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    readInt_ = function readInt_(n, cs) {
      let s_, param0, param1, c2, cs_, s_1, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, curDepth, stackDelayRes1, Cont$func$readInt_$treejoin$_mls_L0_970_1198$1;
      Cont$func$readInt_$treejoin$_mls_L0_970_1198$1 = function Cont$func$readInt_$treejoin$_mls_L0_970_1198$(pc1, next1) { return new Cont$func$readInt_$treejoin$_mls_L0_970_1198$.class(pc1, next1); };
      Cont$func$readInt_$treejoin$_mls_L0_970_1198$1.class = class Cont$func$readInt_$treejoin$_mls_L0_970_1198$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp7;
          tmp7 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 15) {
            stackDelayRes1 = value$;
          } else if (this.pc === 20) {
            tmp6 = value$;
          } else if (this.pc === 16) {
            scrut = value$;
          } else if (this.pc === 18) {
            tmp4 = value$;
          } else if (this.pc === 19) {
            tmp5 = value$;
          } else if (this.pc === 17) {
            tmp1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 15) {
              if (cs instanceof NofibPrelude.Cons.class) {
                param0 = cs.head;
                param1 = cs.tail;
                c2 = param0;
                cs_ = param1;
                runtime.stackDepth = runtime.stackDepth + 1;
                scrut = treejoin.isDigit(c2);
                if (scrut instanceof runtime.EffectSig.class) {
                  this.pc = 16;
                  return scrut
                }
                this.pc = 16;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp6 = NofibPrelude.dropWhile(treejoin.isSpace, cs);
                if (tmp6 instanceof runtime.EffectSig.class) {
                  this.pc = 20;
                  return tmp6
                }
                this.pc = 20;
                continue contLoop;
              }
              this.pc = 21;
              continue contLoop;
            } else if (this.pc === 21) {
              break contLoop;
            } else if (this.pc === 20) {
              tmp6 = runtime.resetDepth(tmp6, curDepth);
              s_ = tmp6;
              this.completed = true;
              return [
                n,
                s_
              ]
            } else if (this.pc === 16) {
              scrut = runtime.resetDepth(scrut, curDepth);
              if (scrut === true) {
                tmp = n * 10;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp1 = runtime.safeCall(c2.codePointAt(0));
                if (tmp1 instanceof runtime.EffectSig.class) {
                  this.pc = 17;
                  return tmp1
                }
                this.pc = 17;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp4 = NofibPrelude.Cons(c2, cs);
                if (tmp4 instanceof runtime.EffectSig.class) {
                  this.pc = 18;
                  return tmp4
                }
                this.pc = 18;
                continue contLoop;
              }
              this.pc = 21;
              continue contLoop;
            } else if (this.pc === 18) {
              tmp4 = runtime.resetDepth(tmp4, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp5 = NofibPrelude.dropWhile(treejoin.isSpace, tmp4);
              if (tmp5 instanceof runtime.EffectSig.class) {
                this.pc = 19;
                return tmp5
              }
              this.pc = 19;
              continue contLoop;
            } else if (this.pc === 19) {
              tmp5 = runtime.resetDepth(tmp5, curDepth);
              s_1 = tmp5;
              this.completed = true;
              return [
                n,
                s_1
              ]
            } else if (this.pc === 17) {
              tmp1 = runtime.resetDepth(tmp1, curDepth);
              tmp2 = tmp + tmp1;
              tmp3 = tmp2 - 48;
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return readInt_(tmp3, cs_)
            }
            break;
          }
        }
        toString() { return "Cont$func$readInt_$treejoin$_mls_L0_970_1198$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$func$readInt_$treejoin$_mls_L0_970_1198$1.class(15, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      if (cs instanceof NofibPrelude.Cons.class) {
        param0 = cs.head;
        param1 = cs.tail;
        c2 = param0;
        cs_ = param1;
        runtime.stackDepth = runtime.stackDepth + 1;
        scrut = treejoin.isDigit(c2);
        if (scrut instanceof runtime.EffectSig.class) {
          scrut.tail.next = new Cont$func$readInt_$treejoin$_mls_L0_970_1198$1.class(16, null);
          scrut.tail = scrut.tail.next;
          return scrut
        }
        scrut = runtime.resetDepth(scrut, curDepth);
        if (scrut === true) {
          tmp = n * 10;
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp1 = runtime.safeCall(c2.codePointAt(0));
          if (tmp1 instanceof runtime.EffectSig.class) {
            tmp1.tail.next = new Cont$func$readInt_$treejoin$_mls_L0_970_1198$1.class(17, null);
            tmp1.tail = tmp1.tail.next;
            return tmp1
          }
          tmp1 = runtime.resetDepth(tmp1, curDepth);
          tmp2 = tmp + tmp1;
          tmp3 = tmp2 - 48;
          runtime.stackDepth = runtime.stackDepth + 1;
          return readInt_(tmp3, cs_)
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp4 = NofibPrelude.Cons(c2, cs);
          if (tmp4 instanceof runtime.EffectSig.class) {
            tmp4.tail.next = new Cont$func$readInt_$treejoin$_mls_L0_970_1198$1.class(18, null);
            tmp4.tail = tmp4.tail.next;
            return tmp4
          }
          tmp4 = runtime.resetDepth(tmp4, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp5 = NofibPrelude.dropWhile(treejoin.isSpace, tmp4);
          if (tmp5 instanceof runtime.EffectSig.class) {
            tmp5.tail.next = new Cont$func$readInt_$treejoin$_mls_L0_970_1198$1.class(19, null);
            tmp5.tail = tmp5.tail.next;
            return tmp5
          }
          tmp5 = runtime.resetDepth(tmp5, curDepth);
          s_1 = tmp5;
          return [
            n,
            s_1
          ]
        }
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp6 = NofibPrelude.dropWhile(treejoin.isSpace, cs);
        if (tmp6 instanceof runtime.EffectSig.class) {
          tmp6.tail.next = new Cont$func$readInt_$treejoin$_mls_L0_970_1198$1.class(20, null);
          tmp6.tail = tmp6.tail.next;
          return tmp6
        }
        tmp6 = runtime.resetDepth(tmp6, curDepth);
        s_ = tmp6;
        return [
          n,
          s_
        ]
      }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$readInt$treejoin$_mls_L0_951_1215$1.class(14, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return readInt_(0, s)
  } 
  static join(t11, t2, j) {
    let param0, param1, param2, k2, l, r, param01, param11, k3, first2, first1, first0, a, b, c2, scrut, param02, first21, first11, first01, d, e1, f, tmp, curDepth, tmp1, tmp2, tmp3, tmp4, stackDelayRes, Cont$func$join$treejoin$_mls_L0_1221_1459$1;
    Cont$func$join$treejoin$_mls_L0_1221_1459$1 = function Cont$func$join$treejoin$_mls_L0_1221_1459$(pc1, next1) { return new Cont$func$join$treejoin$_mls_L0_1221_1459$.class(pc1, next1); };
    Cont$func$join$treejoin$_mls_L0_1221_1459$1.class = class Cont$func$join$treejoin$_mls_L0_1221_1459$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp5;
        tmp5 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 22) {
          stackDelayRes = value$;
        } else if (this.pc === 28) {
          tmp4 = value$;
        } else if (this.pc === 27) {
          tmp = value$;
        } else if (this.pc === 26) {
          tmp3 = value$;
        } else if (this.pc === 23) {
          scrut = value$;
        } else if (this.pc === 25) {
          tmp2 = value$;
        } else if (this.pc === 24) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 22) {
            if (t11 instanceof treejoin.Empty.class) {
              this.completed = true;
              return j
            } else {
              if (t2 instanceof treejoin.Empty.class) {
                this.completed = true;
                return j
              } else {
                if (t11 instanceof treejoin.Leaf.class) {
                  param01 = t11.k;
                  param11 = t11.e;
                  k3 = param01;
                  if (globalThis.Array.isArray(param11) && param11.length === 3) {
                    first0 = param11[0];
                    first1 = param11[1];
                    first2 = param11[2];
                    a = first0;
                    b = first1;
                    c2 = first2;
                    runtime.stackDepth = runtime.stackDepth + 1;
                    scrut = treejoin.lookupT(c2, t2);
                    if (scrut instanceof runtime.EffectSig.class) {
                      this.pc = 23;
                      return scrut
                    }
                    this.pc = 23;
                    continue contLoop;
                  } else {
                    runtime.stackDepth = runtime.stackDepth + 1;
                    tmp3 = new globalThis.Error("match error");
                    if (tmp3 instanceof runtime.EffectSig.class) {
                      this.pc = 26;
                      return tmp3
                    }
                    this.pc = 26;
                    continue contLoop;
                  }
                  this.pc = 29;
                  continue contLoop;
                } else if (t11 instanceof treejoin.Node.class) {
                  param0 = t11.k;
                  param1 = t11.l;
                  param2 = t11.r;
                  k2 = param0;
                  l = param1;
                  r = param2;
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp = treejoin.join(r, t2, j);
                  if (tmp instanceof runtime.EffectSig.class) {
                    this.pc = 27;
                    return tmp
                  }
                  this.pc = 27;
                  continue contLoop;
                  this.pc = 29;
                  continue contLoop;
                } else {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp4 = new globalThis.Error("match error");
                  if (tmp4 instanceof runtime.EffectSig.class) {
                    this.pc = 28;
                    return tmp4
                  }
                  this.pc = 28;
                  continue contLoop;
                }
                this.pc = 29;
                continue contLoop;
              }
              this.pc = 29;
              continue contLoop;
            }
            this.pc = 29;
            continue contLoop;
          } else if (this.pc === 29) {
            break contLoop;
          } else if (this.pc === 28) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            throw tmp4;
          } else if (this.pc === 27) {
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return treejoin.join(l, t2, tmp)
          } else if (this.pc === 26) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            throw tmp3;
          } else if (this.pc === 23) {
            scrut = runtime.resetDepth(scrut, curDepth);
            if (scrut instanceof NofibPrelude.None.class) {
              this.completed = true;
              return j
            } else if (scrut instanceof NofibPrelude.Some.class) {
              param02 = scrut.x;
              if (globalThis.Array.isArray(param02) && param02.length === 3) {
                first01 = param02[0];
                first11 = param02[1];
                first21 = param02[2];
                d = first01;
                e1 = first11;
                f = first21;
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return treejoin.insertT(c2, [
                  a,
                  b,
                  c2,
                  d,
                  e1
                ], j)
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp1 = new globalThis.Error("match error");
                if (tmp1 instanceof runtime.EffectSig.class) {
                  this.pc = 24;
                  return tmp1
                }
                this.pc = 24;
                continue contLoop;
              }
              this.pc = 29;
              continue contLoop;
              this.pc = 29;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp2 = new globalThis.Error("match error");
              if (tmp2 instanceof runtime.EffectSig.class) {
                this.pc = 25;
                return tmp2
              }
              this.pc = 25;
              continue contLoop;
            }
            this.pc = 29;
            continue contLoop;
          } else if (this.pc === 25) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            throw tmp2;
          } else if (this.pc === 24) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            throw tmp1;
          }
          break;
        }
      }
      toString() { return "Cont$func$join$treejoin$_mls_L0_1221_1459$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$join$treejoin$_mls_L0_1221_1459$1.class(22, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (t11 instanceof treejoin.Empty.class) {
      return j
    } else {
      if (t2 instanceof treejoin.Empty.class) {
        return j
      } else {
        if (t11 instanceof treejoin.Leaf.class) {
          param01 = t11.k;
          param11 = t11.e;
          k3 = param01;
          if (globalThis.Array.isArray(param11) && param11.length === 3) {
            first0 = param11[0];
            first1 = param11[1];
            first2 = param11[2];
            a = first0;
            b = first1;
            c2 = first2;
            runtime.stackDepth = runtime.stackDepth + 1;
            scrut = treejoin.lookupT(c2, t2);
            if (scrut instanceof runtime.EffectSig.class) {
              scrut.tail.next = new Cont$func$join$treejoin$_mls_L0_1221_1459$1.class(23, null);
              scrut.tail = scrut.tail.next;
              return scrut
            }
            scrut = runtime.resetDepth(scrut, curDepth);
            if (scrut instanceof NofibPrelude.None.class) {
              return j
            } else if (scrut instanceof NofibPrelude.Some.class) {
              param02 = scrut.x;
              if (globalThis.Array.isArray(param02) && param02.length === 3) {
                first01 = param02[0];
                first11 = param02[1];
                first21 = param02[2];
                d = first01;
                e1 = first11;
                f = first21;
                runtime.stackDepth = runtime.stackDepth + 1;
                return treejoin.insertT(c2, [
                  a,
                  b,
                  c2,
                  d,
                  e1
                ], j)
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp1 = new globalThis.Error("match error");
                if (tmp1 instanceof runtime.EffectSig.class) {
                  tmp1.tail.next = new Cont$func$join$treejoin$_mls_L0_1221_1459$1.class(24, null);
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
                tmp2.tail.next = new Cont$func$join$treejoin$_mls_L0_1221_1459$1.class(25, null);
                tmp2.tail = tmp2.tail.next;
                return tmp2
              }
              tmp2 = runtime.resetDepth(tmp2, curDepth);
              throw tmp2;
            }
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = new globalThis.Error("match error");
            if (tmp3 instanceof runtime.EffectSig.class) {
              tmp3.tail.next = new Cont$func$join$treejoin$_mls_L0_1221_1459$1.class(26, null);
              tmp3.tail = tmp3.tail.next;
              return tmp3
            }
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            throw tmp3;
          }
        } else if (t11 instanceof treejoin.Node.class) {
          param0 = t11.k;
          param1 = t11.l;
          param2 = t11.r;
          k2 = param0;
          l = param1;
          r = param2;
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp = treejoin.join(r, t2, j);
          if (tmp instanceof runtime.EffectSig.class) {
            tmp.tail.next = new Cont$func$join$treejoin$_mls_L0_1221_1459$1.class(27, null);
            tmp.tail = tmp.tail.next;
            return tmp
          }
          tmp = runtime.resetDepth(tmp, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          return treejoin.join(l, t2, tmp)
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp4 = new globalThis.Error("match error");
          if (tmp4 instanceof runtime.EffectSig.class) {
            tmp4.tail.next = new Cont$func$join$treejoin$_mls_L0_1221_1459$1.class(28, null);
            tmp4.tail = tmp4.tail.next;
            return tmp4
          }
          tmp4 = runtime.resetDepth(tmp4, curDepth);
          throw tmp4;
        }
      }
    }
  } 
  static readTree(fk, s1, t3) {
    let scrut, first1, first0, f, s_, scrut1, first11, first01, g, s__, scrut2, first12, first02, h, s___, e1, k2, tmp, tmp1, curDepth, tmp2, tmp3, tmp4, stackDelayRes, Cont$func$readTree$treejoin$_mls_L0_1465_1696$1;
    Cont$func$readTree$treejoin$_mls_L0_1465_1696$1 = function Cont$func$readTree$treejoin$_mls_L0_1465_1696$(pc1, next1) { return new Cont$func$readTree$treejoin$_mls_L0_1465_1696$.class(pc1, next1); };
    Cont$func$readTree$treejoin$_mls_L0_1465_1696$1.class = class Cont$func$readTree$treejoin$_mls_L0_1465_1696$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp5;
        tmp5 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 30) {
          stackDelayRes = value$;
        } else if (this.pc === 31) {
          scrut = value$;
        } else if (this.pc === 38) {
          tmp4 = value$;
        } else if (this.pc === 32) {
          scrut1 = value$;
        } else if (this.pc === 37) {
          tmp3 = value$;
        } else if (this.pc === 33) {
          scrut2 = value$;
        } else if (this.pc === 36) {
          tmp2 = value$;
        } else if (this.pc === 34) {
          tmp = value$;
        } else if (this.pc === 35) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 30) {
            if (s1 instanceof NofibPrelude.Nil.class) {
              this.completed = true;
              return t3
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              scrut = treejoin.readInt(s1);
              if (scrut instanceof runtime.EffectSig.class) {
                this.pc = 31;
                return scrut
              }
              this.pc = 31;
              continue contLoop;
            }
            this.pc = 39;
            continue contLoop;
          } else if (this.pc === 39) {
            break contLoop;
          } else if (this.pc === 31) {
            scrut = runtime.resetDepth(scrut, curDepth);
            if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
              first0 = scrut[0];
              first1 = scrut[1];
              f = first0;
              s_ = first1;
              runtime.stackDepth = runtime.stackDepth + 1;
              scrut1 = treejoin.readInt(s_);
              if (scrut1 instanceof runtime.EffectSig.class) {
                this.pc = 32;
                return scrut1
              }
              this.pc = 32;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp4 = new globalThis.Error("match error");
              if (tmp4 instanceof runtime.EffectSig.class) {
                this.pc = 38;
                return tmp4
              }
              this.pc = 38;
              continue contLoop;
            }
            this.pc = 39;
            continue contLoop;
          } else if (this.pc === 38) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            throw tmp4;
          } else if (this.pc === 32) {
            scrut1 = runtime.resetDepth(scrut1, curDepth);
            if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
              first01 = scrut1[0];
              first11 = scrut1[1];
              g = first01;
              s__ = first11;
              runtime.stackDepth = runtime.stackDepth + 1;
              scrut2 = treejoin.readInt(s__);
              if (scrut2 instanceof runtime.EffectSig.class) {
                this.pc = 33;
                return scrut2
              }
              this.pc = 33;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp3 = new globalThis.Error("match error");
              if (tmp3 instanceof runtime.EffectSig.class) {
                this.pc = 37;
                return tmp3
              }
              this.pc = 37;
              continue contLoop;
            }
            this.pc = 39;
            continue contLoop;
          } else if (this.pc === 37) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            throw tmp3;
          } else if (this.pc === 33) {
            scrut2 = runtime.resetDepth(scrut2, curDepth);
            if (globalThis.Array.isArray(scrut2) && scrut2.length === 2) {
              first02 = scrut2[0];
              first12 = scrut2[1];
              h = first02;
              s___ = first12;
              e1 = [
                f,
                g,
                h
              ];
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = runtime.safeCall(fk(e1));
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 34;
                return tmp
              }
              this.pc = 34;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp2 = new globalThis.Error("match error");
              if (tmp2 instanceof runtime.EffectSig.class) {
                this.pc = 36;
                return tmp2
              }
              this.pc = 36;
              continue contLoop;
            }
            this.pc = 39;
            continue contLoop;
          } else if (this.pc === 36) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            throw tmp2;
          } else if (this.pc === 34) {
            tmp = runtime.resetDepth(tmp, curDepth);
            k2 = tmp;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = treejoin.insertT(k2, e1, t3);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 35;
              return tmp1
            }
            this.pc = 35;
            continue contLoop;
          } else if (this.pc === 35) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return treejoin.readTree(fk, s___, tmp1)
          }
          break;
        }
      }
      toString() { return "Cont$func$readTree$treejoin$_mls_L0_1465_1696$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$readTree$treejoin$_mls_L0_1465_1696$1.class(30, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (s1 instanceof NofibPrelude.Nil.class) {
      return t3
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      scrut = treejoin.readInt(s1);
      if (scrut instanceof runtime.EffectSig.class) {
        scrut.tail.next = new Cont$func$readTree$treejoin$_mls_L0_1465_1696$1.class(31, null);
        scrut.tail = scrut.tail.next;
        return scrut
      }
      scrut = runtime.resetDepth(scrut, curDepth);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        f = first0;
        s_ = first1;
        runtime.stackDepth = runtime.stackDepth + 1;
        scrut1 = treejoin.readInt(s_);
        if (scrut1 instanceof runtime.EffectSig.class) {
          scrut1.tail.next = new Cont$func$readTree$treejoin$_mls_L0_1465_1696$1.class(32, null);
          scrut1.tail = scrut1.tail.next;
          return scrut1
        }
        scrut1 = runtime.resetDepth(scrut1, curDepth);
        if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
          first01 = scrut1[0];
          first11 = scrut1[1];
          g = first01;
          s__ = first11;
          runtime.stackDepth = runtime.stackDepth + 1;
          scrut2 = treejoin.readInt(s__);
          if (scrut2 instanceof runtime.EffectSig.class) {
            scrut2.tail.next = new Cont$func$readTree$treejoin$_mls_L0_1465_1696$1.class(33, null);
            scrut2.tail = scrut2.tail.next;
            return scrut2
          }
          scrut2 = runtime.resetDepth(scrut2, curDepth);
          if (globalThis.Array.isArray(scrut2) && scrut2.length === 2) {
            first02 = scrut2[0];
            first12 = scrut2[1];
            h = first02;
            s___ = first12;
            e1 = [
              f,
              g,
              h
            ];
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = runtime.safeCall(fk(e1));
            if (tmp instanceof runtime.EffectSig.class) {
              tmp.tail.next = new Cont$func$readTree$treejoin$_mls_L0_1465_1696$1.class(34, null);
              tmp.tail = tmp.tail.next;
              return tmp
            }
            tmp = runtime.resetDepth(tmp, curDepth);
            k2 = tmp;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = treejoin.insertT(k2, e1, t3);
            if (tmp1 instanceof runtime.EffectSig.class) {
              tmp1.tail.next = new Cont$func$readTree$treejoin$_mls_L0_1465_1696$1.class(35, null);
              tmp1.tail = tmp1.tail.next;
              return tmp1
            }
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            return treejoin.readTree(fk, s___, tmp1)
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = new globalThis.Error("match error");
            if (tmp2 instanceof runtime.EffectSig.class) {
              tmp2.tail.next = new Cont$func$readTree$treejoin$_mls_L0_1465_1696$1.class(36, null);
              tmp2.tail = tmp2.tail.next;
              return tmp2
            }
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            throw tmp2;
          }
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp3 = new globalThis.Error("match error");
          if (tmp3 instanceof runtime.EffectSig.class) {
            tmp3.tail.next = new Cont$func$readTree$treejoin$_mls_L0_1465_1696$1.class(37, null);
            tmp3.tail = tmp3.tail.next;
            return tmp3
          }
          tmp3 = runtime.resetDepth(tmp3, curDepth);
          throw tmp3;
        }
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp4 = new globalThis.Error("match error");
        if (tmp4 instanceof runtime.EffectSig.class) {
          tmp4.tail.next = new Cont$func$readTree$treejoin$_mls_L0_1465_1696$1.class(38, null);
          tmp4.tail = tmp4.tail.next;
          return tmp4
        }
        tmp4 = runtime.resetDepth(tmp4, curDepth);
        throw tmp4;
      }
    }
  } 
  static testTreejoin_nofib(n) {
    let c11, c2, a, b, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$1;
    Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$1 = function Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$(pc1, next1) { return new Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$.class(pc1, next1); };
    Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$1.class = class Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp10;
        tmp10 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 40) {
          stackDelayRes = value$;
        } else if (this.pc === 41) {
          tmp = value$;
        } else if (this.pc === 42) {
          tmp1 = value$;
        } else if (this.pc === 43) {
          tmp2 = value$;
        } else if (this.pc === 44) {
          tmp3 = value$;
        } else if (this.pc === 45) {
          tmp4 = value$;
        } else if (this.pc === 46) {
          tmp5 = value$;
        } else if (this.pc === 50) {
          tmp7 = value$;
        } else if (this.pc === 54) {
          tmp9 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 40) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/1500.1"));
            if (tmp instanceof runtime.EffectSig.class) {
              this.pc = 41;
              return tmp
            }
            this.pc = 41;
            continue contLoop;
          } else if (this.pc === 41) {
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = runtime.safeCall(tmp.toString());
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 42;
              return tmp1
            }
            this.pc = 42;
            continue contLoop;
          } else if (this.pc === 42) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = NofibPrelude.nofibStringToList(tmp1);
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 43;
              return tmp2
            }
            this.pc = 43;
            continue contLoop;
          } else if (this.pc === 43) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            c11 = tmp2;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/1500.2"));
            if (tmp3 instanceof runtime.EffectSig.class) {
              this.pc = 44;
              return tmp3
            }
            this.pc = 44;
            continue contLoop;
          } else if (this.pc === 44) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = runtime.safeCall(tmp3.toString());
            if (tmp4 instanceof runtime.EffectSig.class) {
              this.pc = 45;
              return tmp4
            }
            this.pc = 45;
            continue contLoop;
          } else if (this.pc === 45) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp5 = NofibPrelude.nofibStringToList(tmp4);
            if (tmp5 instanceof runtime.EffectSig.class) {
              this.pc = 46;
              return tmp5
            }
            this.pc = 46;
            continue contLoop;
          } else if (this.pc === 46) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            c2 = tmp5;
            tmp6 = (caseScrut) => {
              let first2, first1, first0, xx, tmp10, curDepth1, stackDelayRes1, Cont$lambda$2;
              Cont$lambda$2 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$2.class = class Cont$lambda$3 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp11;
                  tmp11 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 47) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 48) {
                    tmp10 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 47) {
                      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
                        first0 = caseScrut[0];
                        first1 = caseScrut[1];
                        first2 = caseScrut[2];
                        xx = first0;
                        this.completed = true;
                        return xx
                      } else {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp10 = new globalThis.Error("match error");
                        if (tmp10 instanceof runtime.EffectSig.class) {
                          this.pc = 48;
                          return tmp10
                        }
                        this.pc = 48;
                        continue contLoop1;
                      }
                      this.pc = 49;
                      continue contLoop1;
                    } else if (this.pc === 49) {
                      break contLoop1;
                    } else if (this.pc === 48) {
                      tmp10 = runtime.resetDepth(tmp10, curDepth1);
                      throw tmp10;
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              curDepth1 = runtime.stackDepth;
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$2.class(47, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
                first0 = caseScrut[0];
                first1 = caseScrut[1];
                first2 = caseScrut[2];
                xx = first0;
                return xx
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp10 = new globalThis.Error("match error");
                if (tmp10 instanceof runtime.EffectSig.class) {
                  tmp10.tail.next = new Cont$lambda$2.class(48, null);
                  tmp10.tail = tmp10.tail.next;
                  return tmp10
                }
                tmp10 = runtime.resetDepth(tmp10, curDepth1);
                throw tmp10;
              }
            };
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp7 = treejoin.readTree(tmp6, c11, treejoin.Empty);
            if (tmp7 instanceof runtime.EffectSig.class) {
              this.pc = 50;
              return tmp7
            }
            this.pc = 50;
            continue contLoop;
          } else if (this.pc === 50) {
            tmp7 = runtime.resetDepth(tmp7, curDepth);
            a = tmp7;
            tmp8 = (caseScrut) => {
              let first2, first1, first0, xx, tmp10, curDepth1, stackDelayRes1, Cont$lambda$2;
              Cont$lambda$2 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$2.class = class Cont$lambda$1 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp11;
                  tmp11 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 51) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 52) {
                    tmp10 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 51) {
                      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
                        first0 = caseScrut[0];
                        first1 = caseScrut[1];
                        first2 = caseScrut[2];
                        xx = first0;
                        this.completed = true;
                        return xx
                      } else {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp10 = new globalThis.Error("match error");
                        if (tmp10 instanceof runtime.EffectSig.class) {
                          this.pc = 52;
                          return tmp10
                        }
                        this.pc = 52;
                        continue contLoop1;
                      }
                      this.pc = 53;
                      continue contLoop1;
                    } else if (this.pc === 53) {
                      break contLoop1;
                    } else if (this.pc === 52) {
                      tmp10 = runtime.resetDepth(tmp10, curDepth1);
                      throw tmp10;
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              curDepth1 = runtime.stackDepth;
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$2.class(51, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
                first0 = caseScrut[0];
                first1 = caseScrut[1];
                first2 = caseScrut[2];
                xx = first0;
                return xx
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp10 = new globalThis.Error("match error");
                if (tmp10 instanceof runtime.EffectSig.class) {
                  tmp10.tail.next = new Cont$lambda$2.class(52, null);
                  tmp10.tail = tmp10.tail.next;
                  return tmp10
                }
                tmp10 = runtime.resetDepth(tmp10, curDepth1);
                throw tmp10;
              }
            };
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp9 = treejoin.readTree(tmp8, c2, treejoin.Empty);
            if (tmp9 instanceof runtime.EffectSig.class) {
              this.pc = 54;
              return tmp9
            }
            this.pc = 54;
            continue contLoop;
          } else if (this.pc === 54) {
            tmp9 = runtime.resetDepth(tmp9, curDepth);
            b = tmp9;
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return treejoin.join(a, b, treejoin.Empty)
          }
          break;
        }
      }
      toString() { return "Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$1.class(40, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/1500.1"));
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.tail.next = new Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$1.class(41, null);
      tmp.tail = tmp.tail.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = runtime.safeCall(tmp.toString());
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.tail.next = new Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$1.class(42, null);
      tmp1.tail = tmp1.tail.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = NofibPrelude.nofibStringToList(tmp1);
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.tail.next = new Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$1.class(43, null);
      tmp2.tail = tmp2.tail.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    c11 = tmp2;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp3 = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/1500.2"));
    if (tmp3 instanceof runtime.EffectSig.class) {
      tmp3.tail.next = new Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$1.class(44, null);
      tmp3.tail = tmp3.tail.next;
      return tmp3
    }
    tmp3 = runtime.resetDepth(tmp3, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp4 = runtime.safeCall(tmp3.toString());
    if (tmp4 instanceof runtime.EffectSig.class) {
      tmp4.tail.next = new Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$1.class(45, null);
      tmp4.tail = tmp4.tail.next;
      return tmp4
    }
    tmp4 = runtime.resetDepth(tmp4, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp5 = NofibPrelude.nofibStringToList(tmp4);
    if (tmp5 instanceof runtime.EffectSig.class) {
      tmp5.tail.next = new Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$1.class(46, null);
      tmp5.tail = tmp5.tail.next;
      return tmp5
    }
    tmp5 = runtime.resetDepth(tmp5, curDepth);
    c2 = tmp5;
    tmp6 = (caseScrut) => {
      let first2, first1, first0, xx, tmp10, curDepth1, stackDelayRes1, Cont$lambda$2;
      Cont$lambda$2 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
      Cont$lambda$2.class = class Cont$lambda$3 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp11;
          tmp11 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 47) {
            stackDelayRes1 = value$;
          } else if (this.pc === 48) {
            tmp10 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 47) {
              if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
                first0 = caseScrut[0];
                first1 = caseScrut[1];
                first2 = caseScrut[2];
                xx = first0;
                this.completed = true;
                return xx
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp10 = new globalThis.Error("match error");
                if (tmp10 instanceof runtime.EffectSig.class) {
                  this.pc = 48;
                  return tmp10
                }
                this.pc = 48;
                continue contLoop;
              }
              this.pc = 49;
              continue contLoop;
            } else if (this.pc === 49) {
              break contLoop;
            } else if (this.pc === 48) {
              tmp10 = runtime.resetDepth(tmp10, curDepth1);
              throw tmp10;
            }
            break;
          }
        }
        toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth1 = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$lambda$2.class(47, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        first2 = caseScrut[2];
        xx = first0;
        return xx
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp10 = new globalThis.Error("match error");
        if (tmp10 instanceof runtime.EffectSig.class) {
          tmp10.tail.next = new Cont$lambda$2.class(48, null);
          tmp10.tail = tmp10.tail.next;
          return tmp10
        }
        tmp10 = runtime.resetDepth(tmp10, curDepth1);
        throw tmp10;
      }
    };
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp7 = treejoin.readTree(tmp6, c11, treejoin.Empty);
    if (tmp7 instanceof runtime.EffectSig.class) {
      tmp7.tail.next = new Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$1.class(50, null);
      tmp7.tail = tmp7.tail.next;
      return tmp7
    }
    tmp7 = runtime.resetDepth(tmp7, curDepth);
    a = tmp7;
    tmp8 = (caseScrut) => {
      let first2, first1, first0, xx, tmp10, curDepth1, stackDelayRes1, Cont$lambda$2;
      Cont$lambda$2 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
      Cont$lambda$2.class = class Cont$lambda$1 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp11;
          tmp11 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 51) {
            stackDelayRes1 = value$;
          } else if (this.pc === 52) {
            tmp10 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 51) {
              if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
                first0 = caseScrut[0];
                first1 = caseScrut[1];
                first2 = caseScrut[2];
                xx = first0;
                this.completed = true;
                return xx
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp10 = new globalThis.Error("match error");
                if (tmp10 instanceof runtime.EffectSig.class) {
                  this.pc = 52;
                  return tmp10
                }
                this.pc = 52;
                continue contLoop;
              }
              this.pc = 53;
              continue contLoop;
            } else if (this.pc === 53) {
              break contLoop;
            } else if (this.pc === 52) {
              tmp10 = runtime.resetDepth(tmp10, curDepth1);
              throw tmp10;
            }
            break;
          }
        }
        toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth1 = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$lambda$2.class(51, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        first2 = caseScrut[2];
        xx = first0;
        return xx
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp10 = new globalThis.Error("match error");
        if (tmp10 instanceof runtime.EffectSig.class) {
          tmp10.tail.next = new Cont$lambda$2.class(52, null);
          tmp10.tail = tmp10.tail.next;
          return tmp10
        }
        tmp10 = runtime.resetDepth(tmp10, curDepth1);
        throw tmp10;
      }
    };
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp9 = treejoin.readTree(tmp8, c2, treejoin.Empty);
    if (tmp9 instanceof runtime.EffectSig.class) {
      tmp9.tail.next = new Cont$func$testTreejoin_nofib$treejoin$_mls_L0_1703_2088$1.class(54, null);
      tmp9.tail = tmp9.tail.next;
      return tmp9
    }
    tmp9 = runtime.resetDepth(tmp9, curDepth);
    b = tmp9;
    runtime.stackDepth = runtime.stackDepth + 1;
    return treejoin.join(a, b, treejoin.Empty)
  }
  static toString() { return "treejoin"; }
};
let treejoin = treejoin1; export default treejoin;
