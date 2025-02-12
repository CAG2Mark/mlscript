import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./NofibPrelude.mjs";
import BenchmarkPrelude from "./BenchmarkPrelude.mjs";
let cryptarithm1;
cryptarithm1 = class cryptarithm {
  static {
    let res, handleBlock$;
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
                if (this.pc === 50) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 50) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 51;
                    continue contLoop;
                  } else if (this.pc === 51) {
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
              handleBlock.contHead.next = new Cont$handler$stackHandler$1.class(50, handleBlock.contHead.next);
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
          if (this.pc === 48) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 48) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 49;
              continue contLoop;
            } else if (this.pc === 49) {
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
        let stackDelayRes, Cont$lambda$1;
        Cont$lambda$1 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
        Cont$lambda$1.class = class Cont$lambda$ extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp;
            tmp = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 47) {
              stackDelayRes = value$;
            }
            contLoop: while (true) {
              if (this.pc === 47) {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return cryptarithm.testCryptarithm_nofib(1)
              }
              break;
            }
          }
          toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        stackDelayRes = runtime.checkDepth();
        if (stackDelayRes instanceof runtime.EffectSig.class) {
          stackDelayRes.tail.next = new Cont$lambda$1.class(47, null);
          stackDelayRes.tail = stackDelayRes.tail.next;
          return stackDelayRes
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        return cryptarithm.testCryptarithm_nofib(1)
      });
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$1(48, null);
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
  static expand(a, b, c, d, e, f) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    tmp = e * 10;
    tmp1 = f + tmp;
    tmp2 = d * 100;
    tmp3 = tmp1 + tmp2;
    tmp4 = c * 1000;
    tmp5 = tmp3 + tmp4;
    tmp6 = b * 10000;
    tmp7 = tmp5 + tmp6;
    tmp8 = a * 100000;
    return tmp7 + tmp8
  } 
  static condition(thirywelvn) {
    let param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1;
    Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1 = function Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$(pc1, next1) { return new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$.class(pc1, next1); };
    Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class = class Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp16;
        tmp16 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 0) {
          stackDelayRes = value$;
        } else if (this.pc === 14) {
          tmp15 = value$;
        } else if (this.pc === 13) {
          tmp14 = value$;
        } else if (this.pc === 12) {
          tmp13 = value$;
        } else if (this.pc === 11) {
          tmp12 = value$;
        } else if (this.pc === 10) {
          tmp11 = value$;
        } else if (this.pc === 9) {
          tmp10 = value$;
        } else if (this.pc === 8) {
          tmp9 = value$;
        } else if (this.pc === 7) {
          tmp8 = value$;
        } else if (this.pc === 6) {
          tmp7 = value$;
        } else if (this.pc === 5) {
          tmp6 = value$;
        } else if (this.pc === 4) {
          tmp5 = value$;
        } else if (this.pc === 1) {
          tmp = value$;
        } else if (this.pc === 2) {
          tmp1 = value$;
        } else if (this.pc === 3) {
          tmp4 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 0) {
            if (thirywelvn instanceof NofibPrelude.Cons.class) {
              param0 = thirywelvn.head;
              param1 = thirywelvn.tail;
              t = param0;
              if (param1 instanceof NofibPrelude.Cons.class) {
                param01 = param1.head;
                param11 = param1.tail;
                h = param01;
                if (param11 instanceof NofibPrelude.Cons.class) {
                  param02 = param11.head;
                  param12 = param11.tail;
                  i = param02;
                  if (param12 instanceof NofibPrelude.Cons.class) {
                    param03 = param12.head;
                    param13 = param12.tail;
                    r = param03;
                    if (param13 instanceof NofibPrelude.Cons.class) {
                      param04 = param13.head;
                      param14 = param13.tail;
                      y = param04;
                      if (param14 instanceof NofibPrelude.Cons.class) {
                        param05 = param14.head;
                        param15 = param14.tail;
                        w = param05;
                        if (param15 instanceof NofibPrelude.Cons.class) {
                          param06 = param15.head;
                          param16 = param15.tail;
                          e1 = param06;
                          if (param16 instanceof NofibPrelude.Cons.class) {
                            param07 = param16.head;
                            param17 = param16.tail;
                            l = param07;
                            if (param17 instanceof NofibPrelude.Cons.class) {
                              param08 = param17.head;
                              param18 = param17.tail;
                              v = param08;
                              if (param18 instanceof NofibPrelude.Cons.class) {
                                param09 = param18.head;
                                param19 = param18.tail;
                                n = param09;
                                if (param19 instanceof NofibPrelude.Nil.class) {
                                  runtime.stackDepth = runtime.stackDepth + 1;
                                  tmp = cryptarithm.expand(t, h, i, r, t, y);
                                  if (tmp instanceof runtime.EffectSig.class) {
                                    this.pc = 1;
                                    return tmp
                                  }
                                  this.pc = 1;
                                  continue contLoop;
                                } else {
                                  runtime.stackDepth = runtime.stackDepth + 1;
                                  tmp5 = new globalThis.Error("match error");
                                  if (tmp5 instanceof runtime.EffectSig.class) {
                                    this.pc = 4;
                                    return tmp5
                                  }
                                  this.pc = 4;
                                  continue contLoop;
                                }
                                this.pc = 15;
                                continue contLoop;
                              } else {
                                runtime.stackDepth = runtime.stackDepth + 1;
                                tmp6 = new globalThis.Error("match error");
                                if (tmp6 instanceof runtime.EffectSig.class) {
                                  this.pc = 5;
                                  return tmp6
                                }
                                this.pc = 5;
                                continue contLoop;
                              }
                              this.pc = 15;
                              continue contLoop;
                            } else {
                              runtime.stackDepth = runtime.stackDepth + 1;
                              tmp7 = new globalThis.Error("match error");
                              if (tmp7 instanceof runtime.EffectSig.class) {
                                this.pc = 6;
                                return tmp7
                              }
                              this.pc = 6;
                              continue contLoop;
                            }
                            this.pc = 15;
                            continue contLoop;
                          } else {
                            runtime.stackDepth = runtime.stackDepth + 1;
                            tmp8 = new globalThis.Error("match error");
                            if (tmp8 instanceof runtime.EffectSig.class) {
                              this.pc = 7;
                              return tmp8
                            }
                            this.pc = 7;
                            continue contLoop;
                          }
                          this.pc = 15;
                          continue contLoop;
                        } else {
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp9 = new globalThis.Error("match error");
                          if (tmp9 instanceof runtime.EffectSig.class) {
                            this.pc = 8;
                            return tmp9
                          }
                          this.pc = 8;
                          continue contLoop;
                        }
                        this.pc = 15;
                        continue contLoop;
                      } else {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp10 = new globalThis.Error("match error");
                        if (tmp10 instanceof runtime.EffectSig.class) {
                          this.pc = 9;
                          return tmp10
                        }
                        this.pc = 9;
                        continue contLoop;
                      }
                      this.pc = 15;
                      continue contLoop;
                    } else {
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp11 = new globalThis.Error("match error");
                      if (tmp11 instanceof runtime.EffectSig.class) {
                        this.pc = 10;
                        return tmp11
                      }
                      this.pc = 10;
                      continue contLoop;
                    }
                    this.pc = 15;
                    continue contLoop;
                  } else {
                    runtime.stackDepth = runtime.stackDepth + 1;
                    tmp12 = new globalThis.Error("match error");
                    if (tmp12 instanceof runtime.EffectSig.class) {
                      this.pc = 11;
                      return tmp12
                    }
                    this.pc = 11;
                    continue contLoop;
                  }
                  this.pc = 15;
                  continue contLoop;
                } else {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp13 = new globalThis.Error("match error");
                  if (tmp13 instanceof runtime.EffectSig.class) {
                    this.pc = 12;
                    return tmp13
                  }
                  this.pc = 12;
                  continue contLoop;
                }
                this.pc = 15;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp14 = new globalThis.Error("match error");
                if (tmp14 instanceof runtime.EffectSig.class) {
                  this.pc = 13;
                  return tmp14
                }
                this.pc = 13;
                continue contLoop;
              }
              this.pc = 15;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp15 = new globalThis.Error("match error");
              if (tmp15 instanceof runtime.EffectSig.class) {
                this.pc = 14;
                return tmp15
              }
              this.pc = 14;
              continue contLoop;
            }
            this.pc = 15;
            continue contLoop;
          } else if (this.pc === 15) {
            break contLoop;
          } else if (this.pc === 14) {
            tmp15 = runtime.resetDepth(tmp15, curDepth);
            throw tmp15;
          } else if (this.pc === 13) {
            tmp14 = runtime.resetDepth(tmp14, curDepth);
            throw tmp14;
          } else if (this.pc === 12) {
            tmp13 = runtime.resetDepth(tmp13, curDepth);
            throw tmp13;
          } else if (this.pc === 11) {
            tmp12 = runtime.resetDepth(tmp12, curDepth);
            throw tmp12;
          } else if (this.pc === 10) {
            tmp11 = runtime.resetDepth(tmp11, curDepth);
            throw tmp11;
          } else if (this.pc === 9) {
            tmp10 = runtime.resetDepth(tmp10, curDepth);
            throw tmp10;
          } else if (this.pc === 8) {
            tmp9 = runtime.resetDepth(tmp9, curDepth);
            throw tmp9;
          } else if (this.pc === 7) {
            tmp8 = runtime.resetDepth(tmp8, curDepth);
            throw tmp8;
          } else if (this.pc === 6) {
            tmp7 = runtime.resetDepth(tmp7, curDepth);
            throw tmp7;
          } else if (this.pc === 5) {
            tmp6 = runtime.resetDepth(tmp6, curDepth);
            throw tmp6;
          } else if (this.pc === 4) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            throw tmp5;
          } else if (this.pc === 1) {
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = cryptarithm.expand(t, w, e1, l, v, e1);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 2;
              return tmp1
            }
            this.pc = 2;
            continue contLoop;
          } else if (this.pc === 2) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            tmp2 = 5 * tmp1;
            tmp3 = tmp + tmp2;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = cryptarithm.expand(n, i, n, e1, t, y);
            if (tmp4 instanceof runtime.EffectSig.class) {
              this.pc = 3;
              return tmp4
            }
            this.pc = 3;
            continue contLoop;
          } else if (this.pc === 3) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            this.completed = true;
            return tmp3 == tmp4
          }
          break;
        }
      }
      toString() { return "Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(0, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (thirywelvn instanceof NofibPrelude.Cons.class) {
      param0 = thirywelvn.head;
      param1 = thirywelvn.tail;
      t = param0;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        h = param01;
        if (param11 instanceof NofibPrelude.Cons.class) {
          param02 = param11.head;
          param12 = param11.tail;
          i = param02;
          if (param12 instanceof NofibPrelude.Cons.class) {
            param03 = param12.head;
            param13 = param12.tail;
            r = param03;
            if (param13 instanceof NofibPrelude.Cons.class) {
              param04 = param13.head;
              param14 = param13.tail;
              y = param04;
              if (param14 instanceof NofibPrelude.Cons.class) {
                param05 = param14.head;
                param15 = param14.tail;
                w = param05;
                if (param15 instanceof NofibPrelude.Cons.class) {
                  param06 = param15.head;
                  param16 = param15.tail;
                  e1 = param06;
                  if (param16 instanceof NofibPrelude.Cons.class) {
                    param07 = param16.head;
                    param17 = param16.tail;
                    l = param07;
                    if (param17 instanceof NofibPrelude.Cons.class) {
                      param08 = param17.head;
                      param18 = param17.tail;
                      v = param08;
                      if (param18 instanceof NofibPrelude.Cons.class) {
                        param09 = param18.head;
                        param19 = param18.tail;
                        n = param09;
                        if (param19 instanceof NofibPrelude.Nil.class) {
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp = cryptarithm.expand(t, h, i, r, t, y);
                          if (tmp instanceof runtime.EffectSig.class) {
                            tmp.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(1, null);
                            tmp.tail = tmp.tail.next;
                            return tmp
                          }
                          tmp = runtime.resetDepth(tmp, curDepth);
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp1 = cryptarithm.expand(t, w, e1, l, v, e1);
                          if (tmp1 instanceof runtime.EffectSig.class) {
                            tmp1.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(2, null);
                            tmp1.tail = tmp1.tail.next;
                            return tmp1
                          }
                          tmp1 = runtime.resetDepth(tmp1, curDepth);
                          tmp2 = 5 * tmp1;
                          tmp3 = tmp + tmp2;
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp4 = cryptarithm.expand(n, i, n, e1, t, y);
                          if (tmp4 instanceof runtime.EffectSig.class) {
                            tmp4.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(3, null);
                            tmp4.tail = tmp4.tail.next;
                            return tmp4
                          }
                          tmp4 = runtime.resetDepth(tmp4, curDepth);
                          return tmp3 == tmp4
                        } else {
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp5 = new globalThis.Error("match error");
                          if (tmp5 instanceof runtime.EffectSig.class) {
                            tmp5.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(4, null);
                            tmp5.tail = tmp5.tail.next;
                            return tmp5
                          }
                          tmp5 = runtime.resetDepth(tmp5, curDepth);
                          throw tmp5;
                        }
                      } else {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp6 = new globalThis.Error("match error");
                        if (tmp6 instanceof runtime.EffectSig.class) {
                          tmp6.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(5, null);
                          tmp6.tail = tmp6.tail.next;
                          return tmp6
                        }
                        tmp6 = runtime.resetDepth(tmp6, curDepth);
                        throw tmp6;
                      }
                    } else {
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp7 = new globalThis.Error("match error");
                      if (tmp7 instanceof runtime.EffectSig.class) {
                        tmp7.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(6, null);
                        tmp7.tail = tmp7.tail.next;
                        return tmp7
                      }
                      tmp7 = runtime.resetDepth(tmp7, curDepth);
                      throw tmp7;
                    }
                  } else {
                    runtime.stackDepth = runtime.stackDepth + 1;
                    tmp8 = new globalThis.Error("match error");
                    if (tmp8 instanceof runtime.EffectSig.class) {
                      tmp8.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(7, null);
                      tmp8.tail = tmp8.tail.next;
                      return tmp8
                    }
                    tmp8 = runtime.resetDepth(tmp8, curDepth);
                    throw tmp8;
                  }
                } else {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp9 = new globalThis.Error("match error");
                  if (tmp9 instanceof runtime.EffectSig.class) {
                    tmp9.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(8, null);
                    tmp9.tail = tmp9.tail.next;
                    return tmp9
                  }
                  tmp9 = runtime.resetDepth(tmp9, curDepth);
                  throw tmp9;
                }
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp10 = new globalThis.Error("match error");
                if (tmp10 instanceof runtime.EffectSig.class) {
                  tmp10.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(9, null);
                  tmp10.tail = tmp10.tail.next;
                  return tmp10
                }
                tmp10 = runtime.resetDepth(tmp10, curDepth);
                throw tmp10;
              }
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp11 = new globalThis.Error("match error");
              if (tmp11 instanceof runtime.EffectSig.class) {
                tmp11.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(10, null);
                tmp11.tail = tmp11.tail.next;
                return tmp11
              }
              tmp11 = runtime.resetDepth(tmp11, curDepth);
              throw tmp11;
            }
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp12 = new globalThis.Error("match error");
            if (tmp12 instanceof runtime.EffectSig.class) {
              tmp12.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(11, null);
              tmp12.tail = tmp12.tail.next;
              return tmp12
            }
            tmp12 = runtime.resetDepth(tmp12, curDepth);
            throw tmp12;
          }
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp13 = new globalThis.Error("match error");
          if (tmp13 instanceof runtime.EffectSig.class) {
            tmp13.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(12, null);
            tmp13.tail = tmp13.tail.next;
            return tmp13
          }
          tmp13 = runtime.resetDepth(tmp13, curDepth);
          throw tmp13;
        }
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp14 = new globalThis.Error("match error");
        if (tmp14 instanceof runtime.EffectSig.class) {
          tmp14.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(13, null);
          tmp14.tail = tmp14.tail.next;
          return tmp14
        }
        tmp14 = runtime.resetDepth(tmp14, curDepth);
        throw tmp14;
      }
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp15 = new globalThis.Error("match error");
      if (tmp15 instanceof runtime.EffectSig.class) {
        tmp15.tail.next = new Cont$func$condition$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_224_415$1.class(14, null);
        tmp15.tail = tmp15.tail.next;
        return tmp15
      }
      tmp15 = runtime.resetDepth(tmp15, curDepth);
      throw tmp15;
    }
  } 
  static addj(j, ls) {
    let lscomp, param0, param1, k, ks, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$1;
    Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$1 = function Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$(pc1, next1) { return new Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$.class(pc1, next1); };
    Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$1.class = class Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp6;
        tmp6 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 16) {
          stackDelayRes = value$;
        } else if (this.pc === 27) {
          tmp5 = value$;
        } else if (this.pc === 23) {
          tmp1 = value$;
        } else if (this.pc === 24) {
          tmp2 = value$;
        } else if (this.pc === 25) {
          tmp3 = value$;
        } else if (this.pc === 26) {
          tmp4 = value$;
        } else if (this.pc === 17) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 16) {
            if (ls instanceof NofibPrelude.Nil.class) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = NofibPrelude.Cons(j, NofibPrelude.Nil);
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 17;
                return tmp
              }
              this.pc = 17;
              continue contLoop;
            } else if (ls instanceof NofibPrelude.Cons.class) {
              param0 = ls.head;
              param1 = ls.tail;
              k = param0;
              ks = param1;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = NofibPrelude.Cons(k, ks);
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 23;
                return tmp1
              }
              this.pc = 23;
              continue contLoop;
              this.pc = 28;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp5 = new globalThis.Error("match error");
              if (tmp5 instanceof runtime.EffectSig.class) {
                this.pc = 27;
                return tmp5
              }
              this.pc = 27;
              continue contLoop;
            }
            this.pc = 28;
            continue contLoop;
          } else if (this.pc === 28) {
            break contLoop;
          } else if (this.pc === 27) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            throw tmp5;
          } else if (this.pc === 23) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = NofibPrelude.Cons(j, tmp1);
            if (tmp2 instanceof runtime.EffectSig.class) {
              this.pc = 24;
              return tmp2
            }
            this.pc = 24;
            continue contLoop;
          } else if (this.pc === 24) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = cryptarithm.addj(j, ks);
            if (tmp3 instanceof runtime.EffectSig.class) {
              this.pc = 25;
              return tmp3
            }
            this.pc = 25;
            continue contLoop;
          } else if (this.pc === 25) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = lscomp(tmp3);
            if (tmp4 instanceof runtime.EffectSig.class) {
              this.pc = 26;
              return tmp4
            }
            this.pc = 26;
            continue contLoop;
          } else if (this.pc === 26) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return NofibPrelude.Cons(tmp2, tmp4)
          } else if (this.pc === 17) {
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return NofibPrelude.Cons(tmp, NofibPrelude.Nil)
          }
          break;
        }
      }
      toString() { return "Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    lscomp = function lscomp(p1) {
      let param01, param11, h1, t1, tmp6, tmp7, curDepth1, tmp8, stackDelayRes1, Cont$func$lscomp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_496_580$1;
      Cont$func$lscomp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_496_580$1 = function Cont$func$lscomp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_496_580$(pc1, next1) { return new Cont$func$lscomp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_496_580$.class(pc1, next1); };
      Cont$func$lscomp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_496_580$1.class = class Cont$func$lscomp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_496_580$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp9;
          tmp9 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 18) {
            stackDelayRes1 = value$;
          } else if (this.pc === 21) {
            tmp8 = value$;
          } else if (this.pc === 19) {
            tmp6 = value$;
          } else if (this.pc === 20) {
            tmp7 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 18) {
              if (p1 instanceof NofibPrelude.Nil.class) {
                this.completed = true;
                return NofibPrelude.Nil
              } else if (p1 instanceof NofibPrelude.Cons.class) {
                param01 = p1.head;
                param11 = p1.tail;
                h1 = param01;
                t1 = param11;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp6 = NofibPrelude.Cons(k, h1);
                if (tmp6 instanceof runtime.EffectSig.class) {
                  this.pc = 19;
                  return tmp6
                }
                this.pc = 19;
                continue contLoop;
                this.pc = 22;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp8 = new globalThis.Error("match error");
                if (tmp8 instanceof runtime.EffectSig.class) {
                  this.pc = 21;
                  return tmp8
                }
                this.pc = 21;
                continue contLoop;
              }
              this.pc = 22;
              continue contLoop;
            } else if (this.pc === 22) {
              break contLoop;
            } else if (this.pc === 21) {
              tmp8 = runtime.resetDepth(tmp8, curDepth1);
              throw tmp8;
            } else if (this.pc === 19) {
              tmp6 = runtime.resetDepth(tmp6, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp7 = lscomp(t1);
              if (tmp7 instanceof runtime.EffectSig.class) {
                this.pc = 20;
                return tmp7
              }
              this.pc = 20;
              continue contLoop;
            } else if (this.pc === 20) {
              tmp7 = runtime.resetDepth(tmp7, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return NofibPrelude.Cons(tmp6, tmp7)
            }
            break;
          }
        }
        toString() { return "Cont$func$lscomp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_496_580$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth1 = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$func$lscomp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_496_580$1.class(18, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      if (p1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (p1 instanceof NofibPrelude.Cons.class) {
        param01 = p1.head;
        param11 = p1.tail;
        h1 = param01;
        t1 = param11;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp6 = NofibPrelude.Cons(k, h1);
        if (tmp6 instanceof runtime.EffectSig.class) {
          tmp6.tail.next = new Cont$func$lscomp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_496_580$1.class(19, null);
          tmp6.tail = tmp6.tail.next;
          return tmp6
        }
        tmp6 = runtime.resetDepth(tmp6, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp7 = lscomp(t1);
        if (tmp7 instanceof runtime.EffectSig.class) {
          tmp7.tail.next = new Cont$func$lscomp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_496_580$1.class(20, null);
          tmp7.tail = tmp7.tail.next;
          return tmp7
        }
        tmp7 = runtime.resetDepth(tmp7, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(tmp6, tmp7)
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp8 = new globalThis.Error("match error");
        if (tmp8 instanceof runtime.EffectSig.class) {
          tmp8.tail.next = new Cont$func$lscomp$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_496_580$1.class(21, null);
          tmp8.tail = tmp8.tail.next;
          return tmp8
        }
        tmp8 = runtime.resetDepth(tmp8, curDepth1);
        throw tmp8;
      }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$1.class(16, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (ls instanceof NofibPrelude.Nil.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = NofibPrelude.Cons(j, NofibPrelude.Nil);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.tail.next = new Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$1.class(17, null);
        tmp.tail = tmp.tail.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.Cons(tmp, NofibPrelude.Nil)
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      k = param0;
      ks = param1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = NofibPrelude.Cons(k, ks);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.tail.next = new Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$1.class(23, null);
        tmp1.tail = tmp1.tail.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = NofibPrelude.Cons(j, tmp1);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.tail.next = new Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$1.class(24, null);
        tmp2.tail = tmp2.tail.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = cryptarithm.addj(j, ks);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.tail.next = new Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$1.class(25, null);
        tmp3.tail = tmp3.tail.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = lscomp(tmp3);
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.tail.next = new Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$1.class(26, null);
        tmp4.tail = tmp4.tail.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.Cons(tmp2, tmp4)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp5 = new globalThis.Error("match error");
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.tail.next = new Cont$func$addj$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_421_624$1.class(27, null);
        tmp5.tail = tmp5.tail.next;
        return tmp5
      }
      tmp5 = runtime.resetDepth(tmp5, curDepth);
      throw tmp5;
    }
  } 
  static permutations(ls1) {
    let lscomp1, param0, param1, j1, js, tmp, curDepth, tmp1, stackDelayRes, Cont$func$permutations$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_630_931$1;
    Cont$func$permutations$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_630_931$1 = function Cont$func$permutations$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_630_931$(pc1, next1) { return new Cont$func$permutations$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_630_931$.class(pc1, next1); };
    Cont$func$permutations$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_630_931$1.class = class Cont$func$permutations$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_630_931$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp2;
        tmp2 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 29) {
          stackDelayRes = value$;
        } else if (this.pc === 39) {
          tmp1 = value$;
        } else if (this.pc === 38) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 29) {
            if (ls1 instanceof NofibPrelude.Nil.class) {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil)
            } else if (ls1 instanceof NofibPrelude.Cons.class) {
              param0 = ls1.head;
              param1 = ls1.tail;
              j1 = param0;
              js = param1;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp = cryptarithm.permutations(js);
              if (tmp instanceof runtime.EffectSig.class) {
                this.pc = 38;
                return tmp
              }
              this.pc = 38;
              continue contLoop;
              this.pc = 40;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = new globalThis.Error("match error");
              if (tmp1 instanceof runtime.EffectSig.class) {
                this.pc = 39;
                return tmp1
              }
              this.pc = 39;
              continue contLoop;
            }
            this.pc = 40;
            continue contLoop;
          } else if (this.pc === 40) {
            break contLoop;
          } else if (this.pc === 39) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            throw tmp1;
          } else if (this.pc === 38) {
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return lscomp1(tmp)
          }
          break;
        }
      }
      toString() { return "Cont$func$permutations$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_630_931$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    lscomp1 = function lscomp1(p1) {
      let lscomp2, param01, param11, pjs, t1, tmp2, curDepth1, tmp3, stackDelayRes1, Cont$func$lscomp1$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_703_901$1;
      Cont$func$lscomp1$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_703_901$1 = function Cont$func$lscomp1$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_703_901$(pc1, next1) { return new Cont$func$lscomp1$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_703_901$.class(pc1, next1); };
      Cont$func$lscomp1$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_703_901$1.class = class Cont$func$lscomp1$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_703_901$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp4;
          tmp4 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 30) {
            stackDelayRes1 = value$;
          } else if (this.pc === 36) {
            tmp3 = value$;
          } else if (this.pc === 35) {
            tmp2 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 30) {
              if (p1 instanceof NofibPrelude.Nil.class) {
                this.completed = true;
                return NofibPrelude.Nil
              } else if (p1 instanceof NofibPrelude.Cons.class) {
                param01 = p1.head;
                param11 = p1.tail;
                pjs = param01;
                t1 = param11;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp2 = cryptarithm.addj(j1, pjs);
                if (tmp2 instanceof runtime.EffectSig.class) {
                  this.pc = 35;
                  return tmp2
                }
                this.pc = 35;
                continue contLoop;
                this.pc = 37;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp3 = new globalThis.Error("match error");
                if (tmp3 instanceof runtime.EffectSig.class) {
                  this.pc = 36;
                  return tmp3
                }
                this.pc = 36;
                continue contLoop;
              }
              this.pc = 37;
              continue contLoop;
            } else if (this.pc === 37) {
              break contLoop;
            } else if (this.pc === 36) {
              tmp3 = runtime.resetDepth(tmp3, curDepth1);
              throw tmp3;
            } else if (this.pc === 35) {
              tmp2 = runtime.resetDepth(tmp2, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return lscomp2(tmp2)
            }
            break;
          }
        }
        toString() { return "Cont$func$lscomp1$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_703_901$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      lscomp2 = function lscomp2(p2) {
        let param02, param12, r, t2, tmp4, curDepth2, tmp5, stackDelayRes2, Cont$func$lscomp2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_778_871$1;
        Cont$func$lscomp2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_778_871$1 = function Cont$func$lscomp2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_778_871$(pc1, next1) { return new Cont$func$lscomp2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_778_871$.class(pc1, next1); };
        Cont$func$lscomp2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_778_871$1.class = class Cont$func$lscomp2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_778_871$ extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp6;
            tmp6 = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 31) {
              stackDelayRes2 = value$;
            } else if (this.pc === 33) {
              tmp5 = value$;
            } else if (this.pc === 32) {
              tmp4 = value$;
            }
            contLoop: while (true) {
              if (this.pc === 31) {
                if (p2 instanceof NofibPrelude.Nil.class) {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  this.completed = true;
                  return lscomp1(t1)
                } else if (p2 instanceof NofibPrelude.Cons.class) {
                  param02 = p2.head;
                  param12 = p2.tail;
                  r = param02;
                  t2 = param12;
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp4 = lscomp2(t2);
                  if (tmp4 instanceof runtime.EffectSig.class) {
                    this.pc = 32;
                    return tmp4
                  }
                  this.pc = 32;
                  continue contLoop;
                  this.pc = 34;
                  continue contLoop;
                } else {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp5 = new globalThis.Error("match error");
                  if (tmp5 instanceof runtime.EffectSig.class) {
                    this.pc = 33;
                    return tmp5
                  }
                  this.pc = 33;
                  continue contLoop;
                }
                this.pc = 34;
                continue contLoop;
              } else if (this.pc === 34) {
                break contLoop;
              } else if (this.pc === 33) {
                tmp5 = runtime.resetDepth(tmp5, curDepth2);
                throw tmp5;
              } else if (this.pc === 32) {
                tmp4 = runtime.resetDepth(tmp4, curDepth2);
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return NofibPrelude.Cons(r, tmp4)
              }
              break;
            }
          }
          toString() { return "Cont$func$lscomp2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_778_871$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        curDepth2 = runtime.stackDepth;
        stackDelayRes2 = runtime.checkDepth();
        if (stackDelayRes2 instanceof runtime.EffectSig.class) {
          stackDelayRes2.tail.next = new Cont$func$lscomp2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_778_871$1.class(31, null);
          stackDelayRes2.tail = stackDelayRes2.tail.next;
          return stackDelayRes2
        }
        if (p2 instanceof NofibPrelude.Nil.class) {
          runtime.stackDepth = runtime.stackDepth + 1;
          return lscomp1(t1)
        } else if (p2 instanceof NofibPrelude.Cons.class) {
          param02 = p2.head;
          param12 = p2.tail;
          r = param02;
          t2 = param12;
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp4 = lscomp2(t2);
          if (tmp4 instanceof runtime.EffectSig.class) {
            tmp4.tail.next = new Cont$func$lscomp2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_778_871$1.class(32, null);
            tmp4.tail = tmp4.tail.next;
            return tmp4
          }
          tmp4 = runtime.resetDepth(tmp4, curDepth2);
          runtime.stackDepth = runtime.stackDepth + 1;
          return NofibPrelude.Cons(r, tmp4)
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp5 = new globalThis.Error("match error");
          if (tmp5 instanceof runtime.EffectSig.class) {
            tmp5.tail.next = new Cont$func$lscomp2$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_778_871$1.class(33, null);
            tmp5.tail = tmp5.tail.next;
            return tmp5
          }
          tmp5 = runtime.resetDepth(tmp5, curDepth2);
          throw tmp5;
        }
      };
      curDepth1 = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$func$lscomp1$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_703_901$1.class(30, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      if (p1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (p1 instanceof NofibPrelude.Cons.class) {
        param01 = p1.head;
        param11 = p1.tail;
        pjs = param01;
        t1 = param11;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp2 = cryptarithm.addj(j1, pjs);
        if (tmp2 instanceof runtime.EffectSig.class) {
          tmp2.tail.next = new Cont$func$lscomp1$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_703_901$1.class(35, null);
          tmp2.tail = tmp2.tail.next;
          return tmp2
        }
        tmp2 = runtime.resetDepth(tmp2, curDepth1);
        runtime.stackDepth = runtime.stackDepth + 1;
        return lscomp2(tmp2)
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp3 = new globalThis.Error("match error");
        if (tmp3 instanceof runtime.EffectSig.class) {
          tmp3.tail.next = new Cont$func$lscomp1$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_703_901$1.class(36, null);
          tmp3.tail = tmp3.tail.next;
          return tmp3
        }
        tmp3 = runtime.resetDepth(tmp3, curDepth1);
        throw tmp3;
      }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$permutations$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_630_931$1.class(29, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (ls1 instanceof NofibPrelude.Nil.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil)
    } else if (ls1 instanceof NofibPrelude.Cons.class) {
      param0 = ls1.head;
      param1 = ls1.tail;
      j1 = param0;
      js = param1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = cryptarithm.permutations(js);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.tail.next = new Cont$func$permutations$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_630_931$1.class(38, null);
        tmp.tail = tmp.tail.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lscomp1(tmp)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = new globalThis.Error("match error");
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.tail.next = new Cont$func$permutations$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_630_931$1.class(39, null);
        tmp1.tail = tmp1.tail.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      throw tmp1;
    }
  } 
  static testCryptarithm_nofib(n) {
    let tmp, tmp1, curDepth, stackDelayRes, Cont$func$testCryptarithm_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_937_1075$1;
    Cont$func$testCryptarithm_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_937_1075$1 = function Cont$func$testCryptarithm_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_937_1075$(pc1, next1) { return new Cont$func$testCryptarithm_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_937_1075$.class(pc1, next1); };
    Cont$func$testCryptarithm_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_937_1075$1.class = class Cont$func$testCryptarithm_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_937_1075$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp2;
        tmp2 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 41) {
          stackDelayRes = value$;
        } else if (this.pc === 46) {
          tmp1 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 41) {
            tmp = (i) => {
              let p0, tmp2, tmp3, tmp4, tmp5, curDepth1, stackDelayRes1, Cont$lambda$1;
              Cont$lambda$1 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$1.class = class Cont$lambda$2 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp6;
                  tmp6 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 42) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 43) {
                    tmp3 = value$1;
                  } else if (this.pc === 44) {
                    tmp4 = value$1;
                  } else if (this.pc === 45) {
                    tmp5 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 42) {
                      tmp2 = 9 + i;
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp3 = NofibPrelude.enumFromTo(0, tmp2);
                      if (tmp3 instanceof runtime.EffectSig.class) {
                        this.pc = 43;
                        return tmp3
                      }
                      this.pc = 43;
                      continue contLoop1;
                    } else if (this.pc === 43) {
                      tmp3 = runtime.resetDepth(tmp3, curDepth1);
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp4 = NofibPrelude.take(10, tmp3);
                      if (tmp4 instanceof runtime.EffectSig.class) {
                        this.pc = 44;
                        return tmp4
                      }
                      this.pc = 44;
                      continue contLoop1;
                    } else if (this.pc === 44) {
                      tmp4 = runtime.resetDepth(tmp4, curDepth1);
                      p0 = tmp4;
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp5 = cryptarithm.permutations(p0);
                      if (tmp5 instanceof runtime.EffectSig.class) {
                        this.pc = 45;
                        return tmp5
                      }
                      this.pc = 45;
                      continue contLoop1;
                    } else if (this.pc === 45) {
                      tmp5 = runtime.resetDepth(tmp5, curDepth1);
                      runtime.stackDepth = runtime.stackDepth + 1;
                      this.completed = true;
                      return NofibPrelude.filter(cryptarithm.condition, tmp5)
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              curDepth1 = runtime.stackDepth;
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$1.class(42, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              tmp2 = 9 + i;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp3 = NofibPrelude.enumFromTo(0, tmp2);
              if (tmp3 instanceof runtime.EffectSig.class) {
                tmp3.tail.next = new Cont$lambda$1.class(43, null);
                tmp3.tail = tmp3.tail.next;
                return tmp3
              }
              tmp3 = runtime.resetDepth(tmp3, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp4 = NofibPrelude.take(10, tmp3);
              if (tmp4 instanceof runtime.EffectSig.class) {
                tmp4.tail.next = new Cont$lambda$1.class(44, null);
                tmp4.tail = tmp4.tail.next;
                return tmp4
              }
              tmp4 = runtime.resetDepth(tmp4, curDepth1);
              p0 = tmp4;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp5 = cryptarithm.permutations(p0);
              if (tmp5 instanceof runtime.EffectSig.class) {
                tmp5.tail.next = new Cont$lambda$1.class(45, null);
                tmp5.tail = tmp5.tail.next;
                return tmp5
              }
              tmp5 = runtime.resetDepth(tmp5, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              return NofibPrelude.filter(cryptarithm.condition, tmp5)
            };
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = NofibPrelude.enumFromTo(1, n);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 46;
              return tmp1
            }
            this.pc = 46;
            continue contLoop;
          } else if (this.pc === 46) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return NofibPrelude.map(tmp, tmp1)
          }
          break;
        }
      }
      toString() { return "Cont$func$testCryptarithm_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_937_1075$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$testCryptarithm_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_937_1075$1.class(41, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    tmp = (i) => {
      let p0, tmp2, tmp3, tmp4, tmp5, curDepth1, stackDelayRes1, Cont$lambda$1;
      Cont$lambda$1 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
      Cont$lambda$1.class = class Cont$lambda$2 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp6;
          tmp6 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 42) {
            stackDelayRes1 = value$;
          } else if (this.pc === 43) {
            tmp3 = value$;
          } else if (this.pc === 44) {
            tmp4 = value$;
          } else if (this.pc === 45) {
            tmp5 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 42) {
              tmp2 = 9 + i;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp3 = NofibPrelude.enumFromTo(0, tmp2);
              if (tmp3 instanceof runtime.EffectSig.class) {
                this.pc = 43;
                return tmp3
              }
              this.pc = 43;
              continue contLoop;
            } else if (this.pc === 43) {
              tmp3 = runtime.resetDepth(tmp3, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp4 = NofibPrelude.take(10, tmp3);
              if (tmp4 instanceof runtime.EffectSig.class) {
                this.pc = 44;
                return tmp4
              }
              this.pc = 44;
              continue contLoop;
            } else if (this.pc === 44) {
              tmp4 = runtime.resetDepth(tmp4, curDepth1);
              p0 = tmp4;
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp5 = cryptarithm.permutations(p0);
              if (tmp5 instanceof runtime.EffectSig.class) {
                this.pc = 45;
                return tmp5
              }
              this.pc = 45;
              continue contLoop;
            } else if (this.pc === 45) {
              tmp5 = runtime.resetDepth(tmp5, curDepth1);
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return NofibPrelude.filter(cryptarithm.condition, tmp5)
            }
            break;
          }
        }
        toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth1 = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$lambda$1.class(42, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      tmp2 = 9 + i;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = NofibPrelude.enumFromTo(0, tmp2);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.tail.next = new Cont$lambda$1.class(43, null);
        tmp3.tail = tmp3.tail.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth1);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = NofibPrelude.take(10, tmp3);
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.tail.next = new Cont$lambda$1.class(44, null);
        tmp4.tail = tmp4.tail.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth1);
      p0 = tmp4;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp5 = cryptarithm.permutations(p0);
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.tail.next = new Cont$lambda$1.class(45, null);
        tmp5.tail = tmp5.tail.next;
        return tmp5
      }
      tmp5 = runtime.resetDepth(tmp5, curDepth1);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.filter(cryptarithm.condition, tmp5)
    };
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = NofibPrelude.enumFromTo(1, n);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.tail.next = new Cont$func$testCryptarithm_nofib$$_home$_attempt0$_mlscript$_benchmark$_benchmark$_src$_nofib$_cryptarithm1$_mls_L0_937_1075$1.class(46, null);
      tmp1.tail = tmp1.tail.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.map(tmp, tmp1)
  }
  static toString() { return "cryptarithm"; }
};