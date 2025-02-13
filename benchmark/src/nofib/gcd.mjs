import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let gcd1;
gcd1 = class gcd {
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
                if (this.pc === 39) {
                  res2 = value$;
                }
                contLoop: while (true) {
                  if (this.pc === 39) {
                    if (res2 instanceof runtime.Return.class) {
                      this.completed = true;
                      return res2
                    }
                    this.pc = 40;
                    continue contLoop;
                  } else if (this.pc === 40) {
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
              handleBlock.contHead.next = new Cont$handler$stackHandler$1.class(39, handleBlock.contHead.next);
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
          if (this.pc === 37) {
            res1 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 37) {
              if (res1 instanceof runtime.Return.class) {
                this.completed = true;
                return res1
              }
              this.pc = 38;
              continue contLoop;
            } else if (this.pc === 38) {
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
        let stackDelayRes, Cont$lambda$2;
        Cont$lambda$2 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
        Cont$lambda$2.class = class Cont$lambda$ extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp;
            tmp = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 36) {
              stackDelayRes = value$;
            }
            contLoop: while (true) {
              if (this.pc === 36) {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return gcd.testGcd_nofib(400)
              }
              break;
            }
          }
          toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        stackDelayRes = runtime.checkDepth();
        if (stackDelayRes instanceof runtime.EffectSig.class) {
          stackDelayRes.tail.next = new Cont$lambda$2.class(36, null);
          stackDelayRes.tail = stackDelayRes.tail.next;
          return stackDelayRes
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        return gcd.testGcd_nofib(400)
      });
      if (res1 instanceof runtime.EffectSig.class) {
        res1.tail.next = new Cont$handleBlock$stackHandler$1(37, null);
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
  static g(u1u2u3, v1v2v3) {
    let first2, first1, first0, u1, u2, u3, first21, first11, first01, v1, v2, v3, scrut, first12, first02, q, r, scrut1, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, tmp5, tmp6, stackDelayRes, Cont$func$g$gcd$_mls_L0_152_372$1;
    Cont$func$g$gcd$_mls_L0_152_372$1 = function Cont$func$g$gcd$_mls_L0_152_372$(pc1, next1) { return new Cont$func$g$gcd$_mls_L0_152_372$.class(pc1, next1); };
    Cont$func$g$gcd$_mls_L0_152_372$1.class = class Cont$func$g$gcd$_mls_L0_152_372$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp7;
        tmp7 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 0) {
          stackDelayRes = value$;
        } else if (this.pc === 4) {
          tmp6 = value$;
        } else if (this.pc === 3) {
          tmp5 = value$;
        } else if (this.pc === 1) {
          scrut = value$;
        } else if (this.pc === 2) {
          tmp4 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 0) {
            if (globalThis.Array.isArray(u1u2u3) && u1u2u3.length === 3) {
              first0 = u1u2u3[0];
              first1 = u1u2u3[1];
              first2 = u1u2u3[2];
              u1 = first0;
              u2 = first1;
              u3 = first2;
              if (globalThis.Array.isArray(v1v2v3) && v1v2v3.length === 3) {
                first01 = v1v2v3[0];
                first11 = v1v2v3[1];
                first21 = v1v2v3[2];
                v1 = first01;
                v2 = first11;
                v3 = first21;
                scrut1 = v3 == 0;
                if (scrut1 === true) {
                  this.completed = true;
                  return [
                    u3,
                    u1,
                    u2
                  ]
                } else {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  scrut = NofibPrelude.quotRem(u3, v3);
                  if (scrut instanceof runtime.EffectSig.class) {
                    this.pc = 1;
                    return scrut
                  }
                  this.pc = 1;
                  continue contLoop;
                }
                this.pc = 5;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp5 = new globalThis.Error("match error");
                if (tmp5 instanceof runtime.EffectSig.class) {
                  this.pc = 3;
                  return tmp5
                }
                this.pc = 3;
                continue contLoop;
              }
              this.pc = 5;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp6 = new globalThis.Error("match error");
              if (tmp6 instanceof runtime.EffectSig.class) {
                this.pc = 4;
                return tmp6
              }
              this.pc = 4;
              continue contLoop;
            }
            this.pc = 5;
            continue contLoop;
          } else if (this.pc === 5) {
            break contLoop;
          } else if (this.pc === 4) {
            tmp6 = runtime.resetDepth(tmp6, curDepth);
            throw tmp6;
          } else if (this.pc === 3) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            throw tmp5;
          } else if (this.pc === 1) {
            scrut = runtime.resetDepth(scrut, curDepth);
            if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
              first02 = scrut[0];
              first12 = scrut[1];
              q = first02;
              r = first12;
              tmp = q * v1;
              tmp1 = u1 - tmp;
              tmp2 = q * v2;
              tmp3 = u2 - tmp2;
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return gcd.g([
                v1,
                v2,
                v3
              ], [
                tmp1,
                tmp3,
                r
              ])
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp4 = new globalThis.Error("match error");
              if (tmp4 instanceof runtime.EffectSig.class) {
                this.pc = 2;
                return tmp4
              }
              this.pc = 2;
              continue contLoop;
            }
            this.pc = 5;
            continue contLoop;
          } else if (this.pc === 2) {
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            throw tmp4;
          }
          break;
        }
      }
      toString() { return "Cont$func$g$gcd$_mls_L0_152_372$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$g$gcd$_mls_L0_152_372$1.class(0, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (globalThis.Array.isArray(u1u2u3) && u1u2u3.length === 3) {
      first0 = u1u2u3[0];
      first1 = u1u2u3[1];
      first2 = u1u2u3[2];
      u1 = first0;
      u2 = first1;
      u3 = first2;
      if (globalThis.Array.isArray(v1v2v3) && v1v2v3.length === 3) {
        first01 = v1v2v3[0];
        first11 = v1v2v3[1];
        first21 = v1v2v3[2];
        v1 = first01;
        v2 = first11;
        v3 = first21;
        scrut1 = v3 == 0;
        if (scrut1 === true) {
          return [
            u3,
            u1,
            u2
          ]
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          scrut = NofibPrelude.quotRem(u3, v3);
          if (scrut instanceof runtime.EffectSig.class) {
            scrut.tail.next = new Cont$func$g$gcd$_mls_L0_152_372$1.class(1, null);
            scrut.tail = scrut.tail.next;
            return scrut
          }
          scrut = runtime.resetDepth(scrut, curDepth);
          if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
            first02 = scrut[0];
            first12 = scrut[1];
            q = first02;
            r = first12;
            tmp = q * v1;
            tmp1 = u1 - tmp;
            tmp2 = q * v2;
            tmp3 = u2 - tmp2;
            runtime.stackDepth = runtime.stackDepth + 1;
            return gcd.g([
              v1,
              v2,
              v3
            ], [
              tmp1,
              tmp3,
              r
            ])
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = new globalThis.Error("match error");
            if (tmp4 instanceof runtime.EffectSig.class) {
              tmp4.tail.next = new Cont$func$g$gcd$_mls_L0_152_372$1.class(2, null);
              tmp4.tail = tmp4.tail.next;
              return tmp4
            }
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            throw tmp4;
          }
        }
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp5 = new globalThis.Error("match error");
        if (tmp5 instanceof runtime.EffectSig.class) {
          tmp5.tail.next = new Cont$func$g$gcd$_mls_L0_152_372$1.class(3, null);
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
        tmp6.tail.next = new Cont$func$g$gcd$_mls_L0_152_372$1.class(4, null);
        tmp6.tail = tmp6.tail.next;
        return tmp6
      }
      tmp6 = runtime.resetDepth(tmp6, curDepth);
      throw tmp6;
    }
  } 
  static gcdE(x, y) {
    let scrut, stackDelayRes, Cont$func$gcdE$gcd$_mls_L0_378_449$1;
    Cont$func$gcdE$gcd$_mls_L0_378_449$1 = function Cont$func$gcdE$gcd$_mls_L0_378_449$(pc1, next1) { return new Cont$func$gcdE$gcd$_mls_L0_378_449$.class(pc1, next1); };
    Cont$func$gcdE$gcd$_mls_L0_378_449$1.class = class Cont$func$gcdE$gcd$_mls_L0_378_449$ extends runtime.Cont.class {
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
            scrut = x == 0;
            if (scrut === true) {
              this.completed = true;
              return [
                y,
                0,
                1
              ]
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.completed = true;
              return gcd.g([
                1,
                0,
                x
              ], [
                0,
                1,
                y
              ])
            }
            this.pc = 7;
            continue contLoop;
          } else if (this.pc === 7) {
            break contLoop;
          }
          break;
        }
      }
      toString() { return "Cont$func$gcdE$gcd$_mls_L0_378_449$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$gcdE$gcd$_mls_L0_378_449$1.class(6, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    scrut = x == 0;
    if (scrut === true) {
      return [
        y,
        0,
        1
      ]
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      return gcd.g([
        1,
        0,
        x
      ], [
        0,
        1,
        y
      ])
    }
  } 
  static max_(ls) {
    let param0, param1, x1, param01, param11, y1, xs, scrut, x2, tmp, tmp1, curDepth, tmp2, tmp3, stackDelayRes, Cont$func$max_$gcd$_mls_L0_455_559$1;
    Cont$func$max_$gcd$_mls_L0_455_559$1 = function Cont$func$max_$gcd$_mls_L0_455_559$(pc1, next1) { return new Cont$func$max_$gcd$_mls_L0_455_559$.class(pc1, next1); };
    Cont$func$max_$gcd$_mls_L0_455_559$1.class = class Cont$func$max_$gcd$_mls_L0_455_559$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp4;
        tmp4 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 8) {
          stackDelayRes = value$;
        } else if (this.pc === 12) {
          tmp3 = value$;
        } else if (this.pc === 11) {
          tmp2 = value$;
        } else if (this.pc === 10) {
          tmp1 = value$;
        } else if (this.pc === 9) {
          tmp = value$;
        }
        contLoop: while (true) {
          if (this.pc === 8) {
            if (ls instanceof NofibPrelude.Cons.class) {
              param0 = ls.head;
              param1 = ls.tail;
              x2 = param0;
              x1 = param0;
              if (param1 instanceof NofibPrelude.Nil.class) {
                this.completed = true;
                return x2
              } else if (param1 instanceof NofibPrelude.Cons.class) {
                param01 = param1.head;
                param11 = param1.tail;
                y1 = param01;
                xs = param11;
                scrut = x1 < y1;
                if (scrut === true) {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp = NofibPrelude.Cons(y1, xs);
                  if (tmp instanceof runtime.EffectSig.class) {
                    this.pc = 9;
                    return tmp
                  }
                  this.pc = 9;
                  continue contLoop;
                } else {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp1 = NofibPrelude.Cons(x1, xs);
                  if (tmp1 instanceof runtime.EffectSig.class) {
                    this.pc = 10;
                    return tmp1
                  }
                  this.pc = 10;
                  continue contLoop;
                }
                this.pc = 13;
                continue contLoop;
                this.pc = 13;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp2 = new globalThis.Error("match error");
                if (tmp2 instanceof runtime.EffectSig.class) {
                  this.pc = 11;
                  return tmp2
                }
                this.pc = 11;
                continue contLoop;
              }
              this.pc = 13;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp3 = new globalThis.Error("match error");
              if (tmp3 instanceof runtime.EffectSig.class) {
                this.pc = 12;
                return tmp3
              }
              this.pc = 12;
              continue contLoop;
            }
            this.pc = 13;
            continue contLoop;
          } else if (this.pc === 13) {
            break contLoop;
          } else if (this.pc === 12) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            throw tmp3;
          } else if (this.pc === 11) {
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            throw tmp2;
          } else if (this.pc === 10) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return gcd.max_(tmp1)
          } else if (this.pc === 9) {
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return gcd.max_(tmp)
          }
          break;
        }
      }
      toString() { return "Cont$func$max_$gcd$_mls_L0_455_559$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$max_$gcd$_mls_L0_455_559$1.class(8, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x2 = param0;
      x1 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return x2
      } else if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        y1 = param01;
        xs = param11;
        scrut = x1 < y1;
        if (scrut === true) {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp = NofibPrelude.Cons(y1, xs);
          if (tmp instanceof runtime.EffectSig.class) {
            tmp.tail.next = new Cont$func$max_$gcd$_mls_L0_455_559$1.class(9, null);
            tmp.tail = tmp.tail.next;
            return tmp
          }
          tmp = runtime.resetDepth(tmp, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          return gcd.max_(tmp)
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp1 = NofibPrelude.Cons(x1, xs);
          if (tmp1 instanceof runtime.EffectSig.class) {
            tmp1.tail.next = new Cont$func$max_$gcd$_mls_L0_455_559$1.class(10, null);
            tmp1.tail = tmp1.tail.next;
            return tmp1
          }
          tmp1 = runtime.resetDepth(tmp1, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          return gcd.max_(tmp1)
        }
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp2 = new globalThis.Error("match error");
        if (tmp2 instanceof runtime.EffectSig.class) {
          tmp2.tail.next = new Cont$func$max_$gcd$_mls_L0_455_559$1.class(11, null);
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
        tmp3.tail.next = new Cont$func$max_$gcd$_mls_L0_455_559$1.class(12, null);
        tmp3.tail = tmp3.tail.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      throw tmp3;
    }
  } 
  static test(d) {
    let lscomp1, ns, ms, tripls, rs, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, stackDelayRes, Cont$func$test$gcd$_mls_L0_565_1020$1;
    Cont$func$test$gcd$_mls_L0_565_1020$1 = function Cont$func$test$gcd$_mls_L0_565_1020$(pc1, next1) { return new Cont$func$test$gcd$_mls_L0_565_1020$.class(pc1, next1); };
    Cont$func$test$gcd$_mls_L0_565_1020$1.class = class Cont$func$test$gcd$_mls_L0_565_1020$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp9;
        tmp9 = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 14) {
          stackDelayRes = value$;
        } else if (this.pc === 22) {
          tmp1 = value$;
        } else if (this.pc === 23) {
          tmp3 = value$;
        } else if (this.pc === 28) {
          tmp5 = value$;
        } else if (this.pc === 29) {
          tmp6 = value$;
        } else if (this.pc === 34) {
          tmp8 = value$;
        }
        contLoop: while (true) {
          if (this.pc === 14) {
            tmp = 5000 + d;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = NofibPrelude.enumFromTo(5000, tmp);
            if (tmp1 instanceof runtime.EffectSig.class) {
              this.pc = 22;
              return tmp1
            }
            this.pc = 22;
            continue contLoop;
          } else if (this.pc === 22) {
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            ns = tmp1;
            tmp2 = 10000 + d;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = NofibPrelude.enumFromTo(10000, tmp2);
            if (tmp3 instanceof runtime.EffectSig.class) {
              this.pc = 23;
              return tmp3
            }
            this.pc = 23;
            continue contLoop;
          } else if (this.pc === 23) {
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            ms = tmp3;
            tmp4 = (caseScrut) => {
              let first1, first0, x1, y1, tmp9, curDepth1, tmp10, stackDelayRes1, Cont$lambda$2;
              Cont$lambda$2 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$2.class = class Cont$lambda$3 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp11;
                  tmp11 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 24) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 26) {
                    tmp10 = value$1;
                  } else if (this.pc === 25) {
                    tmp9 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 24) {
                      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                        first0 = caseScrut[0];
                        first1 = caseScrut[1];
                        x1 = first0;
                        y1 = first1;
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp9 = gcd.gcdE(x1, y1);
                        if (tmp9 instanceof runtime.EffectSig.class) {
                          this.pc = 25;
                          return tmp9
                        }
                        this.pc = 25;
                        continue contLoop1;
                      } else {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp10 = new globalThis.Error("match error");
                        if (tmp10 instanceof runtime.EffectSig.class) {
                          this.pc = 26;
                          return tmp10
                        }
                        this.pc = 26;
                        continue contLoop1;
                      }
                      this.pc = 27;
                      continue contLoop1;
                    } else if (this.pc === 27) {
                      break contLoop1;
                    } else if (this.pc === 26) {
                      tmp10 = runtime.resetDepth(tmp10, curDepth1);
                      throw tmp10;
                    } else if (this.pc === 25) {
                      tmp9 = runtime.resetDepth(tmp9, curDepth1);
                      this.completed = true;
                      return [
                        x1,
                        y1,
                        tmp9
                      ]
                    }
                    break;
                  }
                }
                toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
              };
              curDepth1 = runtime.stackDepth;
              stackDelayRes1 = runtime.checkDepth();
              if (stackDelayRes1 instanceof runtime.EffectSig.class) {
                stackDelayRes1.tail.next = new Cont$lambda$2.class(24, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                first0 = caseScrut[0];
                first1 = caseScrut[1];
                x1 = first0;
                y1 = first1;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp9 = gcd.gcdE(x1, y1);
                if (tmp9 instanceof runtime.EffectSig.class) {
                  tmp9.tail.next = new Cont$lambda$2.class(25, null);
                  tmp9.tail = tmp9.tail.next;
                  return tmp9
                }
                tmp9 = runtime.resetDepth(tmp9, curDepth1);
                return [
                  x1,
                  y1,
                  tmp9
                ]
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp10 = new globalThis.Error("match error");
                if (tmp10 instanceof runtime.EffectSig.class) {
                  tmp10.tail.next = new Cont$lambda$2.class(26, null);
                  tmp10.tail = tmp10.tail.next;
                  return tmp10
                }
                tmp10 = runtime.resetDepth(tmp10, curDepth1);
                throw tmp10;
              }
            };
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp5 = lscomp1(ns);
            if (tmp5 instanceof runtime.EffectSig.class) {
              this.pc = 28;
              return tmp5
            }
            this.pc = 28;
            continue contLoop;
          } else if (this.pc === 28) {
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp6 = NofibPrelude.map(tmp4, tmp5);
            if (tmp6 instanceof runtime.EffectSig.class) {
              this.pc = 29;
              return tmp6
            }
            this.pc = 29;
            continue contLoop;
          } else if (this.pc === 29) {
            tmp6 = runtime.resetDepth(tmp6, curDepth);
            tripls = tmp6;
            tmp7 = (caseScrut) => {
              let first2, first1, first0, d1, d2, first21, first11, first01, gg, u, v, tmp9, tmp10, tmp11, curDepth1, tmp12, stackDelayRes1, Cont$lambda$2;
              Cont$lambda$2 = function Cont$lambda$(pc2, next2) { return new Cont$lambda$.class(pc2, next2); };
              Cont$lambda$2.class = class Cont$lambda$1 extends runtime.Cont.class {
                constructor(pc1, next1) {
                  let tmp13;
                  tmp13 = super(next1, false);
                  this.pc = pc1;
                  this.next = next1;
                }
                resume(value$1) {
                  if (this.pc === 30) {
                    stackDelayRes1 = value$1;
                  } else if (this.pc === 32) {
                    tmp12 = value$1;
                  } else if (this.pc === 31) {
                    tmp11 = value$1;
                  }
                  contLoop1: while (true) {
                    if (this.pc === 30) {
                      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
                        first0 = caseScrut[0];
                        first1 = caseScrut[1];
                        first2 = caseScrut[2];
                        d1 = first0;
                        d2 = first1;
                        if (globalThis.Array.isArray(first2) && first2.length === 3) {
                          first01 = first2[0];
                          first11 = first2[1];
                          first21 = first2[2];
                          gg = first01;
                          u = first11;
                          v = first21;
                          tmp9 = gg + u;
                          tmp10 = tmp9 + v;
                          runtime.stackDepth = runtime.stackDepth + 1;
                          this.completed = true;
                          return NofibPrelude.abs(tmp10)
                        } else {
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp11 = new globalThis.Error("match error");
                          if (tmp11 instanceof runtime.EffectSig.class) {
                            this.pc = 31;
                            return tmp11
                          }
                          this.pc = 31;
                          continue contLoop1;
                        }
                        this.pc = 33;
                        continue contLoop1;
                      } else {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp12 = new globalThis.Error("match error");
                        if (tmp12 instanceof runtime.EffectSig.class) {
                          this.pc = 32;
                          return tmp12
                        }
                        this.pc = 32;
                        continue contLoop1;
                      }
                      this.pc = 33;
                      continue contLoop1;
                    } else if (this.pc === 33) {
                      break contLoop1;
                    } else if (this.pc === 32) {
                      tmp12 = runtime.resetDepth(tmp12, curDepth1);
                      throw tmp12;
                    } else if (this.pc === 31) {
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
                stackDelayRes1.tail.next = new Cont$lambda$2.class(30, null);
                stackDelayRes1.tail = stackDelayRes1.tail.next;
                return stackDelayRes1
              }
              if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
                first0 = caseScrut[0];
                first1 = caseScrut[1];
                first2 = caseScrut[2];
                d1 = first0;
                d2 = first1;
                if (globalThis.Array.isArray(first2) && first2.length === 3) {
                  first01 = first2[0];
                  first11 = first2[1];
                  first21 = first2[2];
                  gg = first01;
                  u = first11;
                  v = first21;
                  tmp9 = gg + u;
                  tmp10 = tmp9 + v;
                  runtime.stackDepth = runtime.stackDepth + 1;
                  return NofibPrelude.abs(tmp10)
                } else {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp11 = new globalThis.Error("match error");
                  if (tmp11 instanceof runtime.EffectSig.class) {
                    tmp11.tail.next = new Cont$lambda$2.class(31, null);
                    tmp11.tail = tmp11.tail.next;
                    return tmp11
                  }
                  tmp11 = runtime.resetDepth(tmp11, curDepth1);
                  throw tmp11;
                }
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp12 = new globalThis.Error("match error");
                if (tmp12 instanceof runtime.EffectSig.class) {
                  tmp12.tail.next = new Cont$lambda$2.class(32, null);
                  tmp12.tail = tmp12.tail.next;
                  return tmp12
                }
                tmp12 = runtime.resetDepth(tmp12, curDepth1);
                throw tmp12;
              }
            };
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp8 = NofibPrelude.map(tmp7, tripls);
            if (tmp8 instanceof runtime.EffectSig.class) {
              this.pc = 34;
              return tmp8
            }
            this.pc = 34;
            continue contLoop;
          } else if (this.pc === 34) {
            tmp8 = runtime.resetDepth(tmp8, curDepth);
            rs = tmp8;
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return gcd.max_(rs)
          }
          break;
        }
      }
      toString() { return "Cont$func$test$gcd$_mls_L0_565_1020$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    lscomp1 = function lscomp1(p1) {
      let lscomp2, param0, param1, h1, t1, tmp9, curDepth1, stackDelayRes1, Cont$func$lscomp1$gcd$_mls_L0_665_848$1;
      Cont$func$lscomp1$gcd$_mls_L0_665_848$1 = function Cont$func$lscomp1$gcd$_mls_L0_665_848$(pc1, next1) { return new Cont$func$lscomp1$gcd$_mls_L0_665_848$.class(pc1, next1); };
      Cont$func$lscomp1$gcd$_mls_L0_665_848$1.class = class Cont$func$lscomp1$gcd$_mls_L0_665_848$ extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp10;
          tmp10 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 15) {
            stackDelayRes1 = value$;
          } else if (this.pc === 20) {
            tmp9 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 15) {
              if (p1 instanceof NofibPrelude.Nil.class) {
                this.completed = true;
                return NofibPrelude.Nil
              } else if (p1 instanceof NofibPrelude.Cons.class) {
                param0 = p1.head;
                param1 = p1.tail;
                h1 = param0;
                t1 = param1;
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return lscomp2(ms);
                this.pc = 21;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp9 = new globalThis.Error("match error");
                if (tmp9 instanceof runtime.EffectSig.class) {
                  this.pc = 20;
                  return tmp9
                }
                this.pc = 20;
                continue contLoop;
              }
              this.pc = 21;
              continue contLoop;
            } else if (this.pc === 21) {
              break contLoop;
            } else if (this.pc === 20) {
              tmp9 = runtime.resetDepth(tmp9, curDepth1);
              throw tmp9;
            }
            break;
          }
        }
        toString() { return "Cont$func$lscomp1$gcd$_mls_L0_665_848$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      lscomp2 = function lscomp2(p2) {
        let param01, param11, h2, t2, tmp10, curDepth2, tmp11, stackDelayRes2, Cont$func$lscomp2$gcd$_mls_L0_733_830$1;
        Cont$func$lscomp2$gcd$_mls_L0_733_830$1 = function Cont$func$lscomp2$gcd$_mls_L0_733_830$(pc1, next1) { return new Cont$func$lscomp2$gcd$_mls_L0_733_830$.class(pc1, next1); };
        Cont$func$lscomp2$gcd$_mls_L0_733_830$1.class = class Cont$func$lscomp2$gcd$_mls_L0_733_830$ extends runtime.Cont.class {
          constructor(pc, next) {
            let tmp12;
            tmp12 = super(next, false);
            this.pc = pc;
            this.next = next;
          }
          resume(value$) {
            if (this.pc === 16) {
              stackDelayRes2 = value$;
            } else if (this.pc === 18) {
              tmp11 = value$;
            } else if (this.pc === 17) {
              tmp10 = value$;
            }
            contLoop: while (true) {
              if (this.pc === 16) {
                if (p2 instanceof NofibPrelude.Nil.class) {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  this.completed = true;
                  return lscomp1(t1)
                } else if (p2 instanceof NofibPrelude.Cons.class) {
                  param01 = p2.head;
                  param11 = p2.tail;
                  h2 = param01;
                  t2 = param11;
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp10 = lscomp2(t2);
                  if (tmp10 instanceof runtime.EffectSig.class) {
                    this.pc = 17;
                    return tmp10
                  }
                  this.pc = 17;
                  continue contLoop;
                  this.pc = 19;
                  continue contLoop;
                } else {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp11 = new globalThis.Error("match error");
                  if (tmp11 instanceof runtime.EffectSig.class) {
                    this.pc = 18;
                    return tmp11
                  }
                  this.pc = 18;
                  continue contLoop;
                }
                this.pc = 19;
                continue contLoop;
              } else if (this.pc === 19) {
                break contLoop;
              } else if (this.pc === 18) {
                tmp11 = runtime.resetDepth(tmp11, curDepth2);
                throw tmp11;
              } else if (this.pc === 17) {
                tmp10 = runtime.resetDepth(tmp10, curDepth2);
                runtime.stackDepth = runtime.stackDepth + 1;
                this.completed = true;
                return NofibPrelude.Cons([
                  h1,
                  h2
                ], tmp10)
              }
              break;
            }
          }
          toString() { return "Cont$func$lscomp2$gcd$_mls_L0_733_830$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
        };
        curDepth2 = runtime.stackDepth;
        stackDelayRes2 = runtime.checkDepth();
        if (stackDelayRes2 instanceof runtime.EffectSig.class) {
          stackDelayRes2.tail.next = new Cont$func$lscomp2$gcd$_mls_L0_733_830$1.class(16, null);
          stackDelayRes2.tail = stackDelayRes2.tail.next;
          return stackDelayRes2
        }
        if (p2 instanceof NofibPrelude.Nil.class) {
          runtime.stackDepth = runtime.stackDepth + 1;
          return lscomp1(t1)
        } else if (p2 instanceof NofibPrelude.Cons.class) {
          param01 = p2.head;
          param11 = p2.tail;
          h2 = param01;
          t2 = param11;
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp10 = lscomp2(t2);
          if (tmp10 instanceof runtime.EffectSig.class) {
            tmp10.tail.next = new Cont$func$lscomp2$gcd$_mls_L0_733_830$1.class(17, null);
            tmp10.tail = tmp10.tail.next;
            return tmp10
          }
          tmp10 = runtime.resetDepth(tmp10, curDepth2);
          runtime.stackDepth = runtime.stackDepth + 1;
          return NofibPrelude.Cons([
            h1,
            h2
          ], tmp10)
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp11 = new globalThis.Error("match error");
          if (tmp11 instanceof runtime.EffectSig.class) {
            tmp11.tail.next = new Cont$func$lscomp2$gcd$_mls_L0_733_830$1.class(18, null);
            tmp11.tail = tmp11.tail.next;
            return tmp11
          }
          tmp11 = runtime.resetDepth(tmp11, curDepth2);
          throw tmp11;
        }
      };
      curDepth1 = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$func$lscomp1$gcd$_mls_L0_665_848$1.class(15, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      if (p1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (p1 instanceof NofibPrelude.Cons.class) {
        param0 = p1.head;
        param1 = p1.tail;
        h1 = param0;
        t1 = param1;
        runtime.stackDepth = runtime.stackDepth + 1;
        return lscomp2(ms)
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp9 = new globalThis.Error("match error");
        if (tmp9 instanceof runtime.EffectSig.class) {
          tmp9.tail.next = new Cont$func$lscomp1$gcd$_mls_L0_665_848$1.class(20, null);
          tmp9.tail = tmp9.tail.next;
          return tmp9
        }
        tmp9 = runtime.resetDepth(tmp9, curDepth1);
        throw tmp9;
      }
    };
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$test$gcd$_mls_L0_565_1020$1.class(14, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    tmp = 5000 + d;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = NofibPrelude.enumFromTo(5000, tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.tail.next = new Cont$func$test$gcd$_mls_L0_565_1020$1.class(22, null);
      tmp1.tail = tmp1.tail.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    ns = tmp1;
    tmp2 = 10000 + d;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp3 = NofibPrelude.enumFromTo(10000, tmp2);
    if (tmp3 instanceof runtime.EffectSig.class) {
      tmp3.tail.next = new Cont$func$test$gcd$_mls_L0_565_1020$1.class(23, null);
      tmp3.tail = tmp3.tail.next;
      return tmp3
    }
    tmp3 = runtime.resetDepth(tmp3, curDepth);
    ms = tmp3;
    tmp4 = (caseScrut) => {
      let first1, first0, x1, y1, tmp9, curDepth1, tmp10, stackDelayRes1, Cont$lambda$2;
      Cont$lambda$2 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
      Cont$lambda$2.class = class Cont$lambda$3 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp11;
          tmp11 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 24) {
            stackDelayRes1 = value$;
          } else if (this.pc === 26) {
            tmp10 = value$;
          } else if (this.pc === 25) {
            tmp9 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 24) {
              if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                first0 = caseScrut[0];
                first1 = caseScrut[1];
                x1 = first0;
                y1 = first1;
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp9 = gcd.gcdE(x1, y1);
                if (tmp9 instanceof runtime.EffectSig.class) {
                  this.pc = 25;
                  return tmp9
                }
                this.pc = 25;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp10 = new globalThis.Error("match error");
                if (tmp10 instanceof runtime.EffectSig.class) {
                  this.pc = 26;
                  return tmp10
                }
                this.pc = 26;
                continue contLoop;
              }
              this.pc = 27;
              continue contLoop;
            } else if (this.pc === 27) {
              break contLoop;
            } else if (this.pc === 26) {
              tmp10 = runtime.resetDepth(tmp10, curDepth1);
              throw tmp10;
            } else if (this.pc === 25) {
              tmp9 = runtime.resetDepth(tmp9, curDepth1);
              this.completed = true;
              return [
                x1,
                y1,
                tmp9
              ]
            }
            break;
          }
        }
        toString() { return "Cont$lambda$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
      };
      curDepth1 = runtime.stackDepth;
      stackDelayRes1 = runtime.checkDepth();
      if (stackDelayRes1 instanceof runtime.EffectSig.class) {
        stackDelayRes1.tail.next = new Cont$lambda$2.class(24, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        x1 = first0;
        y1 = first1;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp9 = gcd.gcdE(x1, y1);
        if (tmp9 instanceof runtime.EffectSig.class) {
          tmp9.tail.next = new Cont$lambda$2.class(25, null);
          tmp9.tail = tmp9.tail.next;
          return tmp9
        }
        tmp9 = runtime.resetDepth(tmp9, curDepth1);
        return [
          x1,
          y1,
          tmp9
        ]
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp10 = new globalThis.Error("match error");
        if (tmp10 instanceof runtime.EffectSig.class) {
          tmp10.tail.next = new Cont$lambda$2.class(26, null);
          tmp10.tail = tmp10.tail.next;
          return tmp10
        }
        tmp10 = runtime.resetDepth(tmp10, curDepth1);
        throw tmp10;
      }
    };
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp5 = lscomp1(ns);
    if (tmp5 instanceof runtime.EffectSig.class) {
      tmp5.tail.next = new Cont$func$test$gcd$_mls_L0_565_1020$1.class(28, null);
      tmp5.tail = tmp5.tail.next;
      return tmp5
    }
    tmp5 = runtime.resetDepth(tmp5, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp6 = NofibPrelude.map(tmp4, tmp5);
    if (tmp6 instanceof runtime.EffectSig.class) {
      tmp6.tail.next = new Cont$func$test$gcd$_mls_L0_565_1020$1.class(29, null);
      tmp6.tail = tmp6.tail.next;
      return tmp6
    }
    tmp6 = runtime.resetDepth(tmp6, curDepth);
    tripls = tmp6;
    tmp7 = (caseScrut) => {
      let first2, first1, first0, d1, d2, first21, first11, first01, gg, u, v, tmp9, tmp10, tmp11, curDepth1, tmp12, stackDelayRes1, Cont$lambda$2;
      Cont$lambda$2 = function Cont$lambda$(pc1, next1) { return new Cont$lambda$.class(pc1, next1); };
      Cont$lambda$2.class = class Cont$lambda$1 extends runtime.Cont.class {
        constructor(pc, next) {
          let tmp13;
          tmp13 = super(next, false);
          this.pc = pc;
          this.next = next;
        }
        resume(value$) {
          if (this.pc === 30) {
            stackDelayRes1 = value$;
          } else if (this.pc === 32) {
            tmp12 = value$;
          } else if (this.pc === 31) {
            tmp11 = value$;
          }
          contLoop: while (true) {
            if (this.pc === 30) {
              if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
                first0 = caseScrut[0];
                first1 = caseScrut[1];
                first2 = caseScrut[2];
                d1 = first0;
                d2 = first1;
                if (globalThis.Array.isArray(first2) && first2.length === 3) {
                  first01 = first2[0];
                  first11 = first2[1];
                  first21 = first2[2];
                  gg = first01;
                  u = first11;
                  v = first21;
                  tmp9 = gg + u;
                  tmp10 = tmp9 + v;
                  runtime.stackDepth = runtime.stackDepth + 1;
                  this.completed = true;
                  return NofibPrelude.abs(tmp10)
                } else {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp11 = new globalThis.Error("match error");
                  if (tmp11 instanceof runtime.EffectSig.class) {
                    this.pc = 31;
                    return tmp11
                  }
                  this.pc = 31;
                  continue contLoop;
                }
                this.pc = 33;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp12 = new globalThis.Error("match error");
                if (tmp12 instanceof runtime.EffectSig.class) {
                  this.pc = 32;
                  return tmp12
                }
                this.pc = 32;
                continue contLoop;
              }
              this.pc = 33;
              continue contLoop;
            } else if (this.pc === 33) {
              break contLoop;
            } else if (this.pc === 32) {
              tmp12 = runtime.resetDepth(tmp12, curDepth1);
              throw tmp12;
            } else if (this.pc === 31) {
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
        stackDelayRes1.tail.next = new Cont$lambda$2.class(30, null);
        stackDelayRes1.tail = stackDelayRes1.tail.next;
        return stackDelayRes1
      }
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        first2 = caseScrut[2];
        d1 = first0;
        d2 = first1;
        if (globalThis.Array.isArray(first2) && first2.length === 3) {
          first01 = first2[0];
          first11 = first2[1];
          first21 = first2[2];
          gg = first01;
          u = first11;
          v = first21;
          tmp9 = gg + u;
          tmp10 = tmp9 + v;
          runtime.stackDepth = runtime.stackDepth + 1;
          return NofibPrelude.abs(tmp10)
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp11 = new globalThis.Error("match error");
          if (tmp11 instanceof runtime.EffectSig.class) {
            tmp11.tail.next = new Cont$lambda$2.class(31, null);
            tmp11.tail = tmp11.tail.next;
            return tmp11
          }
          tmp11 = runtime.resetDepth(tmp11, curDepth1);
          throw tmp11;
        }
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp12 = new globalThis.Error("match error");
        if (tmp12 instanceof runtime.EffectSig.class) {
          tmp12.tail.next = new Cont$lambda$2.class(32, null);
          tmp12.tail = tmp12.tail.next;
          return tmp12
        }
        tmp12 = runtime.resetDepth(tmp12, curDepth1);
        throw tmp12;
      }
    };
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp8 = NofibPrelude.map(tmp7, tripls);
    if (tmp8 instanceof runtime.EffectSig.class) {
      tmp8.tail.next = new Cont$func$test$gcd$_mls_L0_565_1020$1.class(34, null);
      tmp8.tail = tmp8.tail.next;
      return tmp8
    }
    tmp8 = runtime.resetDepth(tmp8, curDepth);
    rs = tmp8;
    runtime.stackDepth = runtime.stackDepth + 1;
    return gcd.max_(rs)
  } 
  static testGcd_nofib(x1) {
    let stackDelayRes, Cont$func$testGcd_nofib$gcd$_mls_L0_1027_1053$1;
    Cont$func$testGcd_nofib$gcd$_mls_L0_1027_1053$1 = function Cont$func$testGcd_nofib$gcd$_mls_L0_1027_1053$(pc1, next1) { return new Cont$func$testGcd_nofib$gcd$_mls_L0_1027_1053$.class(pc1, next1); };
    Cont$func$testGcd_nofib$gcd$_mls_L0_1027_1053$1.class = class Cont$func$testGcd_nofib$gcd$_mls_L0_1027_1053$ extends runtime.Cont.class {
      constructor(pc, next) {
        let tmp;
        tmp = super(next, false);
        this.pc = pc;
        this.next = next;
      }
      resume(value$) {
        if (this.pc === 35) {
          stackDelayRes = value$;
        }
        contLoop: while (true) {
          if (this.pc === 35) {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.completed = true;
            return gcd.test(x1)
          }
          break;
        }
      }
      toString() { return "Cont$func$testGcd_nofib$gcd$_mls_L0_1027_1053$(" + globalThis.Predef.render(this.pc) + ", " + globalThis.Predef.render(this.next) + ")"; }
    };
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.tail.next = new Cont$func$testGcd_nofib$gcd$_mls_L0_1027_1053$1.class(35, null);
      stackDelayRes.tail = stackDelayRes.tail.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return gcd.test(x1)
  }
  static toString() { return "gcd"; }
};
let gcd = gcd1; export default gcd;
