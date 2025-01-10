const Predef$class = class Predef {
  constructor() {
    this.assert = console.assert;
    this.MatchResult = function MatchResult(captures1) { return new MatchResult.class(captures1); };
    this.MatchResult.class = class MatchResult {
      constructor(captures) {
        this.captures = captures;
      }
      toString() { return "MatchResult(" + this.captures + ")"; }
    };
    this.MatchFailure = function MatchFailure(errors1) { return new MatchFailure.class(errors1); };
    this.MatchFailure.class = class MatchFailure {
      constructor(errors) {
        this.errors = errors;
      }
      toString() { return "MatchFailure(" + this.errors + ")"; }
    };
    const TraceLogger$class = class TraceLogger {
      constructor() {
        this.enabled = false;
        this.indentLvl = 0;
      }
      indent() {
        let scrut, prev, tmp;
        scrut = this.enabled;
        if (scrut) {
          prev = this.indentLvl;
          tmp = prev + 1;
          this.indentLvl = tmp;
          return prev;
        } else {
          return null;
        }
      } 
      resetIndent(n) {
        let scrut;
        scrut = this.enabled;
        if (scrut) {
          this.indentLvl = n;
          return null;
        } else {
          return null;
        }
      } 
      log(msg) {
        let scrut, tmp, tmp1, tmp2, tmp3, tmp4;
        scrut = this.enabled;
        if (scrut) {
          tmp = "| ".repeat(this.indentLvl) ?? null;
          tmp1 = "  ".repeat(this.indentLvl) ?? null;
          tmp2 = "\n" + tmp1;
          tmp3 = msg.replaceAll("\n", tmp2);
          tmp4 = tmp + tmp3;
          return console.log(tmp4) ?? null;
        } else {
          return null;
        }
      }
      toString() { return "TraceLogger"; }
    };
    this.TraceLogger = new TraceLogger$class;
    this.TraceLogger.class = TraceLogger$class;
    const this$Predef = this;
    this.Test = class Test {
      constructor() {
        let tmp;
        tmp = this$Predef.print("Test");
        this.y = 1;
      }
      toString() { return "Test"; }
    };
    this.__Cont = function __Cont(next1) { return new __Cont.class(next1); };
    this.__Cont.class = class __Cont {
      constructor(next) {
        this.next = next;
      }
      toString() { return "__Cont(" + this.next + ")"; }
    };
    this.__TailList = function __TailList(next1, tail1) { return new __TailList.class(next1, tail1); };
    this.__TailList.class = class __TailList {
      constructor(next, tail) {
        this.next = next;
        this.tail = tail;
      }
      toString() { return "__TailList(" + this.next + ", " + this.tail + ")"; }
    };
    this.__HandleBlock = function __HandleBlock(next1, nextHandler1, tail1, handler1) { return new __HandleBlock.class(next1, nextHandler1, tail1, handler1); };
    this.__HandleBlock.class = class __HandleBlock {
      constructor(next, nextHandler, tail, handler) {
        this.next = next;
        this.nextHandler = nextHandler;
        this.tail = tail;
        this.handler = handler;
      }
      toString() { return "__HandleBlock(" + this.next + ", " + this.nextHandler + ", " + this.tail + ", " + this.handler + ")"; }
    };
    this.__EffectSig = function __EffectSig(next1, nextHandler1, tail1, tailHandler1, resumed1, handler1, handlerFun1) { return new __EffectSig.class(next1, nextHandler1, tail1, tailHandler1, resumed1, handler1, handlerFun1); };
    this.__EffectSig.class = class __EffectSig {
      constructor(next, nextHandler, tail, tailHandler, resumed, handler, handlerFun) {
        this.next = next;
        this.nextHandler = nextHandler;
        this.tail = tail;
        this.tailHandler = tailHandler;
        this.resumed = resumed;
        this.handler = handler;
        this.handlerFun = handlerFun;
      }
      toString() { return "__EffectSig(" + this.next + ", " + this.nextHandler + ", " + this.tail + ", " + this.tailHandler + ", " + this.resumed + ", " + this.handler + ", " + this.handlerFun + ")"; }
    };
    this.__Return = function __Return(value1) { return new __Return.class(value1); };
    this.__Return.class = class __Return {
      constructor(value) {
        this.value = value;
      }
      toString() { return "__Return(" + this.value + ")"; }
    };
  }
  id(x) {
    return x;
  } 
  not(x1) {
    if (x1 === false) {
      return true;
    } else {
      return false;
    }
  } 
  pipeInto(x2, f) {
    return f(x2) ?? null;
  } 
  pipeFrom(f1, x3) {
    return f1(x3) ?? null;
  } 
  andThen(f2, g) {
    return (x4) => {
      let tmp;
      tmp = f2(x4) ?? null;
      return g(tmp) ?? null;
    };
  } 
  compose(f3, g1) {
    return (x4) => {
      let tmp;
      tmp = g1(x4) ?? null;
      return f3(tmp) ?? null;
    };
  } 
  passTo(receiver, f4) {
    return (...args) => {
      return f4(receiver, ...args) ?? null;
    };
  } 
  call(receiver1, f5) {
    return (...args) => {
      return f5.call(receiver1, ...args);
    };
  } 
  pass1(f6) {
    return (...xs) => {
      return f6(xs[0]) ?? null;
    };
  } 
  pass2(f7) {
    return (...xs) => {
      return f7(xs[0], xs[1]) ?? null;
    };
  } 
  pass3(f8) {
    return (...xs) => {
      return f8(xs[0], xs[1], xs[2]) ?? null;
    };
  } 
  print(...xs) {
    let tmp;
    tmp = xs.map(String) ?? null;
    return console.log(...tmp) ?? null;
  } 
  notImplemented(msg) {
    let tmp;
    tmp = "Not implemented: " + msg;
    throw Error(tmp);
  } 
  get notImplementedError() {
    throw Error("Not implemented");
  } 
  tupleSlice(xs1, i, j) {
    let tmp;
    tmp = xs1.length - j;
    return globalThis.Array.prototype.slice.call(xs1, i, tmp) ?? null;
  } 
  tupleGet(xs2, i1) {
    return globalThis.Array.prototype.at.call(xs2, i1);
  } 
  stringStartsWith(string, prefix) {
    return string.startsWith(prefix) ?? null;
  } 
  stringGet(string1, i2) {
    return string1.at(i2) ?? null;
  } 
  stringDrop(string2, n) {
    return string2.slice(n) ?? null;
  } 
  checkArgs(functionName, expected, isUB, got) {
    let scrut, name, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    tmp = got < expected;
    tmp1 = got > expected;
    tmp2 = isUB && tmp1;
    scrut = tmp || tmp2;
    if (scrut) {
      scrut1 = functionName.length > 0;
      if (scrut1) {
        tmp3 = " '" + functionName;
        tmp4 = tmp3 + "'";
      } else {
        tmp4 = "";
      }
      name = tmp4;
      tmp5 = "Function" + name;
      tmp6 = tmp5 + " expected ";
      tmp7 = tmp6 + expected;
      tmp8 = tmp7 + " arguments but got ";
      tmp9 = tmp8 + got;
      throw globalThis.Error(tmp9) ?? null;
    } else {
      return null;
    }
  } 
  __mkEffect(handler, handlerFun) {
    let res, tmp;
    tmp = new this.__EffectSig.class(null, null, null, null, false, handler, handlerFun);
    res = tmp;
    res.tail = res;
    res.tailHandler = res;
    return res;
  } 
  __handleBlockImpl(cur, handler1) {
    let handlerCont, nxt, scrut, tmp, tmp1, tmp2, tmp3;
    tmp = new this.__HandleBlock.class(null, null, null, handler1);
    handlerCont = tmp;
    handlerCont.tail = handlerCont;
    cur.tailHandler.nextHandler = handlerCont;
    cur.tailHandler = handlerCont;
    tmp4: while (true) {
      if (cur instanceof this.__EffectSig.class) {
        tmp1 = this.__handleEffect(cur);
        nxt = tmp1;
        scrut = cur === nxt;
        if (scrut) {
          cur.tail = handlerCont.tail;
          return cur;
        } else {
          cur = nxt;
          tmp2 = null;
        }
        tmp3 = tmp2;
        continue tmp4;
      } else {
        return cur;
      }
      break;
    }
    return tmp3;
  } 
  __handleEffect(cur1) {
    let prevCont, handlerCont, scrut, scrut1, origTail, savedNext, scrut2, scrut3, findTail, scrut4, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    prevCont = cur1;
    handlerCont = cur1.nextHandler;
    tmp10: while (true) {
      if (handlerCont instanceof this.__HandleBlock.class) {
        scrut = handlerCont.handler !== cur1.handler;
        if (scrut) {
          prevCont = handlerCont;
          handlerCont = handlerCont.nextHandler;
          tmp = null;
          continue tmp10;
        } else {
          tmp = null;
        }
      } else {
        tmp = null;
      }
      break;
    }
    scrut1 = handlerCont === null;
    if (scrut1) {
      return cur1;
    } else {
      tmp1 = null;
    }
    origTail = cur1.tailHandler;
    prevCont.nextHandler = null;
    cur1.tailHandler = prevCont;
    savedNext = handlerCont.next;
    tmp2 = this.__resume(cur1, handlerCont);
    tmp3 = cur1.handlerFun(tmp2) ?? null;
    cur1 = tmp3;
    scrut2 = savedNext !== handlerCont.next;
    if (scrut2) {
      handlerCont.next.next = savedNext;
      scrut3 = handlerCont.tail === handlerCont;
      if (scrut3) {
        handlerCont.tail = handlerCont.next;
        tmp4 = null;
      } else {
        tmp4 = null;
      }
      tmp5 = tmp4;
    } else {
      tmp5 = null;
    }
    if (cur1 instanceof this.__EffectSig.class) {
      cur1.tailHandler.nextHandler = handlerCont;
      cur1.tailHandler = origTail;
      return cur1;
    } else {
      tmp6 = this.__resume(handlerCont, null);
      tmp7 = tmp6(cur1) ?? null;
      cur1 = tmp7;
      if (cur1 instanceof this.__EffectSig.class) {
        findTail = cur1;
        tmp11: while (true) {
          scrut4 = findTail.nextHandler;
          if (scrut4 instanceof this.__HandleBlock.class) {
            findTail = findTail.nextHandler;
            tmp8 = null;
            continue tmp11;
          } else {
            tmp8 = null;
          }
          break;
        }
        cur1.tailHandler = findTail;
        tmp9 = null;
      } else {
        tmp9 = null;
      }
      return cur1;
    }
  } 
  __resume(cur2, tail) {
    return (value) => {
      let scrut, cont, scrut1, scrut2, scrut3, scrut4, nxt, scrut5, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22;
      scrut = cur2.resumed;
      if (scrut) {
        throw Error("Multiple resumption");
      } else {
        tmp = null;
      }
      cur2.resumed = true;
      cont = cur2.next;
      tmp23: while (true) {
        if (cont instanceof this.__Cont.class) {
          tmp1 = cont.resume(value) ?? null;
          value = tmp1;
          if (value instanceof this.__EffectSig.class) {
            value.tail = tail;
            scrut1 = cur2.tailHandler !== cur2;
            if (scrut1) {
              value.tailHandler.nextHandler = cur2.nextHandler;
              value.tailHandler = cur2.tailHandler;
              tmp2 = null;
            } else {
              tmp2 = null;
            }
            return value;
          } else {
            cont = cont.next;
            tmp3 = null;
          }
          tmp4 = tmp3;
          continue tmp23;
        } else {
          tmp4 = null;
        }
        break;
      }
      tmp24: while (true) {
        scrut2 = cur2.nextHandler;
        if (scrut2 instanceof this.__HandleBlock.class) {
          scrut4 = cur2.nextHandler.next;
          if (scrut4 instanceof this.__Cont.class) {
            nxt = cur2.nextHandler.next;
            tmp5 = nxt.resume(value) ?? null;
            value = tmp5;
            if (value instanceof this.__EffectSig.class) {
              tmp6 = cur2.tailHandler !== cur2;
              tmp7 = this.assert(tmp6) ?? null;
              tmp8 = cur2.nextHandler !== null;
              tmp9 = this.assert(tmp8) ?? null;
              scrut5 = cur2.nextHandler.next === value.tail.next;
              if (scrut5) {
                value.tail.next = null;
                tmp10 = null;
              } else {
                cur2.nextHandler.next = cur2.nextHandler.next.next;
                tmp10 = null;
              }
              value.tail = tail;
              value.tailHandler.nextHandler = cur2.nextHandler;
              value.tailHandler = cur2.tailHandler;
              return value;
            } else {
              tmp11 = cur2.nextHandler.next !== cur2.nextHandler.next.next;
              tmp12 = this.assert(tmp11) ?? null;
              cur2.nextHandler.next = cur2.nextHandler.next.next;
              tmp13 = null;
            }
            tmp14 = tmp13;
            continue tmp24;
          } else {
            scrut3 = true;
            if (scrut3) {
              tmp15 = cur2.nextHandler.next === null;
              tmp16 = this.assert(tmp15) ?? null;
              tmp17 = cur2.nextHandler !== cur2.nextHandler.nextHandler;
              tmp18 = this.assert(tmp17) ?? null;
              cur2.nextHandler = cur2.nextHandler.nextHandler;
              tmp14 = null;
              continue tmp24;
            } else {
              tmp19 = cur2.nextHandler === null;
              tmp20 = this.assert(tmp19) ?? null;
              return value;
            }
          }
        } else {
          tmp21 = cur2.nextHandler === null;
          tmp22 = this.assert(tmp21) ?? null;
          return value;
        }
        break;
      }
      return tmp14;
    };
  }
  toString() { return "Predef"; }
}; const Predef = new Predef$class;
Predef.class = Predef$class;
null
export default Predef;
