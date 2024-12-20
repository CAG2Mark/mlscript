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
    this.__Cont = function __Cont(next1, resumed1) { return new __Cont.class(next1, resumed1); };
    this.__Cont.class = class __Cont {
      constructor(next, resumed) {
        this.next = next;
        this.resumed = resumed;
      }
      toString() { return "__Cont(" + this.next + ", " + this.resumed + ")"; }
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
  print(x4) {
    let tmp;
    tmp = String(x4);
    return console.log(tmp) ?? null;
  } 
  tupleSlice(xs, i, j) {
    let tmp;
    tmp = xs.length - j;
    return globalThis.Array.prototype.slice.call(xs, i, tmp) ?? null;
  } 
  tupleGet(xs1, i1) {
    return globalThis.Array.prototype.at.call(xs1, i1);
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
    tmp = new this.__Cont.class(undefined, undefined);
    res = tmp;
    res.tail = res;
    res.tailHandler = res;
    res.handler = handler;
    res.handlerFun = handlerFun;
    return res;
  } 
  __handleBlockImpl(cur, handler1) {
    let handlerTailList, nxt, scrut, handlerCont, tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = new this.__Cont.class(undefined, undefined);
    handlerTailList = tmp;
    handlerTailList.tail = handlerTailList;
    tmp5: while (true) {
      if (cur instanceof this.__Return.class) {
        return cur;
      } else {
        if (cur instanceof this.__Cont.class) {
          tmp1 = this.__handleEffect(cur, handler1, handlerTailList);
          nxt = tmp1;
          scrut = cur === nxt;
          if (scrut) {
            tmp2 = new this.__Cont.class(undefined, undefined);
            handlerCont = tmp2;
            handlerCont.next = handlerTailList.next;
            handlerCont.handler = handler1;
            cur.tailHandler.nextHandler = handlerCont;
            cur.tailHandler = handlerCont;
            cur.tail = handlerTailList.tail;
            return cur;
          } else {
            cur = nxt;
            tmp3 = null;
          }
          tmp4 = tmp3;
          continue tmp5;
        } else {
          return cur;
        }
      }
      break;
    }
    return tmp4;
  } 
  __handleEffect(cur1, handler2, handlerTailList) {
    let handlerCont, scrut, scrut1, savedNext, scrut2, scrut3, savedNext1, scrut4, scrut5, saved, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15;
    handlerCont = cur1.nextHandler;
    tmp16: while (true) {
      if (handlerCont instanceof this.__Cont.class) {
        scrut = handlerCont.handler !== cur1.handler;
        if (scrut) {
          handlerCont = handlerCont.nextHandler;
          tmp = null;
          continue tmp16;
        } else {
          tmp = null;
        }
      } else {
        tmp = null;
      }
      break;
    }
    if (handlerCont) {
      savedNext1 = handlerCont.next;
      tmp1 = this.__resume(cur1, handlerCont, handlerCont);
      tmp2 = cur1.handlerFun(tmp1) ?? null;
      cur1 = tmp2;
      scrut4 = savedNext1 !== handlerCont.next;
      if (scrut4) {
        handlerCont.next.next = savedNext1;
        tmp3 = null;
      } else {
        tmp3 = null;
      }
      if (cur1 instanceof this.__Cont.class) {
        return cur1;
      } else {
        if (cur1 instanceof this.__Return.class) {
          return cur1;
        } else {
          tmp4 = this.__resume(handlerCont, undefined, undefined);
          tmp5 = tmp4(cur1) ?? null;
          cur1 = tmp5;
          tmp6 = null;
        }
        tmp7 = tmp6;
      }
      tmp8 = tmp7;
    } else {
      scrut1 = handler2 === cur1.handler;
      if (scrut1) {
        savedNext = handlerTailList.next;
        tmp9 = this.__resume(cur1, handlerTailList, handlerCont);
        tmp10 = cur1.handlerFun(tmp9) ?? null;
        cur1 = tmp10;
        scrut2 = savedNext !== handlerTailList.next;
        if (scrut2) {
          handlerTailList.next.next = savedNext;
          scrut3 = savedNext === undefined;
          if (scrut3) {
            handlerTailList.tail = handlerTailList.next;
            tmp11 = null;
          } else {
            tmp11 = null;
          }
          tmp12 = tmp11;
        } else {
          tmp12 = null;
        }
        tmp13 = tmp12;
      } else {
        return cur1;
      }
      tmp8 = tmp13;
    }
    tmp17: while (true) {
      if (cur1 instanceof this.__Cont.class) {
        return cur1;
      } else {
        if (cur1 instanceof this.__Return.class) {
          return cur1;
        } else {
          scrut5 = handlerTailList.next;
          if (scrut5 instanceof this.__Cont.class) {
            saved = handlerTailList.next.next;
            tmp14 = handlerTailList.next.resume(cur1) ?? null;
            cur1 = tmp14;
            handlerTailList.next = saved;
            tmp15 = null;
            continue tmp17;
          } else {
            tmp15 = cur1;
          }
        }
      }
      break;
    }
    return tmp15;
  } 
  __resume(cur2, tail, handlerCont) {
    return (value) => {
      let nextHandler, cont, scrut, tmp, tmp1, tmp2, tmp3;
      nextHandler = cur2.nextHandler;
      cont = cur2.next;
      tmp4: while (true) {
        if (cont instanceof this.__Cont.class) {
          tmp = cont.resume(value) ?? null;
          value = tmp;
          if (value instanceof this.__Cont.class) {
            value.tail = tail;
            value.tailHandler.nextHandler = nextHandler;
            return value;
          } else {
            if (value instanceof this.__Return.class) {
              return value;
            } else {
              cont = cont.next;
              tmp1 = null;
            }
            tmp2 = tmp1;
          }
          tmp3 = tmp2;
          continue tmp4;
        } else {
          scrut = nextHandler !== handlerCont;
          if (scrut) {
            cont = nextHandler.next;
            nextHandler = nextHandler.nextHandler;
            tmp3 = null;
            continue tmp4;
          } else {
            tmp3 = value;
          }
        }
        break;
      }
      return tmp3;
    };
  }
  toString() { return "Predef"; }
}; const Predef = new Predef$class;
Predef.class = Predef$class;
null
export default Predef;
