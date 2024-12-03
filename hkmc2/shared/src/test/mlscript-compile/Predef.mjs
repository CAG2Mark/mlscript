const Predef$class = class Predef {
  constructor() {
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
    this.Test = class Test {
      constructor() {
        this.y = 1;
      }
      toString() { return "Test"; }
    };
    this.__Cont = function __Cont(resume1, resumed1, next1, __isCont1) { return new __Cont.class(resume1, resumed1, next1, __isCont1); };
    this.__Cont.class = class __Cont {
      constructor(resume, resumed, next, __isCont) {
        this.resume = resume;
        this.resumed = resumed;
        this.next = next;
        this.__isCont = __isCont;
        
      }
      toString() { return "__Cont(" + this.resume + ", " + this.resumed + ", " + this.next + ", " + this.__isCont + ")"; }
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
  pipe(x2, f) {
    return f(x2);
  } 
  apply(receiver, f1) {
    return (...args) => {
      return f1(receiver, ...args);
    };
  } 
  call(receiver1, f2) {
    return (...args) => {
      return f2.call(receiver1, ...args);
    };
  } 
  print(x3) {
    let tmp;
    tmp = String(x3);
    return console.log(tmp);
  } 
  tupleSlice(xs, i, j) {
    let tmp;
    tmp = xs.length - j;
    return globalThis.Array.prototype.slice.call(xs, i, tmp);
  } 
  tupleGet(xs1, i1) {
    return globalThis.Array.prototype.at.call(xs1, i1);
  } 
  stringStartsWith(string, prefix) {
    return string.startsWith(prefix);
  } 
  stringGet(string1, i2) {
    return string1.at(i2);
  } 
  stringDrop(string2, n) {
    return string2.slice(n);
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
      throw globalThis.Error(tmp9);
    } else {
      return undefined;
    }
  } 
  __resume(cont, tail) {
    return (value) => {
      let scrut, tmp, tmp1, tmp2;
      tmp3: while (true) {
        if (cont) {
          tmp = cont.resume(value);
          value = tmp;
          if (value) {
            scrut = value.__isCont;
            if (scrut) {
              value.tail = tail;
              return value;
            } else {
              cont = cont.next;
              tmp1 = undefined;
            }
          } else {
            cont = cont.next;
            tmp1 = undefined;
          }
          tmp2 = tmp1;
          continue tmp3;
        } else {
          tmp2 = value;
        }
        break;
      }
      return tmp2;
    };
  } 
  __debugCont(cont1) {
    let msg, first, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    msg = "Chain: ";
    first = true;
    tmp9: while (true) {
      if (cont1) {
        if (first) {
          first = false;
          tmp = undefined;
        } else {
          tmp1 = msg + " -> ";
          msg = tmp1;
          tmp = undefined;
        }
        tmp2 = msg + "(";
        tmp3 = tmp2 + cont1.constructor.name;
        msg = tmp3;
        scrut = cont1.tail;
        if (scrut) {
          tmp4 = msg + " with tail ";
          tmp5 = tmp4 + cont1.tail.constructor.name;
          msg = tmp5;
          tmp6 = undefined;
        } else {
          tmp6 = undefined;
        }
        tmp7 = msg + ")";
        msg = tmp7;
        cont1 = cont1.next;
        tmp8 = undefined;
        continue tmp9;
      } else {
        tmp8 = this.print(msg);
      }
      break;
    }
    return tmp8;
  }
  toString() { return "Predef"; }
}; const Predef = new Predef$class;
Predef.class = Predef$class;
undefined
export default Predef;
