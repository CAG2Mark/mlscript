const Predef$class = class Predef {
  constructor() {
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
  call(receiver, f1) {
    return (arg) => {
      return f1.call(receiver, arg);
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
  toString() { return "Predef"; }
}; const Predef = new Predef$class;
Predef.class = Predef$class;
undefined
export default Predef;
