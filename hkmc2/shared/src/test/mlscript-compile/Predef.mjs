import runtime from "./Runtime.mjs";
import Runtime from "./Runtime.mjs";
let Predef1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8;
lambda8 = (undefined, function (arg1, arg2) {
  return arg1 + arg2
});
lambda7 = (undefined, function (acc, x) {
  let tmp, tmp1, tmp2;
  if (typeof x === 'string') {
    tmp = true;
  } else {
    tmp = false;
  }
  tmp1 = runtime.safeCall(Predef1.assert(tmp));
  tmp2 = acc + x;
  return (tmp1 , tmp2)
});
lambda = (undefined, function (arg1, arg2) {
  return arg1 + arg2
});
lambda1 = (undefined, function (arg1, arg2) {
  return arg1 + arg2
});
lambda2 = (undefined, function (arg1, arg2) {
  return arg1 + arg2
});
lambda3 = (undefined, function (arg1, arg2) {
  return arg1 + arg2
});
lambda4 = (undefined, function (caseScrut) {
  let first1, first0, k, v, tmp, tmp1;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    k = first0;
    v = first1;
    tmp = k + ": ";
    tmp1 = Predef1.render(v);
    return tmp + tmp1
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda5 = (undefined, function (arg1, arg2) {
  return arg1 + arg2
});
lambda6 = (undefined, function (caseScrut) {
  let first1, first0, k, v, tmp, tmp1;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    k = first0;
    v = first1;
    tmp = k + ": ";
    tmp1 = Predef1.render(v);
    return tmp + tmp1
  } else {
    throw new globalThis.Error("match error");
  }
});
Predef1 = class Predef {
  static {
    Predef1 = Predef;
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
        let scrut, tmp, tmp1, tmp2, tmp3, tmp4;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          tmp = runtime.safeCall("| ".repeat(TraceLogger.indentLvl));
          tmp1 = runtime.safeCall("  ".repeat(TraceLogger.indentLvl));
          tmp2 = "\n" + tmp1;
          tmp3 = msg.replaceAll("\n", tmp2);
          tmp4 = tmp + tmp3;
          return runtime.safeCall(globalThis.console.log(tmp4))
        } else {
          return runtime.Unit
        }
      }
      static toString() { return "TraceLogger"; }
    };
    this.Test = class Test {
      constructor() {
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
    return runtime.safeCall(f(...args))
  } 
  static pipeInto(x2, f1) {
    return runtime.safeCall(f1(x2))
  } 
  static pipeFrom(f2, x3) {
    return runtime.safeCall(f2(x3))
  } 
  static tap(x4, f3) {
    let tmp;
    tmp = runtime.safeCall(f3(x4));
    return (tmp , x4)
  } 
  static pat(f4, x5) {
    let tmp;
    tmp = runtime.safeCall(f4(x5));
    return (tmp , x5)
  } 
  static andThen(f5, g) {
    return (x6) => {
      let tmp;
      tmp = runtime.safeCall(f5(x6));
      return runtime.safeCall(g(tmp))
    }
  } 
  static compose(f6, g1) {
    return (x6) => {
      let tmp;
      tmp = runtime.safeCall(g1(x6));
      return runtime.safeCall(f6(tmp))
    }
  } 
  static passTo(receiver, f7) {
    return (...args1) => {
      return runtime.safeCall(f7(receiver, ...args1))
    }
  } 
  static call(receiver1, f8) {
    return (...args1) => {
      return f8.call(receiver1, ...args1)
    }
  } 
  static pass1(f9) {
    return (...xs) => {
      return runtime.safeCall(f9(xs[0]))
    }
  } 
  static pass2(f10) {
    return (...xs) => {
      return runtime.safeCall(f10(xs[0], xs[1]))
    }
  } 
  static pass3(f11) {
    return (...xs) => {
      return runtime.safeCall(f11(xs[0], xs[1], xs[2]))
    }
  } 
  static passing(f12, ...args1) {
    return f12.bind(null, ...args1)
  } 
  static print(...xs) {
    let tmp, tmp1;
    tmp = Predef.map(Predef.renderAsStr);
    tmp1 = runtime.safeCall(tmp(...xs));
    return runtime.safeCall(globalThis.console.log(...tmp1))
  } 
  static printRaw(x6) {
    let tmp;
    tmp = Predef.render(x6);
    return runtime.safeCall(globalThis.console.log(tmp))
  } 
  static interleave(sep) {
    return (...args2) => {
      let res, len, i, scrut, idx, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
      scrut2 = args2.length === 0;
      if (scrut2 === true) {
        return []
      } else {
        tmp = args2.length * 2;
        tmp1 = tmp - 1;
        tmp2 = globalThis.Array(tmp1);
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
    if (typeof arg === 'string') {
      return arg
    } else {
      return Predef.render(arg)
    }
  } 
  static render(arg1) {
    let ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34;
    if (arg1 === undefined) {
      return "undefined"
    } else if (arg1 === null) {
      return "null"
    } else if (arg1 instanceof globalThis.Array) {
      tmp = Predef.fold(lambda);
      tmp1 = Predef.interleave(", ");
      tmp2 = Predef.map(Predef.render);
      tmp3 = runtime.safeCall(tmp2(...arg1));
      tmp4 = runtime.safeCall(tmp1(...tmp3));
      return runtime.safeCall(tmp("[", ...tmp4, "]"))
    } else if (typeof arg1 === 'string') {
      return runtime.safeCall(globalThis.JSON.stringify(arg1))
    } else if (arg1 instanceof globalThis.Set) {
      tmp5 = Predef.fold(lambda1);
      tmp6 = Predef.interleave(", ");
      tmp7 = Predef.map(Predef.render);
      tmp8 = runtime.safeCall(tmp7(...arg1));
      tmp9 = runtime.safeCall(tmp6(...tmp8));
      return runtime.safeCall(tmp5("Set{", ...tmp9, "}"))
    } else if (arg1 instanceof globalThis.Map) {
      tmp10 = Predef.fold(lambda2);
      tmp11 = Predef.interleave(", ");
      tmp12 = Predef.map(Predef.render);
      tmp13 = runtime.safeCall(tmp12(...arg1));
      tmp14 = runtime.safeCall(tmp11(...tmp13));
      return runtime.safeCall(tmp10("Map{", ...tmp14, "}"))
    } else if (arg1 instanceof globalThis.Function) {
      p = globalThis.Object.getOwnPropertyDescriptor(arg1, "prototype");
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
          tmp19 = runtime.safeCall(globalThis.Object.entries(arg1));
          es = tmp19;
          tmp20 = Predef.fold(lambda3);
          tmp21 = Predef.interleave(", ");
          tmp22 = lambda4;
          tmp23 = Predef.map(tmp22);
          tmp24 = runtime.safeCall(tmp23(...es));
          tmp25 = runtime.safeCall(tmp21(...tmp24));
          return runtime.safeCall(tmp20("{", ...tmp25, "}"))
        } else {
          return globalThis.String(arg1)
        }
      }
    } else if (arg1 instanceof globalThis.Object) {
      scrut = arg1.constructor.name;
      if (scrut === "Object") {
        tmp26 = runtime.safeCall(globalThis.Object.entries(arg1));
        es = tmp26;
        tmp27 = Predef.fold(lambda5);
        tmp28 = Predef.interleave(", ");
        tmp29 = lambda6;
        tmp30 = Predef.map(tmp29);
        tmp31 = runtime.safeCall(tmp30(...es));
        tmp32 = runtime.safeCall(tmp28(...tmp31));
        return runtime.safeCall(tmp27("{", ...tmp32, "}"))
      } else {
        return globalThis.String(arg1)
      }
    } else {
      ts = arg1["toString"];
      if (ts === undefined) {
        tmp33 = typeof arg1;
        tmp34 = "[" + tmp33;
        return tmp34 + "]"
      } else {
        return runtime.safeCall(ts.call(arg1))
      }
    }
  } 
  static notImplemented(msg) {
    let tmp;
    tmp = "Not implemented: " + msg;
    throw globalThis.Error(tmp);
  } 
  static get notImplementedError() {
    throw globalThis.Error("Not implemented");
  } 
  static tuple(...xs1) {
    return xs1
  } 
  static tupleSlice(xs2, i, j) {
    let tmp;
    tmp = xs2.length - j;
    return runtime.safeCall(globalThis.Array.prototype.slice.call(xs2, i, tmp))
  } 
  static tupleGet(xs3, i1) {
    return globalThis.Array.prototype.at.call(xs3, i1)
  } 
  static map(f13) {
    return (...xs4) => {
      let tmp;
      tmp = Predef.pass1(f13);
      return runtime.safeCall(xs4.map(tmp))
    }
  } 
  static fold(f14) {
    return (init, ...rest) => {
      let i2, len, scrut, tmp, tmp1, tmp2, tmp3;
      i2 = 0;
      len = rest.length;
      tmp4: while (true) {
        scrut = i2 < len;
        if (scrut === true) {
          tmp = runtime.safeCall(rest.at(i2));
          tmp1 = runtime.safeCall(f14(init, tmp));
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
      let len, i2, init, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
      len = rest.length;
      scrut1 = len == 0;
      if (scrut1 === true) {
        return first
      } else {
        tmp = len - 1;
        i2 = tmp;
        tmp1 = runtime.safeCall(rest.at(i2));
        init = tmp1;
        tmp6: while (true) {
          scrut = i2 > 0;
          if (scrut === true) {
            tmp2 = i2 - 1;
            i2 = tmp2;
            tmp3 = runtime.safeCall(rest.at(i2));
            tmp4 = runtime.safeCall(f15(tmp3, init));
            init = tmp4;
            tmp5 = runtime.Unit;
            continue tmp6;
          } else {
            tmp5 = runtime.Unit;
          }
          break;
        }
        return runtime.safeCall(f15(first, init))
      }
    }
  } 
  static mkStr(...xs4) {
    let tmp, tmp1;
    tmp = lambda7;
    tmp1 = Predef.fold(tmp);
    return runtime.safeCall(tmp1(...xs4))
  } 
  static stringStartsWith(string, prefix) {
    return runtime.safeCall(string.startsWith(prefix))
  } 
  static stringGet(string1, i2) {
    return runtime.safeCall(string1.at(i2))
  } 
  static stringDrop(string2, n) {
    return runtime.safeCall(string2.slice(n))
  } 
  static get unreachable() {
    throw globalThis.Error("unreachable");
  } 
  static checkArgs(functionName, expected, isUB, got) {
    let scrut, name, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
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
      tmp5 = Predef.fold(lambda8);
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
      tmp8 = runtime.safeCall(tmp5("Function", name, " expected ", tmp6, expected, " argument", tmp7, " but got ", got));
      throw globalThis.Error(tmp8);
    } else {
      return runtime.Unit
    }
  } 
  static enterHandleBlock(handler, body) {
    return Runtime.enterHandleBlock(handler, body)
  }
  static toString() { return "Predef"; }
};
let Predef = Predef1; export default Predef;
