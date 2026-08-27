const definitionMetadata = globalThis.Symbol.for("mlscript.definitionMetadata");
const prettyPrint = globalThis.Symbol.for("mlscript.prettyPrint");
import runtime from "./Runtime.mjs";
import RuntimeJS from "./RuntimeJS.mjs";
import Rendering from "./Rendering.mjs";
import LazyArray from "./LazyArray.mjs";
import Iter from "./Iter.mjs";
let cntSegment, errorSep, Runtime1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda$, lambda$1, lambda$2, lambda$3, lambda$4, Capture$scope291, lambda$5, Capture$scope401, Capture$handleEffect1, lambda$6, lambda$7, Capture$resumeContTrace1, lambda$8, lambda$9;
lambda$9 = (undefined, function (resumeContTrace$cap, curFrame) {
  return () => {
    return runtime.safeCall(curFrame.resume(resumeContTrace$cap.value$0))
  }
});
lambda$8 = (undefined, function (Runtime2) {
  return (err) => {
    return Runtime2.checkUnhandledErr
  }
});
lambda7 = (undefined, function (resumeContTrace$cap, curFrame) {
  return runtime.safeCall(curFrame.resume(resumeContTrace$cap.value$0))
});
lambda8 = (undefined, function (Runtime2, err) {
  return Runtime2.checkUnhandledErr
});
(class Capture$resumeContTrace {
  static {
    Capture$resumeContTrace1 = this
  }
  constructor(value$0) {
    this.value$0 = value$0;
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Capture$resumeContTrace"];
});
lambda$7 = (undefined, function (handleEffect$cap, Runtime2) {
  return () => {
    let tmp;
    tmp = Runtime2.resume(handleEffect$cap.cur$0.contTrace);
    return runtime.safeCall(handleEffect$cap.cur$0.handlerFun(tmp))
  }
});
lambda$6 = (undefined, function (Runtime2, saved, tmp) {
  return () => {
    return Runtime2.resumeContTrace(saved, tmp)
  }
});
lambda5 = (undefined, function (handleEffect$cap, Runtime2) {
  let tmp;
  tmp = Runtime2.resume(handleEffect$cap.cur$0.contTrace);
  return runtime.safeCall(handleEffect$cap.cur$0.handlerFun(tmp))
});
lambda6 = (undefined, function (Runtime2, saved, tmp) {
  return Runtime2.resumeContTrace(saved, tmp)
});
(class Capture$handleEffect {
  static {
    Capture$handleEffect1 = this
  }
  constructor(cur$0) {
    this.cur$0 = cur$0;
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Capture$handleEffect"];
});
errorSep = function errorSep(loc) {
  runtime.safeCall(globalThis.console.log("--------------------------------"));
  runtime.safeCall(globalThis.console.log("!!! HANDLER VALIDATION ERROR !!!"));
  runtime.safeCall(globalThis.console.log("--------------------------------"));
  return runtime.safeCall(globalThis.console.log("at:", loc))
};
(class Capture$scope40 {
  static {
    Capture$scope401 = this
  }
  constructor(cnt$0, curSegment$1) {
    this.curSegment$1 = curSegment$1;
    this.cnt$0 = cnt$0;
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Capture$scope40"];
});
cntSegment = function cntSegment(scope40$cap) {
  lbl: while (true) {
    let scrut, tmp;
    scrut = scope40$cap.curSegment$1.next !== null;
    if (scrut === true) {
      scope40$cap.curSegment$1 = scope40$cap.curSegment$1.next;
      tmp = scope40$cap.cnt$0 + 1;
      scope40$cap.cnt$0 = tmp;
      continue lbl
    }
    break;
  }
  return runtime.Unit
};
(class Capture$scope29 {
  static {
    Capture$scope291 = this
  }
  constructor(result$0) {
    this.result$0 = result$0;
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Capture$scope29"];
});
lambda$5 = (undefined, function (scope29$cap, cont) {
  return (m, marker) => {
    return lambda4(scope29$cap, cont, m, marker)
  }
});
lambda4 = (undefined, function (scope29$cap, cont, m, marker) {
  let scrut, tmp, tmp1;
  scrut = runtime.safeCall(m.has(cont));
  if (scrut === true) {
    tmp = ", " + marker;
    tmp1 = scope29$cap.result$0 + tmp;
    scope29$cap.result$0 = tmp1;
    return runtime.Unit
  }
  return runtime.Unit;
});
lambda3 = (undefined, function (l) {
  let tmp, tmp1;
  tmp = l.localName + "=";
  tmp1 = runtime.safeCall(Rendering.render(l.value));
  return tmp + tmp1
});
lambda$4 = (undefined, function (Runtime2, body) {
  return () => {
    return Runtime2.enterHandleBlock(Runtime2.StackDelayHandler, body)
  }
});
lambda$3 = (undefined, function (Runtime2) {
  return (err) => {
    return lambda1(Runtime2, err)
  }
});
lambda$2 = (undefined, function (Runtime2) {
  return (err) => {
    return lambda2(Runtime2, err)
  }
});
lambda = (undefined, function (Runtime2, body) {
  return Runtime2.enterHandleBlock(Runtime2.StackDelayHandler, body)
});
lambda1 = (undefined, function (Runtime2, err) {
  let scrut;
  scrut = Runtime2.curEffect === null;
  if (scrut === true) {
    throw err
  }
  return Runtime2.handleEffects(Runtime2.curEffect);
});
lambda2 = (undefined, function (Runtime2, err) {
  let scrut;
  scrut = Runtime2.curEffect === null;
  if (scrut === true) {
    throw err
  }
  return Runtime2.handleEffects(Runtime2.curEffect);
});
lambda$1 = (undefined, function (Runtime2) {
  return (k) => {
    Runtime2.stackResume = k;
    return runtime.Unit
  }
});
lambda10 = (undefined, function (Runtime2, k) {
  Runtime2.stackResume = k;
  return runtime.Unit
});
lambda$ = (undefined, function (Runtime2, EffectHandle1, value) {
  return () => {
    return lambda9(Runtime2, EffectHandle1, value)
  }
});
lambda9 = (undefined, function (Runtime2, EffectHandle1, value) {
  let contTrace, scrut;
  contTrace = EffectHandle1.reified.contTrace;
  scrut = contTrace.resumed;
  if (scrut === true) {
    throw runtime.safeCall(globalThis.Error("Multiple resumption"))
  }
  contTrace.resumed = true;
  return Runtime2.resumeContTrace(contTrace, value);
});
(class Runtime {
  static {
    Runtime1 = this
  }
  static #fcfid;
  static #curContTrace;
  static #curEffect;
  static #resumeValue;
  static #resumeArr;
  static #resumeIdx;
  static #resumePc;
  static #latestId;
  static #handleEffectsCall;
  static #stackLimit;
  static #stackDepth;
  static #stackHandler;
  static #stackResume;
  static get curContTrace() { return Runtime.#curContTrace; }
  static set curContTrace(value) { Runtime.#curContTrace = value; }
  static get curEffect() { return Runtime.#curEffect; }
  static set curEffect(value) { Runtime.#curEffect = value; }
  static get resumeValue() { return Runtime.#resumeValue; }
  static set resumeValue(value) { Runtime.#resumeValue = value; }
  static get resumeArr() { return Runtime.#resumeArr; }
  static set resumeArr(value) { Runtime.#resumeArr = value; }
  static get resumeIdx() { return Runtime.#resumeIdx; }
  static set resumeIdx(value) { Runtime.#resumeIdx = value; }
  static get resumePc() { return Runtime.#resumePc; }
  static set resumePc(value) { Runtime.#resumePc = value; }
  static get latestId() { return Runtime.#latestId; }
  static set latestId(value) { Runtime.#latestId = value; }
  static get handleEffectsCall() { return Runtime.#handleEffectsCall; }
  static set handleEffectsCall(value) { Runtime.#handleEffectsCall = value; }
  static get stackLimit() { return Runtime.#stackLimit; }
  static set stackLimit(value) { Runtime.#stackLimit = value; }
  static get stackDepth() { return Runtime.#stackDepth; }
  static set stackDepth(value) { Runtime.#stackDepth = value; }
  static get stackHandler() { return Runtime.#stackHandler; }
  static set stackHandler(value) { Runtime.#stackHandler = value; }
  static get stackResume() { return Runtime.#stackResume; }
  static set stackResume(value) { Runtime.#stackResume = value; }
  static {
    let tmp;
    (class Unit {
      static {
        new this
      }
      constructor() {
        Runtime.Unit = this;
        Object.defineProperty(this, "class", {
          value: Unit
        });
        globalThis.Object.freeze(this);
      }
      toString() {
        return "()"
      }
      [prettyPrint]() { return this.toString(); }
      static [definitionMetadata] = ["object", "Unit"];
    });
    (class Continue {
      static {
        new this
      }
      constructor() {
        Runtime.Continue = this;
        Object.defineProperty(this, "class", {
          value: Continue
        });
        globalThis.Object.freeze(this);
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "Continue"];
    });
    (class LoopEnd {
      static {
        new this
      }
      constructor() {
        Runtime.LoopEnd = this;
        Object.defineProperty(this, "class", {
          value: LoopEnd
        });
        globalThis.Object.freeze(this);
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "LoopEnd"];
    });
    Runtime.short_and = RuntimeJS.short_and;
    Runtime.short_or = RuntimeJS.short_or;
    Runtime.bitand = RuntimeJS.bitand;
    Runtime.bitnot = RuntimeJS.bitnot;
    Runtime.bitor = RuntimeJS.bitor;
    Runtime.shl = RuntimeJS.shl;
    Runtime.try_catch = RuntimeJS.try_catch;
    Runtime.EffectHandle = function EffectHandle(_reified) {
      return globalThis.Object.freeze(new EffectHandle.class(_reified));
    };
    (class EffectHandle {
      static {
        Runtime.EffectHandle.class = this
      }
      constructor(_reified) {
        this.#_reified = _reified;
        this.reified = this.#_reified;
      }
      #_reified;
      resumeWith(value) {
        let lambda$here;
        lambda$here = lambda$(Runtime, this, value);
        return Runtime._try(lambda$here)
      }
      raise() {
        Runtime.curEffect = this.reified;
        return runtime.Unit
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "EffectHandle", [null]];
    });
    Runtime.MatchSuccess = function MatchSuccess(output, bindings) {
      return globalThis.Object.freeze(new MatchSuccess.class(output, bindings));
    };
    (class MatchSuccess {
      static {
        Runtime.MatchSuccess.class = this
      }
      constructor(output, bindings) {
        this.output = output;
        this.bindings = bindings;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "MatchSuccess", ["output", "bindings"]];
    });
    Runtime.MatchFailure = function MatchFailure(errors) {
      return globalThis.Object.freeze(new MatchFailure.class(errors));
    };
    (class MatchFailure {
      static {
        Runtime.MatchFailure.class = this
      }
      constructor(errors) {
        this.errors = errors;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "MatchFailure", ["errors"]];
    });
    (class Tuple {
      static {
        Runtime.Tuple = this
      }
      static {
        Tuple.split = LazyArray.__split;
      }
      static slice(xs, i, j) {
        let tmp1;
        tmp1 = xs.length - j;
        return runtime.safeCall(xs.slice(i, tmp1))
      }
      static lazySlice(xs, i, j) {
        let callPrefix;
        callPrefix = runtime.safeCall(LazyArray.dropLeftRight(i, j));
        return runtime.safeCall(callPrefix(xs))
      }
      static lazyConcat(...args) {
        return runtime.safeCall(LazyArray.__concat(...args))
      }
      static get(xs, i) {
        let scrut, scrut1, tmp1;
        scrut = i >= xs.length;
        if (scrut === true) {
          throw runtime.safeCall(globalThis.RangeError("Tuple.get: index out of bounds"))
        }
        tmp1 = - xs.length;
        scrut1 = i < tmp1;
        if (scrut1 === true) {
          throw runtime.safeCall(globalThis.RangeError("Tuple.get: negative index out of bounds"))
        }
        return xs.at(i);
      }
      static isArrayLike(xs) {
        return runtime.safeCall(Iter.isArrayLike(xs))
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Tuple"];
    });
    (class Str {
      static {
        Runtime.Str = this
      }
      static startsWith(string, prefix) {
        return runtime.safeCall(string.startsWith(prefix))
      }
      static get(string, i) {
        let scrut;
        scrut = i >= string.length;
        if (scrut === true) {
          throw runtime.safeCall(globalThis.RangeError("Str.get: index out of bounds"))
        }
        return runtime.safeCall(string.at(i));
      }
      static take(string, n) {
        return runtime.safeCall(string.slice(0, n))
      }
      static leave(string, n) {
        return runtime.safeCall(string.slice(n))
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Str"];
    });
    Runtime.render = Rendering.render;
    (class TraceLogger {
      static {
        Runtime.TraceLogger = this
      }
      static #enabled;
      static #indentLvl;
      static get enabled() { return TraceLogger.#enabled; }
      static set enabled(value) { TraceLogger.#enabled = value; }
      static get indentLvl() { return TraceLogger.#indentLvl; }
      static set indentLvl(value) { TraceLogger.#indentLvl = value; }
      static {
        TraceLogger.enabled = false;
        TraceLogger.indentLvl = 0;
      }
      static indent() {
        let scrut, prev, tmp1;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          prev = TraceLogger.indentLvl;
          tmp1 = prev + 1;
          TraceLogger.indentLvl = tmp1;
          return prev
        }
        return runtime.Unit;
      }
      static resetIndent(n) {
        let scrut;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          TraceLogger.indentLvl = n;
          return runtime.Unit
        }
        return runtime.Unit;
      }
      static log(msg) {
        let scrut, tmp1, tmp2, tmp3, tmp4, tmp5;
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          tmp1 = runtime.safeCall(("| ").repeat(TraceLogger.indentLvl));
          tmp2 = runtime.safeCall(("  ").repeat(TraceLogger.indentLvl));
          tmp3 = "\n" + tmp2;
          tmp4 = runtime.safeCall(msg.replaceAll("\n", tmp3));
          tmp5 = tmp1 + tmp4;
          return runtime.safeCall(globalThis.console.log(tmp5))
        }
        return runtime.Unit;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "TraceLogger"];
    });
    Runtime.ContTrace = function ContTrace(next, last, nextHandler, lastHandler, resumed) {
      return globalThis.Object.freeze(new ContTrace.class(next, last, nextHandler, lastHandler, resumed));
    };
    (class ContTrace {
      static {
        Runtime.ContTrace.class = this
      }
      constructor(next, last, nextHandler, lastHandler, resumed) {
        this.next = next;
        this.last = last;
        this.nextHandler = nextHandler;
        this.lastHandler = lastHandler;
        this.resumed = resumed;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "ContTrace", ["next", "last", "nextHandler", "lastHandler", "resumed"]];
    });
    tmp = new Runtime.ContTrace.class(null, null, null, null, false);
    Runtime.curContTrace = tmp;
    Runtime.curEffect = null;
    Runtime.resumeValue = null;
    Runtime.resumeArr = null;
    Runtime.resumeIdx = null;
    Runtime.resumePc = -1;
    Runtime.curContTrace.last = Runtime.curContTrace;
    Runtime.curContTrace.lastHandler = Runtime.curContTrace;
    (class FatalEffect {
      static {
        new this
      }
      constructor() {
        Runtime.FatalEffect = this;
        Object.defineProperty(this, "class", {
          value: FatalEffect
        });
        globalThis.Object.freeze(this);
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "FatalEffect"];
    });
    (class PrintStackEffect {
      static {
        new this
      }
      constructor() {
        Runtime.PrintStackEffect = this;
        Object.defineProperty(this, "class", {
          value: PrintStackEffect
        });
        globalThis.Object.freeze(this);
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "PrintStackEffect"];
    });
    Runtime.#fcfid = 0;
    Runtime.FunctionContFrame = function FunctionContFrame(next, fn, varsClass) {
      return globalThis.Object.freeze(new FunctionContFrame.class(next, fn, varsClass));
    };
    (class FunctionContFrame {
      static {
        Runtime.FunctionContFrame.class = this
      }
      constructor(next, fn, varsClass) {
        let tmp1;
        this.next = next;
        this.fn = fn;
        this.varsClass = varsClass;
        this.id = Runtime.#fcfid;
        tmp1 = Runtime.#fcfid + 1;
        Runtime.#fcfid = tmp1;
      }
      resume(value) {
        Runtime.resumeValue = value;
        return runtime.safeCall(this.fn(this.varsClass))
      }
      get getLocals() {
        return runtime.Unit;
      }
      get getNme() {
        return "";
      }
      get getLoc() {
        return "";
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "FunctionContFrame", ["next", "fn", "varsClass"]];
    });
    Runtime.HandlerContFrame = function HandlerContFrame(next, nextHandler, handler) {
      return globalThis.Object.freeze(new HandlerContFrame.class(next, nextHandler, handler));
    };
    (class HandlerContFrame {
      static {
        Runtime.HandlerContFrame.class = this
      }
      constructor(next, nextHandler, handler) {
        this.next = next;
        this.nextHandler = nextHandler;
        this.handler = handler;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "HandlerContFrame", ["next", "nextHandler", "handler"]];
    });
    Runtime.EffectSig = function EffectSig(contTrace, handler, handlerFun, id) {
      return globalThis.Object.freeze(new EffectSig.class(contTrace, handler, handlerFun, id));
    };
    (class EffectSig {
      static {
        Runtime.EffectSig.class = this
      }
      constructor(contTrace, handler, handlerFun, id) {
        this.contTrace = contTrace;
        this.handler = handler;
        this.handlerFun = handlerFun;
        this.id = id;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "EffectSig", ["contTrace", "handler", "handlerFun", "id"]];
    });
    (class NonLocalReturn {
      static {
        Runtime.NonLocalReturn = this
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "NonLocalReturn"];
    });
    Runtime.FnLocalsInfo = function FnLocalsInfo(fnName, locals) {
      return globalThis.Object.freeze(new FnLocalsInfo.class(fnName, locals));
    };
    (class FnLocalsInfo {
      static {
        Runtime.FnLocalsInfo.class = this
      }
      constructor(fnName, locals) {
        this.fnName = fnName;
        this.locals = locals;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "FnLocalsInfo", ["fnName", "locals"]];
    });
    Runtime.LocalVarInfo = function LocalVarInfo(localName, value) {
      return globalThis.Object.freeze(new LocalVarInfo.class(localName, value));
    };
    (class LocalVarInfo {
      static {
        Runtime.LocalVarInfo.class = this
      }
      constructor(localName, value) {
        this.localName = localName;
        this.value = value;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "LocalVarInfo", ["localName", "value"]];
    });
    Runtime.CustomStackError = function CustomStackError(stack) {
      return globalThis.Object.freeze(new CustomStackError.class(stack));
    };
    (class CustomStackError {
      static {
        Runtime.CustomStackError.class = this
      }
      constructor(stack) {
        this.stack = stack;
      }
      toString() {
        return this.stack
      }
      [prettyPrint]() { return this.toString(); }
      static [definitionMetadata] = ["class", "CustomStackError", ["stack"]];
    });
    Runtime.EffectRaised = function EffectRaised(str) {
      return globalThis.Object.freeze(new EffectRaised.class(str));
    };
    (class EffectRaised {
      static {
        Runtime.EffectRaised.class = this
      }
      constructor(str) {
        this.str = str;
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "EffectRaised", ["str"]];
    });
    Runtime.latestId = 0;
    Runtime.handleEffectsCall = 0;
    Runtime.stackLimit = 0;
    Runtime.stackDepth = 0;
    Runtime.stackHandler = null;
    Runtime.stackResume = null;
    (class StackDelayHandler {
      static {
        new this
      }
      constructor() {
        Runtime.StackDelayHandler = this;
        Object.defineProperty(this, "class", {
          value: StackDelayHandler
        });
        globalThis.Object.freeze(this);
      }
      delay() {
        let lambda$here;
        lambda$here = lambda$1(Runtime);
        return Runtime.mkEffect(this, lambda$here)
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["object", "StackDelayHandler"];
    });
    Runtime.Int31 = function Int31(v) {
      return globalThis.Object.freeze(new Int31.class(v));
    };
    (class Int31 {
      static {
        Runtime.Int31.class = this
      }
      constructor(v) {
        this.#v = v;
      }
      #v;
      zext() {
        let tmp1, tmp2;
        tmp1 = runtime.safeCall(Runtime.shl(1, 31));
        tmp2 = runtime.safeCall(Runtime.bitnot(tmp1));
        return runtime.safeCall(Runtime.bitand(this.#v, tmp2))
      }
      sext() {
        let tmp1;
        tmp1 = runtime.safeCall(Runtime.shl(1, 31));
        return runtime.safeCall(Runtime.bitor(this.#v, tmp1))
      }
      toString() { return runtime.render(this); }
      static [definitionMetadata] = ["class", "Int31", [null]];
    });
  }
  static get unreachable() {
    throw runtime.safeCall(globalThis.Error("unreachable"));
  }
  static assertFail(file, line) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = "Assertion failed (" + file;
    tmp1 = tmp + ":";
    tmp2 = tmp1 + line;
    tmp3 = tmp2 + ")";
    throw runtime.safeCall(globalThis.Error(tmp3))
  }
  static checkArgs(functionName, expected, isUB, got) {
    let scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
    tmp = got < expected;
    if (tmp === false) {
      if (isUB === true) {
        tmp2 = got > expected;
      } else {
        tmp2 = false;
      }
      tmp1 = tmp2;
    } else {
      tmp1 = true;
    }
    if (tmp1 === true) {
      scrut = functionName.length > 0;
      if (scrut === true) {
        tmp3 = " '" + functionName;
        tmp4 = tmp3 + "'";
      } else {
        tmp4 = "";
      }
      tmp5 = "Function" + tmp4;
      tmp6 = tmp5 + " expected ";
      if (isUB === true) {
        tmp7 = "";
      } else {
        tmp7 = "at least ";
      }
      tmp8 = tmp6 + tmp7;
      tmp9 = tmp8 + expected;
      tmp10 = tmp9 + " argument";
      scrut1 = expected === 1;
      if (scrut1 === true) {
        tmp11 = "";
      } else {
        tmp11 = "s";
      }
      tmp12 = tmp10 + tmp11;
      tmp13 = tmp12 + " but got ";
      tmp14 = tmp13 + got;
      throw runtime.safeCall(globalThis.Error(tmp14))
    }
    return runtime.Unit;
  }
  static checkSelect(sel, nme, qual) {
    let scrut, tmp, tmp1, tmp2;
    scrut = sel === undefined;
    if (scrut === true) {
      tmp = "Access to required field '" + nme;
      tmp1 = tmp + "' yielded 'undefined'";
      throw runtime.safeCall(globalThis.Error(tmp1))
    }
    tmp2 = nme + "$__checkNotMethod";
    qual[tmp2];
    return sel;
  }
  static safeCall(x) {
    if (x === undefined) {
      return runtime.Unit
    }
    return x;
  }
  static checkCall(x) {
    if (x === undefined) {
      throw runtime.safeCall(globalThis.Error("MLscript call unexpectedly returned `undefined`, the forbidden value."))
    }
    return x;
  }
  static deboundMethod(mtdName, clsName) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = "[debinding error] Method '" + mtdName;
    tmp1 = tmp + "' of class '";
    tmp2 = tmp1 + clsName;
    tmp3 = tmp2 + "' was accessed without being called.";
    throw runtime.safeCall(globalThis.Error(tmp3))
  }
  static _try(f) {
    let res, scrut, tmp;
    res = runtime.safeCall(f());
    scrut = Runtime.curEffect !== null;
    if (scrut === true) {
      tmp = Runtime.curEffect;
      Runtime.curEffect = null;
      return Runtime.EffectHandle(tmp)
    }
    return res;
  }
  static printRaw(x) {
    let rcd, tmp;
    rcd = globalThis.Object.freeze({
      indent: 2,
      breakLength: 76
    });
    tmp = runtime.safeCall(Runtime.render(x, rcd));
    return runtime.safeCall(globalThis.console.log(tmp))
  }
  static makeNewContTrace() {
    let tmp;
    tmp = new Runtime.ContTrace.class(null, null, null, null, false);
    Runtime.curContTrace = tmp;
    Runtime.curContTrace.last = Runtime.curContTrace;
    Runtime.curContTrace.lastHandler = Runtime.curContTrace;
    return runtime.Unit
  }
  static resetEffects() {
    Runtime.curEffect = null;
    Runtime.resumePc = -1;
    return runtime.Unit
  }
  static raisePrintStackEffect(showLocals) {
    return Runtime.mkEffect(Runtime.PrintStackEffect, showLocals)
  }
  static topLevelTrampoline(limit, body) {
    let scrut, old, old1, old2, result, tmp, tmp1, tmp2, lambda$here, lambda$here1, lambda$here2;
    Runtime.makeNewContTrace();
    scrut = limit !== undefined;
    if (scrut === true) {
      Runtime.curEffect = null;
      old = Runtime.stackLimit;
      try {
        Runtime.stackLimit = limit;
        old1 = Runtime.stackDepth;
        try {
          Runtime.stackDepth = 1;
          old2 = Runtime.stackHandler;
          try {
            Runtime.stackHandler = Runtime.StackDelayHandler;
            lambda$here = lambda$4(Runtime, body);
            lambda$here1 = lambda$3(Runtime);
            result = runtime.safeCall(RuntimeJS.try_catch(lambda$here, lambda$here1));
            lbl: while (true) {
              let scrut1, saved, scrut2, tmp3, tmp4;
              scrut1 = Runtime.stackResume !== null;
              if (scrut1 === true) {
                saved = Runtime.stackResume;
                Runtime.stackResume = null;
                Runtime.stackDepth = 1;
                tmp3 = runtime.safeCall(RuntimeJS.try_catch(saved, Runtime.checkUnhandledErr));
                result = tmp3;
                scrut2 = Runtime.curEffect !== null;
                if (scrut2 === true) {
                  tmp4 = Runtime.handleEffects(Runtime.curEffect);
                  result = tmp4;
                  continue lbl
                }
                continue lbl;
              }
              break;
            }
            tmp2 = result;
          } finally {
            Runtime.stackHandler = old2;
          }
          tmp1 = tmp2;
        } finally {
          Runtime.stackDepth = old1;
        }
        tmp = tmp1;
      } finally {
        Runtime.stackLimit = old;
      }
      return tmp
    }
    lambda$here2 = lambda$2(Runtime);
    return runtime.safeCall(RuntimeJS.try_catch(body, lambda$here2));
  }
  static topLevelEffect(debug) {
    let tr, v, tmp, tmp1;
    tr = Runtime.curEffect;
    v = null;
    lbl: while (true) {
      let scrut, tmp2, tmp3;
      if (tr instanceof Runtime.EffectSig.class) {
        scrut = tr.handler === Runtime.PrintStackEffect;
        if (scrut === true) {
          tmp2 = Runtime.showStackTrace("Stack Trace:", tr, debug, tr.handlerFun);
          runtime.safeCall(globalThis.console.log(tmp2));
          Runtime.curEffect = null;
          tmp3 = Runtime.resume(tr.contTrace)(runtime.Unit);
          v = tmp3;
          tr = Runtime.curEffect;
          continue lbl
        }
      }
      break;
    }
    if (tr instanceof Runtime.EffectSig.class) {
      Runtime.curEffect = null;
      tmp = "Error: Unhandled effect " + tr.handler.constructor.name;
      tmp1 = Runtime.showStackTrace(tmp, tr, debug, false);
      throw Runtime.CustomStackError(tmp1)
    }
    return v;
  }
  static illegalEffect(position) {
    let tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = Runtime.curEffect;
    Runtime.curEffect = null;
    tmp1 = "Error: Effect " + tmp.handler.constructor.name;
    tmp2 = tmp1 + " is raised ";
    tmp3 = tmp2 + position;
    tmp4 = Runtime.showStackTrace(tmp3, tmp, false, false);
    throw Runtime.CustomStackError(tmp4)
  }
  static showStackTrace(header, tr, debug, showLocals) {
    let msg, curHandler, atTail;
    msg = header;
    curHandler = tr.contTrace;
    atTail = true;
    if (debug === true) {
      lbl: while (true) {
        let scrut, cur, scrut1, tmp, tmp1;
        scrut = curHandler !== null;
        if (scrut === true) {
          cur = curHandler.next;
          lbl1: while (true) {
            let scrut2, curLocals, loc, scrut3, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10;
            scrut2 = cur !== null;
            if (scrut2 === true) {
              curLocals = cur.getLocals;
              loc = cur.getLoc;
              if (showLocals === true) {
                scrut3 = curLocals.length > 0;
                if (scrut3 === true) {
                  tmp2 = runtime.safeCall(curLocals.map(lambda3));
                  tmp3 = runtime.safeCall(tmp2.join(", "));
                  tmp4 = " with locals: " + tmp3;
                } else {
                  tmp4 = "";
                }
              } else {
                tmp4 = "";
              }
              tmp5 = "\n\tat " + cur.getNme;
              tmp6 = tmp5 + " (";
              tmp7 = tmp6 + loc;
              tmp8 = tmp7 + ")";
              tmp9 = msg + tmp8;
              tmp10 = tmp9 + tmp4;
              msg = tmp10;
              cur = cur.next;
              atTail = false;
              continue lbl1
            }
            break;
          }
          curHandler = curHandler.nextHandler;
          scrut1 = curHandler !== null;
          if (scrut1 === true) {
            tmp = "\n\twith handler " + curHandler.handler.constructor.name;
            tmp1 = msg + tmp;
            msg = tmp1;
            atTail = false;
            continue lbl
          }
          continue lbl;
        }
        break;
      }
      if (atTail === true) {
        return msg + "\n\tat tail position"
      }
      return msg;
    }
    return header;
  }
  static showFunctionContChain(cont, hl, vis, reps) {
    let scrut, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, scope29$cap, lambda$here;
    scope29$cap = new Capture$scope291(undefined);
    if (cont instanceof Runtime.FunctionContFrame.class) {
      tmp = cont.constructor.name + "(";
      tmp1 = tmp + cont.fn.name;
      tmp2 = tmp1 + ", pc=";
      tmp3 = tmp2 + cont.varsClass.at(0);
      tmp4 = tmp3 + ", id=";
      scope29$cap.result$0 = tmp4 + cont.id;
      lambda$here = lambda$5(scope29$cap, cont);
      runtime.safeCall(hl.forEach(lambda$here));
      scrut = runtime.safeCall(vis.has(cont));
      if (scrut === true) {
        tmp5 = reps + 1;
        reps = tmp5;
        scrut1 = tmp5 > 10;
        if (scrut1 === true) {
          throw runtime.safeCall(globalThis.Error("10 repeated continuation frame (loop?)"))
        }
        tmp6 = scope29$cap.result$0 + ", REPEAT";
        scope29$cap.result$0 = tmp6;
      } else {
        runtime.safeCall(vis.add(cont));
      }
      tmp7 = scope29$cap.result$0 + ") -> ";
      tmp8 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
      return tmp7 + tmp8
    }
    scrut2 = cont === null;
    if (scrut2 === true) {
      return "(null)"
    }
    return "(NOT CONT)";
  }
  static showHandlerContChain(cont, hl, vis, reps) {
    let result, scrut, scrut1, scrut2, tmp, tmp1, tmp2, tmp3;
    if (cont instanceof Runtime.HandlerContFrame.class) {
      result = cont.handler.constructor.name;
      scrut = runtime.safeCall(vis.has(cont));
      if (scrut === true) {
        tmp = reps + 1;
        reps = tmp;
        scrut1 = tmp > 10;
        if (scrut1 === true) {
          throw runtime.safeCall(globalThis.Error("10 repeated continuation frame (loop?)"))
        }
        tmp1 = result + ", REPEAT";
        result = tmp1;
      } else {
        runtime.safeCall(vis.add(cont));
      }
      tmp2 = result + " -> ";
      tmp3 = Runtime.showFunctionContChain(cont.next, hl, vis, reps);
      return tmp2 + tmp3
    }
    scrut2 = cont === null;
    if (scrut2 === true) {
      return "(null)"
    }
    return "(NOT HANDLER CONT)";
  }
  static debugCont(cont) {
    let tmp, tmp1, tmp2;
    tmp = globalThis.Object.freeze(new globalThis.Map());
    tmp1 = globalThis.Object.freeze(new globalThis.Set());
    tmp2 = Runtime.showFunctionContChain(cont, tmp, tmp1, 0);
    return Runtime.myDebug(tmp2)
  }
  static debugHandler(cont) {
    let tmp, tmp1, tmp2;
    tmp = globalThis.Object.freeze(new globalThis.Map());
    tmp1 = globalThis.Object.freeze(new globalThis.Set());
    tmp2 = Runtime.showHandlerContChain(cont, tmp, tmp1, 0);
    return Runtime.myDebug(tmp2)
  }
  static debugContTrace(contTrace) {
    let scrut, scrut1, vis, hl, cur, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    if (contTrace instanceof Runtime.ContTrace.class) {
      runtime.safeCall(globalThis.console.log("resumed: ", contTrace.resumed));
      scrut = contTrace.last === contTrace;
      if (scrut === true) {
        runtime.safeCall(globalThis.console.log("<last is self>"));
      }
      scrut1 = contTrace.lastHandler === contTrace;
      if (scrut1 === true) {
        runtime.safeCall(globalThis.console.log("<lastHandler is self>"));
      }
      vis = globalThis.Object.freeze(new globalThis.Set());
      hl = globalThis.Object.freeze(new globalThis.Map());
      tmp = globalThis.Object.freeze([
        contTrace.last
      ]);
      tmp1 = globalThis.Object.freeze(new globalThis.Set(tmp));
      runtime.safeCall(hl.set("last", tmp1));
      tmp2 = globalThis.Object.freeze([
        contTrace.lastHandler
      ]);
      tmp3 = globalThis.Object.freeze(new globalThis.Set(tmp2));
      runtime.safeCall(hl.set("last-handler", tmp3));
      tmp4 = Runtime.showFunctionContChain(contTrace.next, hl, vis, 0);
      tmp5 = "ContTrace -> " + tmp4;
      runtime.safeCall(globalThis.console.log(tmp5));
      cur = contTrace.nextHandler;
      lbl: while (true) {
        let scrut2, tmp6;
        scrut2 = cur !== null;
        if (scrut2 === true) {
          runtime.safeCall(globalThis.console.log("v"));
          tmp6 = Runtime.showHandlerContChain(cur, hl, vis, 0);
          runtime.safeCall(globalThis.console.log(tmp6));
          cur = cur.nextHandler;
          continue lbl
        }
        break;
      }
      return runtime.safeCall(globalThis.console.log())
    }
    runtime.safeCall(globalThis.console.log("Not a cont trace:"));
    return runtime.safeCall(globalThis.console.log(contTrace));
  }
  static debugEff(eff) {
    if (eff instanceof Runtime.EffectSig.class) {
      runtime.safeCall(globalThis.console.log("Debug EffectSig:"));
      runtime.safeCall(globalThis.console.log("handler: ", eff.handler.constructor.name));
      runtime.safeCall(globalThis.console.log("handlerFun: ", eff.handlerFun));
      return Runtime.debugContTrace(eff.contTrace)
    }
    runtime.safeCall(globalThis.console.log("Not an effect:"));
    return runtime.safeCall(globalThis.console.log(eff));
  }
  static pushFrame(fn, vars) {
    let newFrame, scrut;
    newFrame = new Runtime.FunctionContFrame.class(Runtime.curContTrace.next, fn, vars);
    scrut = Runtime.curContTrace.last === Runtime.curContTrace;
    if (scrut === true) {
      Runtime.curContTrace.last = newFrame;
    }
    Runtime.curContTrace.next = newFrame;
    return runtime.Unit
  }
  static popFrame(id) {
    let scrut, scrut1;
    scrut = Runtime.curContTrace.next === null;
    if (scrut === true) {
      throw "INVALID CONT TRACE: next was null when popping " + id
    }
    scrut1 = Runtime.curContTrace.next === Runtime.curContTrace.last;
    if (scrut1 === true) {
      Runtime.curContTrace.last = Runtime.curContTrace;
    }
    Runtime.curContTrace.next = Runtime.curContTrace.next.next;
    return runtime.Unit;
  }
  static mkEffect(handler, handlerFun) {
    let res, tmp;
    res = new Runtime.EffectSig.class(Runtime.curContTrace, handler, handlerFun, Runtime.latestId);
    tmp = Runtime.latestId + 1;
    Runtime.latestId = tmp;
    Runtime.curEffect = res;
    Runtime.makeNewContTrace();
    throw Runtime.EffectRaised("mkEffect")
  }
  static popHandler(tr) {
    let scrut, scrut1;
    scrut = tr.lastHandler === tr.nextHandler;
    if (scrut === true) {
      tr.lastHandler = tr;
      scrut1 = tr.last === tr.nextHandler;
      if (scrut1 === true) {
        tr.last = tr;
      }
    }
    tr.next = tr.nextHandler.next;
    tr.nextHandler = tr.nextHandler.nextHandler;
    return runtime.Unit
  }
  static countFramesInTrace(tr) {
    let scope40$cap;
    scope40$cap = new Capture$scope401(undefined, undefined);
    scope40$cap.cnt$0 = 0;
    scope40$cap.curSegment$1 = tr;
    lbl: while (true) {
      let scrut, tmp;
      scrut = scope40$cap.curSegment$1.next !== null;
      if (scrut === true) {
        scope40$cap.curSegment$1 = scope40$cap.curSegment$1.next;
        tmp = scope40$cap.cnt$0 + 1;
        scope40$cap.cnt$0 = tmp;
        continue lbl
      }
      break;
    }
    lbl1: while (true) {
      let scrut, tmp;
      scrut = tr.nextHandler !== null;
      if (scrut === true) {
        tr = tr.nextHandler;
        scope40$cap.curSegment$1 = tr;
        lbl2: while (true) {
          let scrut1, tmp1;
          scrut1 = scope40$cap.curSegment$1.next !== null;
          if (scrut1 === true) {
            scope40$cap.curSegment$1 = scope40$cap.curSegment$1.next;
            tmp1 = scope40$cap.cnt$0 + 1;
            scope40$cap.cnt$0 = tmp1;
            continue lbl2
          }
          break;
        }
        tmp = scope40$cap.cnt$0 + 1;
        scope40$cap.cnt$0 = tmp;
        continue lbl1
      }
      break;
    }
    return scope40$cap.cnt$0
  }
  static validateContTrace(tr, loc) {
    let remainIter, realLastHandler, realLast, scrut, scrut1, scrut2;
    remainIter = 100000;
    realLastHandler = tr;
    lbl: while (true) {
      let scrut3, scrut4, tmp;
      scrut3 = remainIter >= 0;
      if (scrut3 === true) {
        scrut4 = realLastHandler.nextHandler !== null;
        if (scrut4 === true) {
          tmp = remainIter - 1;
          remainIter = tmp;
          realLastHandler = realLastHandler.nextHandler;
          continue lbl
        }
      }
      break;
    }
    realLast = realLastHandler;
    lbl1: while (true) {
      let scrut3, scrut4;
      scrut3 = remainIter >= 0;
      if (scrut3 === true) {
        scrut4 = realLast.next !== null;
        if (scrut4 === true) {
          realLast = realLast.next;
          continue lbl1
        }
      }
      break;
    }
    scrut = remainIter < 0;
    if (scrut === true) {
      errorSep(loc);
      throw "INVALID CONT TRACE: infinite loop"
    }
    scrut1 = realLast !== tr.last;
    if (scrut1 === true) {
      errorSep(loc);
      runtime.safeCall(globalThis.console.log("expected last:", realLast));
      runtime.safeCall(globalThis.console.dir(tr));
      throw "INVALID CONT TRACE: last is incorrect"
    }
    scrut2 = realLastHandler !== tr.lastHandler;
    if (scrut2 === true) {
      errorSep(loc);
      runtime.safeCall(globalThis.console.dir(tr));
      throw "INVALID CONT TRACE: lastHandler is incorrect"
    }
    return runtime.Unit;
  }
  static enterHandleBlock(handler, body) {
    let handlerFrame, scrut, scrut1, ret;
    handlerFrame = new Runtime.HandlerContFrame.class(Runtime.curContTrace.next, Runtime.curContTrace.nextHandler, handler);
    Runtime.curContTrace.nextHandler = handlerFrame;
    Runtime.curContTrace.next = null;
    scrut = Runtime.curContTrace.lastHandler === Runtime.curContTrace;
    if (scrut === true) {
      Runtime.curContTrace.lastHandler = handlerFrame;
    }
    scrut1 = Runtime.curContTrace.last === Runtime.curContTrace;
    if (scrut1 === true) {
      Runtime.curContTrace.last = handlerFrame;
    }
    ret = runtime.safeCall(body());
    Runtime.popHandler(Runtime.curContTrace);
    return ret
  }
  static myDebug(arg) {
    let tmp;
    if (true === true) {
      tmp = globalThis.Object.freeze({
        depth: 10
      });
      return runtime.safeCall(globalThis.console.dir(arg, tmp))
    }
    return runtime.Unit;
  }
  static handleEffects(cur) {
    let tmp;
    tmp = Runtime.handleEffectsCall + 1;
    Runtime.handleEffectsCall = tmp;
    lbl: while (true) {
      let nxt, scrut;
      if (cur instanceof Runtime.EffectSig.class) {
        nxt = Runtime.handleEffect(cur);
        scrut = cur === nxt;
        if (scrut === true) {
          Runtime.curEffect = cur;
          throw Runtime.EffectRaised("handleEffects")
        }
        cur = nxt;
        continue lbl;
      }
      return cur;
    }
  }
  static checkUnhandledErr(err) {
    let scrut;
    scrut = Runtime.curEffect === null;
    if (scrut === true) {
      throw err
    }
    return runtime.Unit;
  }
  static concatTraces(bottom, top) {
    let scrut, scrut1, scrut2, scrut3;
    scrut = bottom.next !== null;
    if (scrut === true) {
      top.last.next = bottom.next;
    }
    scrut1 = bottom.last !== bottom;
    if (scrut1 === true) {
      top.last = bottom.last;
    }
    scrut2 = bottom.nextHandler !== null;
    if (scrut2 === true) {
      top.lastHandler.nextHandler = bottom.nextHandler;
    }
    scrut3 = bottom.lastHandler !== bottom;
    if (scrut3 === true) {
      top.lastHandler = bottom.lastHandler;
      return runtime.Unit
    }
    return runtime.Unit;
  }
  static handleEffect(cur) {
    let prevHandlerFrame, scrut, handlerFrame, saved, scrut1, scrut2, old, scrut3, retVal, scrut4, tmp, tmp1, tmp2, handleEffect$cap, lambda$here, lambda$here1;
    handleEffect$cap = new Capture$handleEffect1(cur);
    prevHandlerFrame = handleEffect$cap.cur$0.contTrace;
    lbl: while (true) {
      let scrut5, scrut6;
      scrut5 = prevHandlerFrame.nextHandler !== null;
      if (scrut5 === true) {
        scrut6 = prevHandlerFrame.nextHandler.handler !== handleEffect$cap.cur$0.handler;
        if (scrut6 === true) {
          prevHandlerFrame = prevHandlerFrame.nextHandler;
          continue lbl
        }
      }
      break;
    }
    scrut = prevHandlerFrame.nextHandler === null;
    if (scrut === true) {
      return handleEffect$cap.cur$0
    }
    handlerFrame = prevHandlerFrame.nextHandler;
    saved = new Runtime.ContTrace.class(handlerFrame.next, handleEffect$cap.cur$0.contTrace.last, handlerFrame.nextHandler, handleEffect$cap.cur$0.contTrace.lastHandler, false);
    scrut1 = handleEffect$cap.cur$0.contTrace.last === handlerFrame;
    if (scrut1 === true) {
      saved.last = saved;
    }
    scrut2 = handleEffect$cap.cur$0.contTrace.lastHandler === handlerFrame;
    if (scrut2 === true) {
      saved.lastHandler = saved;
    }
    handleEffect$cap.cur$0.contTrace.last = handlerFrame;
    handleEffect$cap.cur$0.contTrace.lastHandler = handlerFrame;
    handlerFrame.next = null;
    handlerFrame.nextHandler = null;
    Runtime.curEffect = null;
    old = Runtime.stackDepth;
    try {
      tmp1 = Runtime.stackDepth + 2;
      Runtime.stackDepth = tmp1;
      lambda$here = lambda$7(handleEffect$cap, Runtime);
      tmp2 = runtime.safeCall(RuntimeJS.try_catch(lambda$here, Runtime.checkUnhandledErr));
      tmp = tmp2;
    } finally {
      Runtime.stackDepth = old;
    }
    scrut3 = Runtime.curEffect !== null;
    if (scrut3 === true) {
      handleEffect$cap.cur$0 = Runtime.curEffect;
      Runtime.concatTraces(saved, handleEffect$cap.cur$0.contTrace);
      return handleEffect$cap.cur$0
    }
    lambda$here1 = lambda$6(Runtime, saved, tmp);
    retVal = runtime.safeCall(RuntimeJS.try_catch(lambda$here1, Runtime.checkUnhandledErr));
    scrut4 = Runtime.curEffect !== null;
    if (scrut4 === true) {
      return Runtime.curEffect
    }
    return retVal;
  }
  static resume(contTrace) {
    return (value) => {
      let scrut;
      scrut = contTrace.resumed;
      if (scrut === true) {
        throw runtime.safeCall(globalThis.Error("Multiple resumption"))
      }
      contTrace.resumed = true;
      return Runtime.resumeContTrace(contTrace, value);
    }
  }
  static resumeContTrace(contTrace, value) {
    let savedResumeFrames, resumeContTrace$cap;
    resumeContTrace$cap = new Capture$resumeContTrace1(value);
    savedResumeFrames = Runtime.curContTrace;
    Runtime.curContTrace = contTrace;
    lbl: while (true) {
      let scrut, curFrame, old, scrut1, scrut2, tmp, tmp1, tmp2, lambda$here, lambda$here1;
      scrut = contTrace.next;
      if (scrut instanceof Runtime.FunctionContFrame.class) {
        curFrame = contTrace.next;
        Runtime.curEffect = null;
        old = Runtime.stackDepth;
        try {
          tmp1 = Runtime.stackDepth + 3;
          Runtime.stackDepth = tmp1;
          lambda$here = lambda$9(resumeContTrace$cap, curFrame);
          lambda$here1 = lambda$8(Runtime);
          tmp2 = runtime.safeCall(RuntimeJS.try_catch(lambda$here, lambda$here1));
          tmp = tmp2;
        } finally {
          Runtime.stackDepth = old;
        }
        resumeContTrace$cap.value$0 = tmp;
        scrut1 = Runtime.curEffect !== null;
        if (scrut1 === true) {
          resumeContTrace$cap.value$0 = Runtime.curEffect;
        }
        if (resumeContTrace$cap.value$0 instanceof Runtime.EffectSig.class) {
          contTrace = Runtime.curEffect.contTrace;
          contTrace.resumed = false;
          contTrace.last.next = savedResumeFrames.next;
          contTrace.lastHandler.nextHandler = savedResumeFrames.nextHandler;
          Runtime.concatTraces(savedResumeFrames, contTrace);
          throw Runtime.EffectRaised("resumeContTrace")
        }
        continue lbl;
      }
      scrut2 = contTrace.nextHandler;
      if (scrut2 instanceof Runtime.HandlerContFrame.class) {
        Runtime.popHandler(contTrace);
        continue lbl
      }
      Runtime.curContTrace = savedResumeFrames;
      return resumeContTrace$cap.value$0;
    }
  }
  static checkDepth() {
    let tmp, tmp1;
    tmp = Runtime.stackDepth >= Runtime.stackLimit;
    if (tmp === true) {
      tmp1 = Runtime.stackHandler !== null;
      if (tmp1 === true) {
        return runtime.safeCall(Runtime.stackHandler.delay())
      }
      return runtime.Unit;
    }
    return runtime.Unit;
  }
  static runStackSafe(limit, f) {
    let old, old1, old2, result, scrut, tmp, tmp1, tmp2;
    old = Runtime.stackLimit;
    try {
      Runtime.stackLimit = limit;
      old1 = Runtime.stackDepth;
      try {
        Runtime.stackDepth = 1;
        old2 = Runtime.stackHandler;
        try {
          Runtime.stackHandler = Runtime.StackDelayHandler;
          result = Runtime.enterHandleBlock(Runtime.StackDelayHandler, f);
          scrut = Runtime.curEffect !== null;
          if (scrut === true) {
            throw globalThis.Object.freeze(new globalThis.Error("Effect crossed through stack safe boundary"))
          }
          lbl: while (true) {
            let scrut1, saved, scrut2, tmp3;
            scrut1 = Runtime.stackResume !== null;
            if (scrut1 === true) {
              saved = Runtime.stackResume;
              Runtime.stackResume = null;
              Runtime.stackDepth = 1;
              tmp3 = runtime.safeCall(saved(runtime.Unit));
              result = tmp3;
              scrut2 = Runtime.curEffect !== null;
              if (scrut2 === true) {
                throw globalThis.Object.freeze(new globalThis.Error("Effect crossed through stack safe boundary"))
              }
              continue lbl;
            }
            break;
          }
          tmp2 = result;
        } finally {
          Runtime.stackHandler = old2;
        }
        tmp1 = tmp2;
      } finally {
        Runtime.stackDepth = old1;
      }
      tmp = tmp1;
    } finally {
      Runtime.stackLimit = old;
    }
    return tmp
  }
  static plus_impl(lhs, rhs) {
    if (lhs instanceof Runtime.Int31.class) {
      if (rhs instanceof Runtime.Int31.class) {
        return lhs + rhs
      }
      return Runtime.unreachable;
    }
    return Runtime.unreachable;
  }
  toString() { return runtime.render(this); }
  static [definitionMetadata] = ["class", "Runtime"];
});
export { cntSegment as _$_modulePrivate_$_cntSegment };
export { errorSep as _$_modulePrivate_$_errorSep };
export { Runtime1 as _$_modulePrivate_$_Runtime };
export { lambda as _$_modulePrivate_$_lambda };
export { lambda1 as _$_modulePrivate_$_lambda1 };
export { lambda2 as _$_modulePrivate_$_lambda2 };
export { lambda3 as _$_modulePrivate_$_lambda3 };
export { lambda4 as _$_modulePrivate_$_lambda4 };
export { lambda5 as _$_modulePrivate_$_lambda5 };
export { lambda6 as _$_modulePrivate_$_lambda6 };
export { lambda7 as _$_modulePrivate_$_lambda7 };
export { lambda8 as _$_modulePrivate_$_lambda8 };
export { lambda9 as _$_modulePrivate_$_lambda9 };
export { lambda10 as _$_modulePrivate_$_lambda10 };
export { lambda$ as _$_modulePrivate_$_lambda$ };
export { lambda$1 as _$_modulePrivate_$_lambda$1 };
export { lambda$2 as _$_modulePrivate_$_lambda$2 };
export { lambda$3 as _$_modulePrivate_$_lambda$3 };
export { lambda$4 as _$_modulePrivate_$_lambda$4 };
export { Capture$scope291 as _$_modulePrivate_$_Capture$scope29 };
export { lambda$5 as _$_modulePrivate_$_lambda$5 };
export { Capture$scope401 as _$_modulePrivate_$_Capture$scope40 };
export { Capture$handleEffect1 as _$_modulePrivate_$_Capture$handleEffect };
export { lambda$6 as _$_modulePrivate_$_lambda$6 };
export { lambda$7 as _$_modulePrivate_$_lambda$7 };
export { Capture$resumeContTrace1 as _$_modulePrivate_$_Capture$resumeContTrace };
export { lambda$8 as _$_modulePrivate_$_lambda$8 };
export { lambda$9 as _$_modulePrivate_$_lambda$9 };
let Runtime = Runtime1; export default Runtime;
