import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import Runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import Predef from "./../../../hkmc2/shared/src/test/mlscript-compile/Predef.mjs";
import NofibPrelude from "./NofibPrelude.mjs";
import benchmark from "benchmark";
let BenchmarkPrelude1, b, lambda, Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$1, Cont$func$lambda$$1, Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$1, Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$$ctor, Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$$, lambda$, Cont$func$lambda$$$ctor, Cont$func$lambda$$$, Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$$ctor, Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$$;
b = benchmark;
Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$$ = function Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$$(fn$0, suite$1, settings$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, curDepth$9, stackDelayRes$10, pc) {
  let tmp;
  tmp = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$1.class(pc);
  return tmp(fn$0, suite$1, settings$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, curDepth$9, stackDelayRes$10)
};
Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$$ctor = function Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$$ctor(fn$0, suite$1, settings$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, curDepth$9, stackDelayRes$10) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$1.class(pc);
    return tmp(fn$0, suite$1, settings$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, curDepth$9, stackDelayRes$10)
  }
};
Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$1 = function Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$(pc1) {
  return (fn$01, suite$11, settings$21, tmp$31, tmp$41, tmp$51, tmp$61, tmp$71, tmp$81, curDepth$91, stackDelayRes$101) => {
    return new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$.class(pc1)(fn$01, suite$11, settings$21, tmp$31, tmp$41, tmp$51, tmp$61, tmp$71, tmp$81, curDepth$91, stackDelayRes$101);
  }
};
Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$1.class = class Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (fn$0, suite$1, settings$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, curDepth$9, stackDelayRes$10) => {
      let tmp;
      tmp = super(null);
      this.fn$0 = fn$0;
      this.suite$1 = suite$1;
      this.settings$2 = settings$2;
      this.tmp$3 = tmp$3;
      this.tmp$4 = tmp$4;
      this.tmp$5 = tmp$5;
      this.tmp$6 = tmp$6;
      this.tmp$7 = tmp$7;
      this.tmp$8 = tmp$8;
      this.curDepth$9 = curDepth$9;
      this.stackDelayRes$10 = stackDelayRes$10;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    let lambda$this;
    if (this.pc === 3) {
      this.stackDelayRes$10 = value$;
    } else if (this.pc === 4) {
      this.tmp$3 = value$;
    } else if (this.pc === 7) {
      this.tmp$4 = value$;
    } else if (this.pc === 8) {
      this.tmp$5 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 3) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = new b.Suite();
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 4;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 4;
        continue contLoop;
      } else if (this.pc === 4) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$9);
        this.suite$1 = this.tmp$3;
        this.pc = 11;
        continue contLoop;
      } else if (this.pc === 11) {
        runtime.stackDepth = runtime.stackDepth + 1;
        lambda$this = runtime.safeCall(lambda(this.fn$0));
        this.tmp$4 = this.suite$1.add("main", lambda$this);
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 7;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 7;
        continue contLoop;
      } else if (this.pc === 7) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$9);
        this.settings$2 = runtime.Unit;
        this.settings$2.async = false;
        this.pc = 10;
        continue contLoop;
      } else if (this.pc === 10) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = runtime.safeCall(this.suite$1.run(this.settings$2));
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 8;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 8;
        continue contLoop;
      } else if (this.pc === 8) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$9);
        this.tmp$6 = this.suite$1[0].stats.mean * 1000;
        this.tmp$7 = "Time: " + this.tmp$6;
        this.tmp$8 = this.tmp$7 + "ms";
        this.pc = 9;
        continue contLoop;
      } else if (this.pc === 9) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Predef.print(this.tmp$8)
      }
      break;
    }
  }
  toString() { return "Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$ = function Cont$func$lambda$$$(fn$0, stackDelayRes$1, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$1.class(pc);
  return tmp(fn$0, stackDelayRes$1)
};
Cont$func$lambda$$$ctor = function Cont$func$lambda$$$ctor(fn$0, stackDelayRes$1) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$1.class(pc);
    return tmp(fn$0, stackDelayRes$1)
  }
};
Cont$func$lambda$$1 = function Cont$func$lambda$$(pc1) {
  return (fn$01, stackDelayRes$11) => {
    return new Cont$func$lambda$$.class(pc1)(fn$01, stackDelayRes$11);
  }
};
Cont$func$lambda$$1.class = class Cont$func$lambda$$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (fn$0, stackDelayRes$1) => {
      let tmp;
      tmp = super(null);
      this.fn$0 = fn$0;
      this.stackDelayRes$1 = stackDelayRes$1;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 5) {
      this.stackDelayRes$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 5) {
        this.pc = 6;
        continue contLoop;
      } else if (this.pc === 6) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return BenchmarkPrelude1.helper(this.fn$0)
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda$ = function lambda$(fn) {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$(fn, stackDelayRes, 5);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return BenchmarkPrelude1.helper(fn)
};
lambda = (undefined, function (fn) {
  return () => {
    return lambda$(fn)
  }
});
Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$$ = function Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$$(f$0, tmp$1, curDepth$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$1.class(pc);
  return tmp(f$0, tmp$1, curDepth$2, stackDelayRes$3)
};
Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$$ctor = function Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$$ctor(f$0, tmp$1, curDepth$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$1.class(pc);
    return tmp(f$0, tmp$1, curDepth$2, stackDelayRes$3)
  }
};
Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$1 = function Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$(pc1) {
  return (f$01, tmp$11, curDepth$21, stackDelayRes$31) => {
    return new Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$.class(pc1)(f$01, tmp$11, curDepth$21, stackDelayRes$31);
  }
};
Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$1.class = class Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, tmp$1, curDepth$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.f$0 = f$0;
      this.tmp$1 = tmp$1;
      this.curDepth$2 = curDepth$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 0) {
      this.stackDelayRes$3 = value$;
    } else if (this.pc === 1) {
      this.tmp$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 0) {
        this.pc = 2;
        continue contLoop;
      } else if (this.pc === 2) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = Runtime.runStackSafe(2000, this.f$0);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 1;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 1;
        continue contLoop;
      } else if (this.pc === 1) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$2);
        return true
      }
      break;
    }
  }
  toString() { return "Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$(" + globalThis.Predef.render(this.pc) + ")"; }
};
BenchmarkPrelude1 = class BenchmarkPrelude {
  static {
    BenchmarkPrelude1 = BenchmarkPrelude;
    globalThis.Predef = Predef;
    runtime.Unit
  }
  static not(x) {
    return x === false
  } 
  static print(s) {
    return s
  } 
  static helper(f) {
    let tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$$(f, tmp, curDepth, stackDelayRes, 0);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = Runtime.runStackSafe(2000, f);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$helper$BenchmarkPrelude$_mls_L0_316_359$$(f, tmp, curDepth, stackDelayRes, 1);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    return true
  } 
  static benchmark(fn) {
    let suite, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, lambda$this;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$$(fn, suite, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 3);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = new b.Suite();
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$$(fn, suite, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 4);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    suite = tmp;
    runtime.stackDepth = runtime.stackDepth + 1;
    lambda$this = runtime.safeCall(lambda(fn));
    tmp1 = suite.add("main", lambda$this);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$$(fn, suite, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 7);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    settings = runtime.Unit;
    settings.async = false;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = runtime.safeCall(suite.run(settings));
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$benchmark$BenchmarkPrelude$_mls_L0_372_637$$(fn, suite, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 8);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    tmp3 = suite[0].stats.mean * 1000;
    tmp4 = "Time: " + tmp3;
    tmp5 = tmp4 + "ms";
    runtime.stackDepth = runtime.stackDepth + 1;
    return Predef.print(tmp5)
  }
  static toString() { return "BenchmarkPrelude"; }
};
let BenchmarkPrelude = BenchmarkPrelude1; export default BenchmarkPrelude;
