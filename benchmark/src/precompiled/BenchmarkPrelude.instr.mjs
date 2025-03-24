import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import Runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import Predef from "./../../../hkmc2/shared/src/test/mlscript-compile/Predef.mjs";
import NofibPrelude from "./NofibPrelude.mjs";
import benchmark from "benchmark";
let BenchmarkPrelude1, b, Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$1, Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$1, Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$1, Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$$ctor, Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$$, Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$$ctor, Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$$, Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$$ctor, Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$$;
b = benchmark;
Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$$ = function Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$$(fn$0, start$1, res$2, end$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11, pc) {
  let tmp;
  tmp = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$1.class(pc);
  return tmp(fn$0, start$1, res$2, end$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11)
};
Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$$ctor = function Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$$ctor(fn$0, start$1, res$2, end$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$1.class(pc);
    return tmp(fn$0, start$1, res$2, end$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11)
  }
};
Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$1 = function Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$(pc1) {
  return (fn$01, start$11, res$21, end$31, tmp$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, curDepth$101, stackDelayRes$111) => {
    return new Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$.class(pc1)(fn$01, start$11, res$21, end$31, tmp$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, curDepth$101, stackDelayRes$111);
  }
};
Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$1.class = class Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (fn$0, start$1, res$2, end$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11) => {
      let tmp;
      tmp = super(null);
      this.fn$0 = fn$0;
      this.start$1 = start$1;
      this.res$2 = res$2;
      this.end$3 = end$3;
      this.tmp$4 = tmp$4;
      this.tmp$5 = tmp$5;
      this.tmp$6 = tmp$6;
      this.tmp$7 = tmp$7;
      this.tmp$8 = tmp$8;
      this.tmp$9 = tmp$9;
      this.curDepth$10 = curDepth$10;
      this.stackDelayRes$11 = stackDelayRes$11;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 5) {
      this.stackDelayRes$11 = value$;
    } else if (this.pc === 6) {
      this.tmp$4 = value$;
    } else if (this.pc === 7) {
      this.tmp$5 = value$;
    } else if (this.pc === 8) {
      this.tmp$6 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 5) {
        this.pc = 12;
        continue contLoop;
      } else if (this.pc === 12) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$4 = runtime.safeCall(globalThis.performance.now());
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 6;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 6;
        continue contLoop;
      } else if (this.pc === 6) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$10);
        this.start$1 = this.tmp$4;
        this.pc = 11;
        continue contLoop;
      } else if (this.pc === 11) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = BenchmarkPrelude1.helper(this.fn$0);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 7;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 7;
        continue contLoop;
      } else if (this.pc === 7) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$10);
        this.res$2 = this.tmp$5;
        this.pc = 10;
        continue contLoop;
      } else if (this.pc === 10) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = runtime.safeCall(globalThis.performance.now());
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 8;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 8;
        continue contLoop;
      } else if (this.pc === 8) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$10);
        this.end$3 = this.tmp$6;
        this.tmp$7 = this.end$3 - this.start$1;
        this.tmp$8 = "Time: " + this.tmp$7;
        this.tmp$9 = this.tmp$8 + "ms";
        this.pc = 9;
        continue contLoop;
      } else if (this.pc === 9) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return BenchmarkPrelude1.print(this.tmp$9)
      }
      break;
    }
  }
  toString() { return "Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$$ = function Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$$(f$0, tmp$1, curDepth$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$1.class(pc);
  return tmp(f$0, tmp$1, curDepth$2, stackDelayRes$3)
};
Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$$ctor = function Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$$ctor(f$0, tmp$1, curDepth$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$1.class(pc);
    return tmp(f$0, tmp$1, curDepth$2, stackDelayRes$3)
  }
};
Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$1 = function Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$(pc1) {
  return (f$01, tmp$11, curDepth$21, stackDelayRes$31) => {
    return new Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$.class(pc1)(f$01, tmp$11, curDepth$21, stackDelayRes$31);
  }
};
Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$1.class = class Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$ extends runtime.FunctionContFrame.class {
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
    if (this.pc === 2) {
      this.stackDelayRes$3 = value$;
    } else if (this.pc === 3) {
      this.tmp$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 2) {
        this.pc = 4;
        continue contLoop;
      } else if (this.pc === 4) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = Runtime.runStackSafe(2000, this.f$0);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 3;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 3;
        continue contLoop;
      } else if (this.pc === 3) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$2);
        return true
      }
      break;
    }
  }
  toString() { return "Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$$ = function Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$$(s$0, stackDelayRes$1, pc) {
  let tmp;
  tmp = new Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$1.class(pc);
  return tmp(s$0, stackDelayRes$1)
};
Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$$ctor = function Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$$ctor(s$0, stackDelayRes$1) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$1.class(pc);
    return tmp(s$0, stackDelayRes$1)
  }
};
Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$1 = function Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$(pc1) {
  return (s$01, stackDelayRes$11) => {
    return new Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$.class(pc1)(s$01, stackDelayRes$11);
  }
};
Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$1.class = class Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (s$0, stackDelayRes$1) => {
      let tmp;
      tmp = super(null);
      this.s$0 = s$0;
      this.stackDelayRes$1 = stackDelayRes$1;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 0) {
      this.stackDelayRes$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 0) {
        this.pc = 1;
        continue contLoop;
      } else if (this.pc === 1) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Predef.print(this.s$0)
      }
      break;
    }
  }
  toString() { return "Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$(" + globalThis.Predef.render(this.pc) + ")"; }
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
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$print$BenchmarkPrelude$_mls_L0_298_324$$(s, stackDelayRes, 0);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return Predef.print(s)
  } 
  static helper(f) {
    let tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$$(f, tmp, curDepth, stackDelayRes, 2);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = Runtime.runStackSafe(2000, f);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$helper$BenchmarkPrelude$_mls_L0_330_373$$(f, tmp, curDepth, stackDelayRes, 3);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    return true
  } 
  static benchmark(fn) {
    let start, res, end, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$$(fn, start, res, end, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 5);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = runtime.safeCall(globalThis.performance.now());
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$$(fn, start, res, end, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 6);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    start = tmp;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = BenchmarkPrelude.helper(fn);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$$(fn, start, res, end, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 7);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    res = tmp1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = runtime.safeCall(globalThis.performance.now());
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$benchmark$BenchmarkPrelude$_mls_L0_386_806$$(fn, start, res, end, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 8);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    end = tmp2;
    tmp3 = end - start;
    tmp4 = "Time: " + tmp3;
    tmp5 = tmp4 + "ms";
    runtime.stackDepth = runtime.stackDepth + 1;
    return BenchmarkPrelude.print(tmp5)
  }
  static toString() { return "BenchmarkPrelude"; }
};
let BenchmarkPrelude = BenchmarkPrelude1; export default BenchmarkPrelude;
