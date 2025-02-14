import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import Predef from "./../../../hkmc2/shared/src/test/mlscript-compile/Predef.mjs";
import Stack from "./../../../hkmc2/shared/src/test/mlscript-compile/Stack.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
import benchmark from "benchmark";
let map, main, fill, toString, sum, do_benchmark, lambda, lambda1, lambda2, lambda3, res, Cont$func$sum$StackSafety$_mls_L0_296_343$1, Cont$func$fill$StackSafety$_mls_L0_349_417$1, Cont$func$map$StackSafety$_mls_L0_423_504$1, Cont$func$toString$StackSafety$_mls_L0_510_749$1, Cont$func$main$StackSafety$_mls_L0_755_799$1, Cont$func$lambda$$4, Cont$func$lambda$$5, Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$1, Cont$func$lambda$$6, Cont$func$lambda$$7, handleBlock$, Cont$handleBlock$stackHandler$1, StackDelay$1, lambda4, Cont$func$sum$StackSafety$_mls_L0_296_343$$ctor, Cont$func$sum$StackSafety$_mls_L0_296_343$$, Cont$func$fill$StackSafety$_mls_L0_349_417$$ctor, Cont$func$fill$StackSafety$_mls_L0_349_417$$, Cont$func$map$StackSafety$_mls_L0_423_504$$ctor, Cont$func$map$StackSafety$_mls_L0_423_504$$, Cont$func$toString$StackSafety$_mls_L0_510_749$$ctor, Cont$func$toString$StackSafety$_mls_L0_510_749$$, Cont$func$main$StackSafety$_mls_L0_755_799$$ctor, Cont$func$main$StackSafety$_mls_L0_755_799$$, lambda$, Cont$func$lambda$$$ctor, Cont$func$lambda$$$, lambda$1, Cont$func$lambda$$$ctor1, Cont$func$lambda$$$1, Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$ctor, Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$, lambda$2, Cont$func$lambda$$$ctor2, Cont$func$lambda$$$2, Cont$func$lambda$$$ctor3, Cont$func$lambda$$$3, Cont$handleBlock$stackHandler$$ctor, Cont$handleBlock$stackHandler$$, lambda$3;
Cont$func$sum$StackSafety$_mls_L0_296_343$$ = function Cont$func$sum$StackSafety$_mls_L0_296_343$$(n$0, scrut$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5, pc) {
  let tmp;
  tmp = new Cont$func$sum$StackSafety$_mls_L0_296_343$1.class(pc);
  return tmp(n$0, scrut$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5)
};
Cont$func$sum$StackSafety$_mls_L0_296_343$$ctor = function Cont$func$sum$StackSafety$_mls_L0_296_343$$ctor(n$0, scrut$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$sum$StackSafety$_mls_L0_296_343$1.class(pc);
    return tmp(n$0, scrut$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5)
  }
};
Cont$func$sum$StackSafety$_mls_L0_296_343$1 = function Cont$func$sum$StackSafety$_mls_L0_296_343$(pc1) {
  return (n$01, scrut$11, tmp$21, tmp$31, curDepth$41, stackDelayRes$51) => {
    return new Cont$func$sum$StackSafety$_mls_L0_296_343$.class(pc1)(n$01, scrut$11, tmp$21, tmp$31, curDepth$41, stackDelayRes$51);
  }
};
Cont$func$sum$StackSafety$_mls_L0_296_343$1.class = class Cont$func$sum$StackSafety$_mls_L0_296_343$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (n$0, scrut$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.n$0 = n$0;
      this.scrut$1 = scrut$1;
      this.tmp$2 = tmp$2;
      this.tmp$3 = tmp$3;
      this.curDepth$4 = curDepth$4;
      this.stackDelayRes$5 = stackDelayRes$5;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 0) {
      this.stackDelayRes$5 = value$;
    } else if (this.pc === 1) {
      this.tmp$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 0) {
        this.scrut$1 = this.n$0 == 0;
        if (this.scrut$1 === true) {
          return 0
        } else {
          this.tmp$2 = this.n$0 - 1;
          this.pc = 3;
          continue contLoop;
        }
        this.pc = 2;
        continue contLoop;
      } else if (this.pc === 2) {
        break contLoop;
      } else if (this.pc === 3) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = sum(this.tmp$2);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 1;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 1;
        continue contLoop;
      } else if (this.pc === 1) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$4);
        return this.n$0 + this.tmp$3
      }
      break;
    }
  }
  toString() { return "Cont$func$sum$StackSafety$_mls_L0_296_343$(" + globalThis.Predef.render(this.pc) + ")"; }
};
sum = function sum(n) {
  let scrut, tmp, tmp1, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$sum$StackSafety$_mls_L0_296_343$$(n, scrut, tmp, tmp1, curDepth, stackDelayRes, 0);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  scrut = n == 0;
  if (scrut === true) {
    return 0
  } else {
    tmp = n - 1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = sum(tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$sum$StackSafety$_mls_L0_296_343$$(n, scrut, tmp, tmp1, curDepth, stackDelayRes, 1);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    return n + tmp1
  }
};
Cont$func$fill$StackSafety$_mls_L0_349_417$$ = function Cont$func$fill$StackSafety$_mls_L0_349_417$$(n$0, x$1, scrut$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6, pc) {
  let tmp;
  tmp = new Cont$func$fill$StackSafety$_mls_L0_349_417$1.class(pc);
  return tmp(n$0, x$1, scrut$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6)
};
Cont$func$fill$StackSafety$_mls_L0_349_417$$ctor = function Cont$func$fill$StackSafety$_mls_L0_349_417$$ctor(n$0, x$1, scrut$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$fill$StackSafety$_mls_L0_349_417$1.class(pc);
    return tmp(n$0, x$1, scrut$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6)
  }
};
Cont$func$fill$StackSafety$_mls_L0_349_417$1 = function Cont$func$fill$StackSafety$_mls_L0_349_417$(pc1) {
  return (n$01, x$11, scrut$21, tmp$31, tmp$41, curDepth$51, stackDelayRes$61) => {
    return new Cont$func$fill$StackSafety$_mls_L0_349_417$.class(pc1)(n$01, x$11, scrut$21, tmp$31, tmp$41, curDepth$51, stackDelayRes$61);
  }
};
Cont$func$fill$StackSafety$_mls_L0_349_417$1.class = class Cont$func$fill$StackSafety$_mls_L0_349_417$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (n$0, x$1, scrut$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.n$0 = n$0;
      this.x$1 = x$1;
      this.scrut$2 = scrut$2;
      this.tmp$3 = tmp$3;
      this.tmp$4 = tmp$4;
      this.curDepth$5 = curDepth$5;
      this.stackDelayRes$6 = stackDelayRes$6;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 4) {
      this.stackDelayRes$6 = value$;
    } else if (this.pc === 5) {
      this.tmp$4 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 4) {
        this.scrut$2 = this.n$0 == 0;
        if (this.scrut$2 === true) {
          return Stack.Nil
        } else {
          this.tmp$3 = this.n$0 - 1;
          this.pc = 8;
          continue contLoop;
        }
        this.pc = 6;
        continue contLoop;
      } else if (this.pc === 6) {
        break contLoop;
      } else if (this.pc === 7) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Stack.Cons(this.x$1, this.tmp$4)
      } else if (this.pc === 8) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$4 = fill(this.tmp$3, this.x$1);
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 5;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 5;
        continue contLoop;
      } else if (this.pc === 5) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$5);
        this.pc = 7;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$fill$StackSafety$_mls_L0_349_417$(" + globalThis.Predef.render(this.pc) + ")"; }
};
fill = function fill(n, x) {
  let scrut, tmp, tmp1, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$fill$StackSafety$_mls_L0_349_417$$(n, x, scrut, tmp, tmp1, curDepth, stackDelayRes, 4);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  scrut = n == 0;
  if (scrut === true) {
    return Stack.Nil
  } else {
    tmp = n - 1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = fill(tmp, x);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$fill$StackSafety$_mls_L0_349_417$$(n, x, scrut, tmp, tmp1, curDepth, stackDelayRes, 5);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return Stack.Cons(x, tmp1)
  }
};
Cont$func$map$StackSafety$_mls_L0_423_504$$ = function Cont$func$map$StackSafety$_mls_L0_423_504$$(list$0, fn$1, param0$2, param1$3, h$4, t$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10, pc) {
  let tmp;
  tmp = new Cont$func$map$StackSafety$_mls_L0_423_504$1.class(pc);
  return tmp(list$0, fn$1, param0$2, param1$3, h$4, t$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
};
Cont$func$map$StackSafety$_mls_L0_423_504$$ctor = function Cont$func$map$StackSafety$_mls_L0_423_504$$ctor(list$0, fn$1, param0$2, param1$3, h$4, t$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$map$StackSafety$_mls_L0_423_504$1.class(pc);
    return tmp(list$0, fn$1, param0$2, param1$3, h$4, t$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
  }
};
Cont$func$map$StackSafety$_mls_L0_423_504$1 = function Cont$func$map$StackSafety$_mls_L0_423_504$(pc1) {
  return (list$01, fn$11, param0$21, param1$31, h$41, t$51, tmp$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101) => {
    return new Cont$func$map$StackSafety$_mls_L0_423_504$.class(pc1)(list$01, fn$11, param0$21, param1$31, h$41, t$51, tmp$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101);
  }
};
Cont$func$map$StackSafety$_mls_L0_423_504$1.class = class Cont$func$map$StackSafety$_mls_L0_423_504$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (list$0, fn$1, param0$2, param1$3, h$4, t$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.list$0 = list$0;
      this.fn$1 = fn$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.h$4 = h$4;
      this.t$5 = t$5;
      this.tmp$6 = tmp$6;
      this.tmp$7 = tmp$7;
      this.curDepth$8 = curDepth$8;
      this.tmp$9 = tmp$9;
      this.stackDelayRes$10 = stackDelayRes$10;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 9) {
      this.stackDelayRes$10 = value$;
    } else if (this.pc === 12) {
      this.tmp$9 = value$;
    } else if (this.pc === 10) {
      this.tmp$6 = value$;
    } else if (this.pc === 11) {
      this.tmp$7 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 9) {
        if (this.list$0 instanceof Stack.Cons.class) {
          this.param0$2 = this.list$0.head;
          this.param1$3 = this.list$0.tail;
          this.h$4 = this.param0$2;
          this.t$5 = this.param1$3;
          this.pc = 16;
          continue contLoop;
        } else if (this.list$0 instanceof Stack.Nil.class) {
          return Stack.Nil;
          this.pc = 13;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$9 = new globalThis.Error("match error");
          if (this.tmp$9 instanceof runtime.EffectSig.class) {
            this.pc = 12;
            this.tmp$9.contTrace.last.next = this;
            this.tmp$9.contTrace.last = this;
            return this.tmp$9
          }
          this.pc = 12;
          continue contLoop;
        }
        this.pc = 13;
        continue contLoop;
      } else if (this.pc === 13) {
        break contLoop;
      } else if (this.pc === 12) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$8);
        throw this.tmp$9;
      } else if (this.pc === 14) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Stack.Cons(this.tmp$6, this.tmp$7)
      } else if (this.pc === 16) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = runtime.safeCall(this.fn$1(this.h$4));
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 10;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 10;
        continue contLoop;
      } else if (this.pc === 10) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$8);
        this.pc = 15;
        continue contLoop;
      } else if (this.pc === 15) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = map(this.t$5, this.fn$1);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 11;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 11;
        continue contLoop;
      } else if (this.pc === 11) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$8);
        this.pc = 14;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$map$StackSafety$_mls_L0_423_504$(" + globalThis.Predef.render(this.pc) + ")"; }
};
map = function map(list, fn) {
  let param0, param1, h, t, tmp, tmp1, curDepth, tmp2, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$map$StackSafety$_mls_L0_423_504$$(list, fn, param0, param1, h, t, tmp, tmp1, curDepth, tmp2, stackDelayRes, 9);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (list instanceof Stack.Cons.class) {
    param0 = list.head;
    param1 = list.tail;
    h = param0;
    t = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = runtime.safeCall(fn(h));
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$map$StackSafety$_mls_L0_423_504$$(list, fn, param0, param1, h, t, tmp, tmp1, curDepth, tmp2, stackDelayRes, 10);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = map(t, fn);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$map$StackSafety$_mls_L0_423_504$$(list, fn, param0, param1, h, t, tmp, tmp1, curDepth, tmp2, stackDelayRes, 11);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return Stack.Cons(tmp, tmp1)
  } else if (list instanceof Stack.Nil.class) {
    return Stack.Nil
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = new globalThis.Error("match error");
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$map$StackSafety$_mls_L0_423_504$$(list, fn, param0, param1, h, t, tmp, tmp1, curDepth, tmp2, stackDelayRes, 12);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    throw tmp2;
  }
};
Cont$func$toString$StackSafety$_mls_L0_510_749$$ = function Cont$func$toString$StackSafety$_mls_L0_510_749$$(st$0, result$1, param0$2, param1$3, h$4, t$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13, pc) {
  let tmp;
  tmp = new Cont$func$toString$StackSafety$_mls_L0_510_749$1.class(pc);
  return tmp(st$0, result$1, param0$2, param1$3, h$4, t$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13)
};
Cont$func$toString$StackSafety$_mls_L0_510_749$$ctor = function Cont$func$toString$StackSafety$_mls_L0_510_749$$ctor(st$0, result$1, param0$2, param1$3, h$4, t$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$toString$StackSafety$_mls_L0_510_749$1.class(pc);
    return tmp(st$0, result$1, param0$2, param1$3, h$4, t$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13)
  }
};
Cont$func$toString$StackSafety$_mls_L0_510_749$1 = function Cont$func$toString$StackSafety$_mls_L0_510_749$(pc1) {
  return (st$01, result$11, param0$21, param1$31, h$41, t$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, curDepth$111, tmp$121, stackDelayRes$131) => {
    return new Cont$func$toString$StackSafety$_mls_L0_510_749$.class(pc1)(st$01, result$11, param0$21, param1$31, h$41, t$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, curDepth$111, tmp$121, stackDelayRes$131);
  }
};
Cont$func$toString$StackSafety$_mls_L0_510_749$1.class = class Cont$func$toString$StackSafety$_mls_L0_510_749$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (st$0, result$1, param0$2, param1$3, h$4, t$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.st$0 = st$0;
      this.result$1 = result$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.h$4 = h$4;
      this.t$5 = t$5;
      this.tmp$6 = tmp$6;
      this.tmp$7 = tmp$7;
      this.tmp$8 = tmp$8;
      this.tmp$9 = tmp$9;
      this.tmp$10 = tmp$10;
      this.curDepth$11 = curDepth$11;
      this.tmp$12 = tmp$12;
      this.stackDelayRes$13 = stackDelayRes$13;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 17) {
      this.stackDelayRes$13 = value$;
    } else if (this.pc === 19) {
      this.tmp$12 = value$;
    } else if (this.pc === 18) {
      this.tmp$6 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 17) {
        this.result$1 = "[";
        this.pc = 21;
        continue contLoop;
      } else if (this.pc === 20) {
        return this.tmp$10
      } else if (this.pc === 21) {
        if (this.st$0 instanceof Stack.Cons.class) {
          this.param0$2 = this.st$0.head;
          this.param1$3 = this.st$0.tail;
          this.h$4 = this.param0$2;
          this.t$5 = this.param1$3;
          this.pc = 23;
          continue contLoop;
        } else if (this.st$0 instanceof Stack.Nil.class) {
          return "[]";
          this.pc = 20;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$12 = new globalThis.Error("match error");
          if (this.tmp$12 instanceof runtime.EffectSig.class) {
            this.pc = 19;
            this.tmp$12.contTrace.last.next = this;
            this.tmp$12.contTrace.last = this;
            return this.tmp$12
          }
          this.pc = 19;
          continue contLoop;
        }
        this.pc = 20;
        continue contLoop;
      } else if (this.pc === 19) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$11);
        throw this.tmp$12;
      } else if (this.pc === 23) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = runtime.safeCall(this.h$4.toString());
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 18;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 18;
        continue contLoop;
      } else if (this.pc === 18) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$11);
        this.tmp$7 = this.result$1 + this.tmp$6;
        this.result$1 = this.tmp$7;
        this.st$0 = this.t$5;
        if (this.t$5 instanceof Stack.Nil.class) {
          return this.result$1 + "]"
        } else {
          this.tmp$8 = this.result$1 + ", ";
          this.result$1 = this.tmp$8;
          this.tmp$9 = runtime.Unit;
          this.pc = 22;
          continue contLoop;
        }
        this.pc = 22;
        continue contLoop;
      } else if (this.pc === 22) {
        this.tmp$10 = this.tmp$9;
        this.pc = 21;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$toString$StackSafety$_mls_L0_510_749$(" + globalThis.Predef.render(this.pc) + ")"; }
};
toString = function toString(st) {
  let result, param0, param1, h, t, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$toString$StackSafety$_mls_L0_510_749$$(st, result, param0, param1, h, t, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 17);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  result = "[";
  tmp6: while (true) {
    if (st instanceof Stack.Cons.class) {
      param0 = st.head;
      param1 = st.tail;
      h = param0;
      t = param1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = runtime.safeCall(h.toString());
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$toString$StackSafety$_mls_L0_510_749$$(st, result, param0, param1, h, t, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 18);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      tmp1 = result + tmp;
      result = tmp1;
      st = t;
      if (t instanceof Stack.Nil.class) {
        return result + "]"
      } else {
        tmp2 = result + ", ";
        result = tmp2;
        tmp3 = runtime.Unit;
      }
      tmp4 = tmp3;
      continue tmp6;
    } else if (st instanceof Stack.Nil.class) {
      return "[]"
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp5 = new globalThis.Error("match error");
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.contTrace.last.next = Cont$func$toString$StackSafety$_mls_L0_510_749$$(st, result, param0, param1, h, t, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 19);
        tmp5.contTrace.last = tmp5.contTrace.last.next;
        return tmp5
      }
      tmp5 = runtime.resetDepth(tmp5, curDepth);
      throw tmp5;
    }
    break;
  }
  return tmp4
};
Cont$func$main$StackSafety$_mls_L0_755_799$$ = function Cont$func$main$StackSafety$_mls_L0_755_799$$(n$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$main$StackSafety$_mls_L0_755_799$1.class(pc);
  return tmp(n$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$main$StackSafety$_mls_L0_755_799$$ctor = function Cont$func$main$StackSafety$_mls_L0_755_799$$ctor(n$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$main$StackSafety$_mls_L0_755_799$1.class(pc);
    return tmp(n$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$main$StackSafety$_mls_L0_755_799$1 = function Cont$func$main$StackSafety$_mls_L0_755_799$(pc1) {
  return (n$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$main$StackSafety$_mls_L0_755_799$.class(pc1)(n$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$main$StackSafety$_mls_L0_755_799$1.class = class Cont$func$main$StackSafety$_mls_L0_755_799$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (n$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.n$0 = n$0;
      this.tmp$1 = tmp$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 24) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 25) {
      this.tmp$1 = value$;
    } else if (this.pc === 26) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 24) {
        this.pc = 29;
        continue contLoop;
      } else if (this.pc === 27) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return toString(this.tmp$2)
      } else if (this.pc === 28) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = map(this.tmp$1, sum);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 26;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 26;
        continue contLoop;
      } else if (this.pc === 29) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = fill(this.n$0, 10);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 25;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 25;
        continue contLoop;
      } else if (this.pc === 25) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$3);
        this.pc = 28;
        continue contLoop;
      } else if (this.pc === 26) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        this.pc = 27;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$main$StackSafety$_mls_L0_755_799$(" + globalThis.Predef.render(this.pc) + ")"; }
};
main = function main(n) {
  let tmp, tmp1, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$main$StackSafety$_mls_L0_755_799$$(n, tmp, tmp1, curDepth, stackDelayRes, 24);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = fill(n, 10);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$main$StackSafety$_mls_L0_755_799$$(n, tmp, tmp1, curDepth, stackDelayRes, 25);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = map(tmp, sum);
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$main$StackSafety$_mls_L0_755_799$$(n, tmp, tmp1, curDepth, stackDelayRes, 26);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return toString(tmp1)
};
Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$ = function Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$(fn$0, suite$1, data$2, i$3, scrut$4, settings$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, stackDelayRes$17, pc) {
  let tmp;
  tmp = new Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$1.class(pc);
  return tmp(fn$0, suite$1, data$2, i$3, scrut$4, settings$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, stackDelayRes$17)
};
Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$ctor = function Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$ctor(fn$0, suite$1, data$2, i$3, scrut$4, settings$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, stackDelayRes$17) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$1.class(pc);
    return tmp(fn$0, suite$1, data$2, i$3, scrut$4, settings$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, stackDelayRes$17)
  }
};
Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$1 = function Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$(pc1) {
  return (fn$01, suite$11, data$21, i$31, scrut$41, settings$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, curDepth$161, stackDelayRes$171) => {
    return new Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$.class(pc1)(fn$01, suite$11, data$21, i$31, scrut$41, settings$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, curDepth$161, stackDelayRes$171);
  }
};
Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$1.class = class Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (fn$0, suite$1, data$2, i$3, scrut$4, settings$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, stackDelayRes$17) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.fn$0 = fn$0;
      this.suite$1 = suite$1;
      this.data$2 = data$2;
      this.i$3 = i$3;
      this.scrut$4 = scrut$4;
      this.settings$5 = settings$5;
      this.tmp$6 = tmp$6;
      this.tmp$7 = tmp$7;
      this.tmp$8 = tmp$8;
      this.tmp$9 = tmp$9;
      this.tmp$10 = tmp$10;
      this.tmp$11 = tmp$11;
      this.tmp$12 = tmp$12;
      this.tmp$13 = tmp$13;
      this.tmp$14 = tmp$14;
      this.tmp$15 = tmp$15;
      this.curDepth$16 = curDepth$16;
      this.stackDelayRes$17 = stackDelayRes$17;
      return this;
    }
  }
  resume(value$) {
    let lambda$this;
    if (this.pc === 30) {
      this.stackDelayRes$17 = value$;
    } else if (this.pc === 31) {
      this.tmp$6 = value$;
    } else if (this.pc === 32) {
      this.tmp$7 = value$;
    } else if (this.pc === 33) {
      this.tmp$8 = value$;
    } else if (this.pc === 34) {
      this.tmp$9 = value$;
    } else if (this.pc === 35) {
      this.tmp$12 = value$;
    } else if (this.pc === 46) {
      this.tmp$14 = value$;
    } else if (this.pc === 51) {
      this.tmp$15 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 30) {
        this.pc = 59;
        continue contLoop;
      } else if (this.pc === 59) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = Predef.print("benchmarking...");
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 31;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 31;
        continue contLoop;
      } else if (this.pc === 31) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$16);
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = new benchmark.Suite();
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 32;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 32;
        continue contLoop;
      } else if (this.pc === 32) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$16);
        this.suite$1 = this.tmp$7;
        this.data$2 = runtime.Unit;
        this.data$2.x = [];
        this.data$2.y = [];
        this.data$2.log = [];
        this.i$3 = 50;
        this.pc = 56;
        continue contLoop;
      } else if (this.pc === 56) {
        this.scrut$4 = this.i$3 <= 15000;
        if (this.scrut$4 === true) {
          this.pc = 58;
          continue contLoop;
        } else {
          this.tmp$11 = runtime.Unit;
          this.pc = 55;
          continue contLoop;
        }
        this.pc = 55;
        continue contLoop;
      } else if (this.pc === 57) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = this.suite$1.add(this.i$3, this.tmp$8);
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 34;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 34;
        continue contLoop;
      } else if (this.pc === 58) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = this.fn$0.bind(null, this.i$3);
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 33;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 33;
        continue contLoop;
      } else if (this.pc === 33) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$16);
        this.pc = 57;
        continue contLoop;
      } else if (this.pc === 34) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$16);
        this.tmp$10 = this.i$3 + 50;
        this.i$3 = this.tmp$10;
        this.tmp$11 = runtime.Unit;
        this.pc = 56;
        continue contLoop;
      } else if (this.pc === 55) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$12 = this.suite$1.add("main", this.fn$0);
        if (this.tmp$12 instanceof runtime.EffectSig.class) {
          this.pc = 35;
          this.tmp$12.contTrace.last.next = this;
          this.tmp$12.contTrace.last = this;
          return this.tmp$12
        }
        this.pc = 35;
        continue contLoop;
      } else if (this.pc === 35) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$16);
        this.settings$5 = runtime.Unit;
        this.settings$5.async = false;
        this.tmp$13 = runtime.safeCall(lambda(this.data$2));
        this.pc = 54;
        continue contLoop;
      } else if (this.pc === 54) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$14 = this.suite$1.on("cycle", this.tmp$13);
        if (this.tmp$14 instanceof runtime.EffectSig.class) {
          this.pc = 46;
          this.tmp$14.contTrace.last.next = this;
          this.tmp$14.contTrace.last = this;
          return this.tmp$14
        }
        this.pc = 46;
        continue contLoop;
      } else if (this.pc === 46) {
        this.tmp$14 = runtime.resetDepth(this.tmp$14, this.curDepth$16);
        this.pc = 53;
        continue contLoop;
      } else if (this.pc === 53) {
        runtime.stackDepth = runtime.stackDepth + 1;
        lambda$this = runtime.safeCall(lambda1(this.data$2));
        this.tmp$15 = this.tmp$14.on("complete", lambda$this);
        if (this.tmp$15 instanceof runtime.EffectSig.class) {
          this.pc = 51;
          this.tmp$15.contTrace.last.next = this;
          this.tmp$15.contTrace.last = this;
          return this.tmp$15
        }
        this.pc = 51;
        continue contLoop;
      } else if (this.pc === 51) {
        this.tmp$15 = runtime.resetDepth(this.tmp$15, this.curDepth$16);
        this.pc = 52;
        continue contLoop;
      } else if (this.pc === 52) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.tmp$15.run(this.settings$5))
      }
      break;
    }
  }
  toString() { return "Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$1 = function Cont$func$lambda$$$(data$0, event$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$4.class(pc);
  return tmp(data$0, event$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7)
};
Cont$func$lambda$$$ctor1 = function Cont$func$lambda$$$ctor(data$0, event$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$4.class(pc);
    return tmp(data$0, event$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7)
  }
};
Cont$func$lambda$$4 = function Cont$func$lambda$$(pc1) {
  return (data$01, event$11, tmp$21, tmp$31, tmp$41, tmp$51, curDepth$61, stackDelayRes$71) => {
    return new Cont$func$lambda$$.class(pc1)(data$01, event$11, tmp$21, tmp$31, tmp$41, tmp$51, curDepth$61, stackDelayRes$71);
  }
};
Cont$func$lambda$$4.class = class Cont$func$lambda$$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (data$0, event$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.data$0 = data$0;
      this.event$1 = event$1;
      this.tmp$2 = tmp$2;
      this.tmp$3 = tmp$3;
      this.tmp$4 = tmp$4;
      this.tmp$5 = tmp$5;
      this.curDepth$6 = curDepth$6;
      this.stackDelayRes$7 = stackDelayRes$7;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 36) {
      this.stackDelayRes$7 = value$;
    } else if (this.pc === 37) {
      this.tmp$2 = value$;
    } else if (this.pc === 38) {
      this.tmp$3 = value$;
    } else if (this.pc === 39) {
      this.tmp$4 = value$;
    } else if (this.pc === 40) {
      this.tmp$5 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 36) {
        this.pc = 45;
        continue contLoop;
      } else if (this.pc === 44) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = Predef.print(this.tmp$2);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 38;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 38;
        continue contLoop;
      } else if (this.pc === 45) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = globalThis.String(this.event$1.target);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 37;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 37;
        continue contLoop;
      } else if (this.pc === 37) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$6);
        this.pc = 44;
        continue contLoop;
      } else if (this.pc === 38) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$6);
        this.pc = 43;
        continue contLoop;
      } else if (this.pc === 43) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$4 = runtime.safeCall(this.data$0.y.push(this.event$1.target.hz));
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 39;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 39;
        continue contLoop;
      } else if (this.pc === 39) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$6);
        this.pc = 42;
        continue contLoop;
      } else if (this.pc === 41) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.data$0.log.push(this.tmp$5))
      } else if (this.pc === 42) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = globalThis.String(this.event$1.target);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 40;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 40;
        continue contLoop;
      } else if (this.pc === 40) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$6);
        this.pc = 41;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda$1 = function lambda$(data, event) {
  let tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$1(data, event, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 36);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = globalThis.String(event.target);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$1(data, event, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 37);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = Predef.print(tmp);
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$lambda$$$1(data, event, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 38);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp2 = runtime.safeCall(data.y.push(event.target.hz));
  if (tmp2 instanceof runtime.EffectSig.class) {
    tmp2.contTrace.last.next = Cont$func$lambda$$$1(data, event, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 39);
    tmp2.contTrace.last = tmp2.contTrace.last.next;
    return tmp2
  }
  tmp2 = runtime.resetDepth(tmp2, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp3 = globalThis.String(event.target);
  if (tmp3 instanceof runtime.EffectSig.class) {
    tmp3.contTrace.last.next = Cont$func$lambda$$$1(data, event, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 40);
    tmp3.contTrace.last = tmp3.contTrace.last.next;
    return tmp3
  }
  tmp3 = runtime.resetDepth(tmp3, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return runtime.safeCall(data.log.push(tmp3))
};
lambda = (undefined, function (data) {
  return (event) => {
    return lambda$1(data, event)
  }
});
Cont$func$lambda$$$ = function Cont$func$lambda$$$(data$0, tmp$1, curDepth$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$5.class(pc);
  return tmp(data$0, tmp$1, curDepth$2, stackDelayRes$3)
};
Cont$func$lambda$$$ctor = function Cont$func$lambda$$$ctor(data$0, tmp$1, curDepth$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$5.class(pc);
    return tmp(data$0, tmp$1, curDepth$2, stackDelayRes$3)
  }
};
Cont$func$lambda$$5 = function Cont$func$lambda$$(pc1) {
  return (data$01, tmp$11, curDepth$21, stackDelayRes$31) => {
    return new Cont$func$lambda$$.class(pc1)(data$01, tmp$11, curDepth$21, stackDelayRes$31);
  }
};
Cont$func$lambda$$5.class = class Cont$func$lambda$$1 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (data$0, tmp$1, curDepth$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.data$0 = data$0;
      this.tmp$1 = tmp$1;
      this.curDepth$2 = curDepth$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 47) {
      this.stackDelayRes$3 = value$;
    } else if (this.pc === 48) {
      this.tmp$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 47) {
        this.pc = 50;
        continue contLoop;
      } else if (this.pc === 49) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return fs.writeFileSync("./benchmark/data.json", this.tmp$1)
      } else if (this.pc === 50) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = runtime.safeCall(globalThis.JSON.stringify(this.data$0));
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 48;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 48;
        continue contLoop;
      } else if (this.pc === 48) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$2);
        this.pc = 49;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda$ = function lambda$(data) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$(data, tmp, curDepth, stackDelayRes, 47);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = runtime.safeCall(globalThis.JSON.stringify(data));
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$(data, tmp, curDepth, stackDelayRes, 48);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return fs.writeFileSync("./benchmark/data.json", tmp)
};
lambda1 = (undefined, function (data) {
  return () => {
    return lambda$(data)
  }
});
do_benchmark = function do_benchmark(fn) {
  let suite, data, i, scrut, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, lambda$this;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$(fn, suite, data, i, scrut, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 30);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = Predef.print("benchmarking...");
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$(fn, suite, data, i, scrut, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 31);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = new benchmark.Suite();
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$(fn, suite, data, i, scrut, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 32);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  suite = tmp1;
  data = runtime.Unit;
  data.x = [];
  data.y = [];
  data.log = [];
  i = 50;
  tmp10: while (true) {
    scrut = i <= 15000;
    if (scrut === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = fn.bind(null, i);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.contTrace.last.next = Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$(fn, suite, data, i, scrut, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 33);
        tmp2.contTrace.last = tmp2.contTrace.last.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = suite.add(i, tmp2);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.contTrace.last.next = Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$(fn, suite, data, i, scrut, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 34);
        tmp3.contTrace.last = tmp3.contTrace.last.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      tmp4 = i + 50;
      i = tmp4;
      tmp5 = runtime.Unit;
      continue tmp10;
    } else {
      tmp5 = runtime.Unit;
    }
    break;
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp6 = suite.add("main", fn);
  if (tmp6 instanceof runtime.EffectSig.class) {
    tmp6.contTrace.last.next = Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$(fn, suite, data, i, scrut, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 35);
    tmp6.contTrace.last = tmp6.contTrace.last.next;
    return tmp6
  }
  tmp6 = runtime.resetDepth(tmp6, curDepth);
  settings = runtime.Unit;
  settings.async = false;
  tmp7 = runtime.safeCall(lambda(data));
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp8 = suite.on("cycle", tmp7);
  if (tmp8 instanceof runtime.EffectSig.class) {
    tmp8.contTrace.last.next = Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$(fn, suite, data, i, scrut, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 46);
    tmp8.contTrace.last = tmp8.contTrace.last.next;
    return tmp8
  }
  tmp8 = runtime.resetDepth(tmp8, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  lambda$this = runtime.safeCall(lambda1(data));
  tmp9 = tmp8.on("complete", lambda$this);
  if (tmp9 instanceof runtime.EffectSig.class) {
    tmp9.contTrace.last.next = Cont$func$do_benchmark$StackSafety$_mls_L0_805_1364$$(fn, suite, data, i, scrut, settings, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 51);
    tmp9.contTrace.last = tmp9.contTrace.last.next;
    return tmp9
  }
  tmp9 = runtime.resetDepth(tmp9, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return runtime.safeCall(tmp9.run(settings))
};
Cont$func$lambda$$$3 = function Cont$func$lambda$$$(x$0, stackDelayRes$1, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$7.class(pc);
  return tmp(x$0, stackDelayRes$1)
};
Cont$func$lambda$$$ctor3 = function Cont$func$lambda$$$ctor(x$0, stackDelayRes$1) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$7.class(pc);
    return tmp(x$0, stackDelayRes$1)
  }
};
Cont$func$lambda$$7 = function Cont$func$lambda$$(pc1) {
  return (x$01, stackDelayRes$11) => {
    return new Cont$func$lambda$$.class(pc1)(x$01, stackDelayRes$11);
  }
};
Cont$func$lambda$$7.class = class Cont$func$lambda$$2 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, stackDelayRes$1) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$0 = x$0;
      this.stackDelayRes$1 = stackDelayRes$1;
      return this;
    }
  }
  resume(value$) {
    let lambda$this;
    if (this.pc === 60) {
      this.stackDelayRes$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 60) {
        this.pc = 63;
        continue contLoop;
      } else if (this.pc === 63) {
        runtime.stackDepth = runtime.stackDepth + 1;
        lambda$this = runtime.safeCall(lambda3(this.x$0));
        return BenchmarkPrelude.helper(lambda$this)
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$2 = function Cont$func$lambda$$$(x$0, stackDelayRes$1, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$6.class(pc);
  return tmp(x$0, stackDelayRes$1)
};
Cont$func$lambda$$$ctor2 = function Cont$func$lambda$$$ctor(x$0, stackDelayRes$1) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$6.class(pc);
    return tmp(x$0, stackDelayRes$1)
  }
};
Cont$func$lambda$$6 = function Cont$func$lambda$$(pc1) {
  return (x$01, stackDelayRes$11) => {
    return new Cont$func$lambda$$.class(pc1)(x$01, stackDelayRes$11);
  }
};
Cont$func$lambda$$6.class = class Cont$func$lambda$$3 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, stackDelayRes$1) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$0 = x$0;
      this.stackDelayRes$1 = stackDelayRes$1;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 61) {
      this.stackDelayRes$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 61) {
        this.pc = 62;
        continue contLoop;
      } else if (this.pc === 62) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return main(this.x$0)
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda$2 = function lambda$(x) {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$2(x, stackDelayRes, 61);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return main(x)
};
lambda3 = (undefined, function (x) {
  return () => {
    return lambda$2(x)
  }
});
lambda2 = (undefined, function (x) {
  let stackDelayRes, lambda$this;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$3(x, stackDelayRes, 60);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  lambda$this = runtime.safeCall(lambda3(x));
  return BenchmarkPrelude.helper(lambda$this)
});
lambda$3 = function lambda$(StackDelay$$instance, resume) {
  runtime.stackOffset = runtime.stackDepth;
  return resume()
};
lambda4 = (undefined, function (StackDelay$$instance) {
  return (resume) => {
    return lambda$3(StackDelay$$instance, resume)
  }
});
StackDelay$1 = class StackDelay$ extends runtime.StackDelay {
  constructor() {
    let tmp;
    tmp = super();
  }
  perform() {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda4(this));
    return runtime.mkEffect(this, lambda$this)
  }
  toString() { return "StackDelay$"; }
};
Cont$handleBlock$stackHandler$$ = function Cont$handleBlock$stackHandler$$(res$0, pc) {
  let tmp;
  tmp = new Cont$handleBlock$stackHandler$1.class(pc);
  return tmp(res$0)
};
Cont$handleBlock$stackHandler$$ctor = function Cont$handleBlock$stackHandler$$ctor(res$0) {
  return (pc) => {
    let tmp;
    tmp = new Cont$handleBlock$stackHandler$1.class(pc);
    return tmp(res$0)
  }
};
Cont$handleBlock$stackHandler$1 = function Cont$handleBlock$stackHandler$(pc1) {
  return (res$01) => {
    return new Cont$handleBlock$stackHandler$.class(pc1)(res$01);
  }
};
Cont$handleBlock$stackHandler$1.class = class Cont$handleBlock$stackHandler$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (res$0) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.res$0 = res$0;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 64) {
      this.res$0 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 64) {
        return this.res$0
      }
      break;
    }
  }
  toString() { return "Cont$handleBlock$stackHandler$(" + globalThis.Predef.render(this.pc) + ")"; }
};
handleBlock$ = function handleBlock$() {
  let stackHandler, res1;
  stackHandler = new StackDelay$1();
  runtime.stackLimit = 500;
  runtime.stackOffset = 0;
  runtime.stackDepth = 1;
  runtime.stackHandler = stackHandler;
  res1 = do_benchmark(lambda2);
  if (res1 instanceof runtime.EffectSig.class) {
    res1.contTrace.last.next = Cont$handleBlock$stackHandler$$(res1, 64);
    return runtime.handleBlockImpl(res1, stackHandler)
  }
  return res1
};
res = handleBlock$();
if (res instanceof runtime.EffectSig.class) {
  throw new this.Error("Unhandled effects");
}
runtime.stackDepth = 0;
runtime.stackHandler = null;
res