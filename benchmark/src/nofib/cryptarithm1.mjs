import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let lscomp, lscomp2, lscomp1, cryptarithm11, lambda, Cont$func$condition$cryptarithm1$_mls_L0_310_501$1, Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$1, Cont$func$addj$cryptarithm1$_mls_L0_507_715$1, Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$1, Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$1, Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$1, Cont$func$lambda$$2, Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$1, Cont$func$lambda$$3, Cont$func$lambda$$$ctor, Cont$func$lambda$$$, Cont$func$condition$cryptarithm1$_mls_L0_310_501$$ctor, Cont$func$condition$cryptarithm1$_mls_L0_310_501$$, lscomp$, Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$$ctor, Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$$, Cont$func$addj$cryptarithm1$_mls_L0_507_715$$ctor, Cont$func$addj$cryptarithm1$_mls_L0_507_715$$, lscomp1$, lscomp2$, Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$$ctor, Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$$, Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$$ctor, Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$$, Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$$ctor, Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$$, Cont$func$lambda$$$ctor1, Cont$func$lambda$$$1, Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$$ctor, Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$$, lscomp1$capture1;
Cont$func$lambda$$$ = function Cont$func$lambda$$$(tmp$0, curDepth$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$3.class(pc);
  return tmp(tmp$0, curDepth$1, stackDelayRes$2)
};
Cont$func$lambda$$$ctor = function Cont$func$lambda$$$ctor(tmp$0, curDepth$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$3.class(pc);
    return tmp(tmp$0, curDepth$1, stackDelayRes$2)
  }
};
Cont$func$lambda$$3 = function Cont$func$lambda$$(pc1) {
  return (tmp$01, curDepth$11, stackDelayRes$21) => {
    return new Cont$func$lambda$$.class(pc1)(tmp$01, curDepth$11, stackDelayRes$21);
  }
};
Cont$func$lambda$$3.class = class Cont$func$lambda$$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (tmp$0, curDepth$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.tmp$0 = tmp$0;
      this.curDepth$1 = curDepth$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 74) {
      this.stackDelayRes$2 = value$;
    } else if (this.pc === 75) {
      this.tmp$0 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 74) {
        this.pc = 77;
        continue contLoop;
      } else if (this.pc === 76) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return BenchmarkPrelude.print(this.tmp$0)
      } else if (this.pc === 77) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$0 = cryptarithm11.testCryptarithm_nofib(1);
        if (this.tmp$0 instanceof runtime.EffectSig.class) {
          this.pc = 75;
          this.tmp$0.contTrace.last.next = this;
          this.tmp$0.contTrace.last = this;
          return this.tmp$0
        }
        this.pc = 75;
        continue contLoop;
      } else if (this.pc === 75) {
        this.tmp$0 = runtime.resetDepth(this.tmp$0, this.curDepth$1);
        this.pc = 76;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$$ = function Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$$(n$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$1.class(pc);
  return tmp(n$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$$ctor = function Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$$ctor(n$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$1.class(pc);
    return tmp(n$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$1 = function Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$(pc1) {
  return (n$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$.class(pc1)(n$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$1.class = class Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (n$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.n$0 = n$0;
      this.tmp$1 = tmp$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 62) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 71) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 62) {
        this.tmp$1 = lambda;
        this.pc = 73;
        continue contLoop;
      } else if (this.pc === 72) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.map(this.tmp$1, this.tmp$2)
      } else if (this.pc === 73) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = NofibPrelude.enumFromTo(1, this.n$0);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 71;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 71;
        continue contLoop;
      } else if (this.pc === 71) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        this.pc = 72;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$1 = function Cont$func$lambda$$$(i$0, p0$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$2.class(pc);
  return tmp(i$0, p0$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7)
};
Cont$func$lambda$$$ctor1 = function Cont$func$lambda$$$ctor(i$0, p0$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$2.class(pc);
    return tmp(i$0, p0$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7)
  }
};
Cont$func$lambda$$2 = function Cont$func$lambda$$(pc1) {
  return (i$01, p0$11, tmp$21, tmp$31, tmp$41, tmp$51, curDepth$61, stackDelayRes$71) => {
    return new Cont$func$lambda$$.class(pc1)(i$01, p0$11, tmp$21, tmp$31, tmp$41, tmp$51, curDepth$61, stackDelayRes$71);
  }
};
Cont$func$lambda$$2.class = class Cont$func$lambda$$1 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (i$0, p0$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7) => {
      let tmp;
      tmp = super(null);
      this.i$0 = i$0;
      this.p0$1 = p0$1;
      this.tmp$2 = tmp$2;
      this.tmp$3 = tmp$3;
      this.tmp$4 = tmp$4;
      this.tmp$5 = tmp$5;
      this.curDepth$6 = curDepth$6;
      this.stackDelayRes$7 = stackDelayRes$7;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 63) {
      this.stackDelayRes$7 = value$;
    } else if (this.pc === 64) {
      this.tmp$3 = value$;
    } else if (this.pc === 65) {
      this.tmp$4 = value$;
    } else if (this.pc === 66) {
      this.tmp$5 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 63) {
        this.tmp$2 = 9 + this.i$0;
        this.pc = 70;
        continue contLoop;
      } else if (this.pc === 69) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$4 = NofibPrelude.take(10, this.tmp$3);
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 65;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 65;
        continue contLoop;
      } else if (this.pc === 70) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = NofibPrelude.enumFromTo(0, this.tmp$2);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 64;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 64;
        continue contLoop;
      } else if (this.pc === 64) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$6);
        this.pc = 69;
        continue contLoop;
      } else if (this.pc === 65) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$6);
        this.p0$1 = this.tmp$4;
        this.pc = 68;
        continue contLoop;
      } else if (this.pc === 67) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.filter(cryptarithm11.condition, this.tmp$5)
      } else if (this.pc === 68) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = cryptarithm11.permutations(this.p0$1);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 66;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 66;
        continue contLoop;
      } else if (this.pc === 66) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$6);
        this.pc = 67;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda = (undefined, function (i) {
  let p0, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$1(i, p0, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 63);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  tmp = 9 + i;
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = NofibPrelude.enumFromTo(0, tmp);
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$lambda$$$1(i, p0, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 64);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp2 = NofibPrelude.take(10, tmp1);
  if (tmp2 instanceof runtime.EffectSig.class) {
    tmp2.contTrace.last.next = Cont$func$lambda$$$1(i, p0, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 65);
    tmp2.contTrace.last = tmp2.contTrace.last.next;
    return tmp2
  }
  tmp2 = runtime.resetDepth(tmp2, curDepth);
  p0 = tmp2;
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp3 = cryptarithm11.permutations(p0);
  if (tmp3 instanceof runtime.EffectSig.class) {
    tmp3.contTrace.last.next = Cont$func$lambda$$$1(i, p0, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 66);
    tmp3.contTrace.last = tmp3.contTrace.last.next;
    return tmp3
  }
  tmp3 = runtime.resetDepth(tmp3, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return NofibPrelude.filter(cryptarithm11.condition, tmp3)
});
Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$$ = function Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$$(ls$0, param0$1, param1$2, j$3, js$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8, pc) {
  let tmp;
  tmp = new Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$1.class(pc);
  return tmp(ls$0, param0$1, param1$2, j$3, js$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8)
};
Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$$ctor = function Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$$ctor(ls$0, param0$1, param1$2, j$3, js$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$1.class(pc);
    return tmp(ls$0, param0$1, param1$2, j$3, js$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8)
  }
};
Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$1 = function Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$(pc1) {
  return (ls$01, param0$11, param1$21, j$31, js$41, tmp$51, curDepth$61, tmp$71, stackDelayRes$81) => {
    return new Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$.class(pc1)(ls$01, param0$11, param1$21, j$31, js$41, tmp$51, curDepth$61, tmp$71, stackDelayRes$81);
  }
};
Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$1.class = class Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (ls$0, param0$1, param1$2, j$3, js$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8) => {
      let tmp;
      tmp = super(null);
      this.ls$0 = ls$0;
      this.param0$1 = param0$1;
      this.param1$2 = param1$2;
      this.j$3 = j$3;
      this.js$4 = js$4;
      this.tmp$5 = tmp$5;
      this.curDepth$6 = curDepth$6;
      this.tmp$7 = tmp$7;
      this.stackDelayRes$8 = stackDelayRes$8;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 42) {
      this.stackDelayRes$8 = value$;
    } else if (this.pc === 57) {
      this.tmp$7 = value$;
    } else if (this.pc === 56) {
      this.tmp$5 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 42) {
        if (this.ls$0 instanceof NofibPrelude.Nil.class) {
          this.pc = 59;
          continue contLoop;
        } else if (this.ls$0 instanceof NofibPrelude.Cons.class) {
          this.param0$1 = this.ls$0.head;
          this.param1$2 = this.ls$0.tail;
          this.j$3 = this.param0$1;
          this.js$4 = this.param1$2;
          this.pc = 61;
          continue contLoop;
          this.pc = 58;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$7 = new globalThis.Error("match error");
          if (this.tmp$7 instanceof runtime.EffectSig.class) {
            this.pc = 57;
            this.tmp$7.contTrace.last.next = this;
            this.tmp$7.contTrace.last = this;
            return this.tmp$7
          }
          this.pc = 57;
          continue contLoop;
        }
        this.pc = 58;
        continue contLoop;
      } else if (this.pc === 58) {
        break contLoop;
      } else if (this.pc === 57) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$6);
        throw this.tmp$7;
      } else if (this.pc === 60) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return lscomp1$(this.j$3, this.tmp$5)
      } else if (this.pc === 61) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = cryptarithm11.permutations(this.js$4);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 56;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 56;
        continue contLoop;
      } else if (this.pc === 56) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$6);
        this.pc = 60;
        continue contLoop;
      } else if (this.pc === 59) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil)
      }
      break;
    }
  }
  toString() { return "Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$$ = function Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$$(j$1, p1$2, curDepth$3, lscomp1$capture$0, pc) {
  let tmp;
  tmp = new Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$1.class(pc);
  return tmp(j$1, p1$2, curDepth$3, lscomp1$capture$0)
};
Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$$ctor = function Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$$ctor(j$1, p1$2, curDepth$3, lscomp1$capture$0) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$1.class(pc);
    return tmp(j$1, p1$2, curDepth$3, lscomp1$capture$0)
  }
};
Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$1 = function Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$(pc1) {
  return (j$11, p1$21, curDepth$31, lscomp1$capture$01) => {
    return new Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$.class(pc1)(j$11, p1$21, curDepth$31, lscomp1$capture$01);
  }
};
Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$1.class = class Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (j$1, p1$2, curDepth$3, lscomp1$capture$0) => {
      let tmp;
      tmp = super(null);
      this.j$1 = j$1;
      this.p1$2 = p1$2;
      this.curDepth$3 = curDepth$3;
      this.lscomp1$capture$0 = lscomp1$capture$0;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 43) {
      this.lscomp1$capture$0.stackDelayRes6$ = value$;
    } else if (this.pc === 52) {
      this.lscomp1$capture$0.tmp5$ = value$;
    } else if (this.pc === 51) {
      this.lscomp1$capture$0.tmp4$ = value$;
    }
    contLoop: while (true) {
      if (this.pc === 43) {
        if (this.p1$2 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (this.p1$2 instanceof NofibPrelude.Cons.class) {
          this.lscomp1$capture$0.param00$ = this.p1$2.head;
          this.lscomp1$capture$0.param11$ = this.p1$2.tail;
          this.lscomp1$capture$0.pjs2$ = this.lscomp1$capture$0.param00$;
          this.lscomp1$capture$0.t13$ = this.lscomp1$capture$0.param11$;
          this.pc = 55;
          continue contLoop;
          this.pc = 53;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.lscomp1$capture$0.tmp5$ = new globalThis.Error("match error");
          if (this.lscomp1$capture$0.tmp5$ instanceof runtime.EffectSig.class) {
            this.pc = 52;
            this.lscomp1$capture$0.tmp5$.contTrace.last.next = this;
            this.lscomp1$capture$0.tmp5$.contTrace.last = this;
            return this.lscomp1$capture$0.tmp5$
          }
          this.pc = 52;
          continue contLoop;
        }
        this.pc = 53;
        continue contLoop;
      } else if (this.pc === 53) {
        break contLoop;
      } else if (this.pc === 52) {
        this.lscomp1$capture$0.tmp5$ = runtime.resetDepth(this.lscomp1$capture$0.tmp5$, this.curDepth$3);
        throw this.lscomp1$capture$0.tmp5$;
      } else if (this.pc === 54) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return lscomp2$(this.j$1, this.p1$2, this.curDepth$3, this.lscomp1$capture$0, this.lscomp1$capture$0.tmp4$)
      } else if (this.pc === 55) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.lscomp1$capture$0.tmp4$ = cryptarithm11.addj(this.j$1, this.lscomp1$capture$0.pjs2$);
        if (this.lscomp1$capture$0.tmp4$ instanceof runtime.EffectSig.class) {
          this.pc = 51;
          this.lscomp1$capture$0.tmp4$.contTrace.last.next = this;
          this.lscomp1$capture$0.tmp4$.contTrace.last = this;
          return this.lscomp1$capture$0.tmp4$
        }
        this.pc = 51;
        continue contLoop;
      } else if (this.pc === 51) {
        this.lscomp1$capture$0.tmp4$ = runtime.resetDepth(this.lscomp1$capture$0.tmp4$, this.curDepth$3);
        this.pc = 54;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$$ = function Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$$(j$1, p1$2, p2$3, param0$4, param1$5, r$6, t2$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11, curDepth$12, lscomp1$capture$0, pc) {
  let tmp;
  tmp = new Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$1.class(pc);
  return tmp(j$1, p1$2, p2$3, param0$4, param1$5, r$6, t2$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11, curDepth$12, lscomp1$capture$0)
};
Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$$ctor = function Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$$ctor(j$1, p1$2, p2$3, param0$4, param1$5, r$6, t2$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11, curDepth$12, lscomp1$capture$0) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$1.class(pc);
    return tmp(j$1, p1$2, p2$3, param0$4, param1$5, r$6, t2$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11, curDepth$12, lscomp1$capture$0)
  }
};
Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$1 = function Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$(pc1) {
  return (j$11, p1$21, p2$31, param0$41, param1$51, r$61, t2$71, tmp$81, curDepth$91, tmp$101, stackDelayRes$111, curDepth$121, lscomp1$capture$01) => {
    return new Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$.class(pc1)(j$11, p1$21, p2$31, param0$41, param1$51, r$61, t2$71, tmp$81, curDepth$91, tmp$101, stackDelayRes$111, curDepth$121, lscomp1$capture$01);
  }
};
Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$1.class = class Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (j$1, p1$2, p2$3, param0$4, param1$5, r$6, t2$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11, curDepth$12, lscomp1$capture$0) => {
      let tmp;
      tmp = super(null);
      this.j$1 = j$1;
      this.p1$2 = p1$2;
      this.p2$3 = p2$3;
      this.param0$4 = param0$4;
      this.param1$5 = param1$5;
      this.r$6 = r$6;
      this.t2$7 = t2$7;
      this.tmp$8 = tmp$8;
      this.curDepth$9 = curDepth$9;
      this.tmp$10 = tmp$10;
      this.stackDelayRes$11 = stackDelayRes$11;
      this.curDepth$12 = curDepth$12;
      this.lscomp1$capture$0 = lscomp1$capture$0;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 44) {
      this.stackDelayRes$11 = value$;
    } else if (this.pc === 46) {
      this.tmp$10 = value$;
    } else if (this.pc === 45) {
      this.tmp$8 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 44) {
        if (this.p2$3 instanceof NofibPrelude.Nil.class) {
          this.pc = 48;
          continue contLoop;
        } else if (this.p2$3 instanceof NofibPrelude.Cons.class) {
          this.param0$4 = this.p2$3.head;
          this.param1$5 = this.p2$3.tail;
          this.r$6 = this.param0$4;
          this.t2$7 = this.param1$5;
          this.pc = 50;
          continue contLoop;
          this.pc = 47;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$10 = new globalThis.Error("match error");
          if (this.tmp$10 instanceof runtime.EffectSig.class) {
            this.pc = 46;
            this.tmp$10.contTrace.last.next = this;
            this.tmp$10.contTrace.last = this;
            return this.tmp$10
          }
          this.pc = 46;
          continue contLoop;
        }
        this.pc = 47;
        continue contLoop;
      } else if (this.pc === 47) {
        break contLoop;
      } else if (this.pc === 46) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$9);
        throw this.tmp$10;
      } else if (this.pc === 49) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.r$6, this.tmp$8)
      } else if (this.pc === 50) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = lscomp2$(this.j$1, this.p1$2, this.curDepth$12, this.lscomp1$capture$0, this.t2$7);
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 45;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 45;
        continue contLoop;
      } else if (this.pc === 45) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$9);
        this.pc = 49;
        continue contLoop;
      } else if (this.pc === 48) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return lscomp1$(this.j$1, this.lscomp1$capture$0.t13$)
      }
      break;
    }
  }
  toString() { return "Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lscomp2$ = function lscomp2$(j, p1, curDepth, lscomp1$capture2, p2) {
  let param0, param1, r, t2, tmp, curDepth1, tmp1, stackDelayRes;
  curDepth1 = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$$(j, p1, p2, param0, param1, r, t2, tmp, curDepth1, tmp1, stackDelayRes, curDepth, lscomp1$capture2, 44);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (p2 instanceof NofibPrelude.Nil.class) {
    runtime.stackDepth = runtime.stackDepth + 1;
    return lscomp1$(j, lscomp1$capture2.t13$)
  } else if (p2 instanceof NofibPrelude.Cons.class) {
    param0 = p2.head;
    param1 = p2.tail;
    r = param0;
    t2 = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = lscomp2$(j, p1, curDepth, lscomp1$capture2, t2);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$$(j, p1, p2, param0, param1, r, t2, tmp, curDepth1, tmp1, stackDelayRes, curDepth, lscomp1$capture2, 45);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth1);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.Cons(r, tmp)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = new globalThis.Error("match error");
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$lscomp2$cryptarithm1$_mls_L0_869_962$$(j, p1, p2, param0, param1, r, t2, tmp, curDepth1, tmp1, stackDelayRes, curDepth, lscomp1$capture2, 46);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth1);
    throw tmp1;
  }
};
lscomp2 = function lscomp2(j, p1, curDepth, lscomp1$capture2) {
  return (p2) => {
    return lscomp2$(j, p1, curDepth, lscomp1$capture2, p2)
  }
};
lscomp1$capture1 = function lscomp1$capture(param00$1, param11$1, pjs2$1, t13$1, tmp4$1, tmp5$1, stackDelayRes6$1) {
  return new lscomp1$capture.class(param00$1, param11$1, pjs2$1, t13$1, tmp4$1, tmp5$1, stackDelayRes6$1);
};
lscomp1$capture1.class = class lscomp1$capture {
  constructor(param00$, param11$, pjs2$, t13$, tmp4$, tmp5$, stackDelayRes6$) {
    this.stackDelayRes6$ = stackDelayRes6$;
    this.tmp5$ = tmp5$;
    this.tmp4$ = tmp4$;
    this.t13$ = t13$;
    this.pjs2$ = pjs2$;
    this.param11$ = param11$;
    this.param00$ = param00$;
  }
  toString() { return "lscomp1$capture(" + globalThis.Predef.render(this.param00$) + ", " + globalThis.Predef.render(this.param11$) + ", " + globalThis.Predef.render(this.pjs2$) + ", " + globalThis.Predef.render(this.t13$) + ", " + globalThis.Predef.render(this.tmp4$) + ", " + globalThis.Predef.render(this.tmp5$) + ", " + globalThis.Predef.render(this.stackDelayRes6$) + ")"; }
};
lscomp1$ = function lscomp1$(j, p1) {
  let curDepth, capture;
  capture = new lscomp1$capture1(null, null, null, null, null, null, null);
  curDepth = runtime.stackDepth;
  capture.stackDelayRes6$ = runtime.checkDepth();
  if (capture.stackDelayRes6$ instanceof runtime.EffectSig.class) {
    capture.stackDelayRes6$.contTrace.last.next = Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$$(j, p1, curDepth, capture, 43);
    capture.stackDelayRes6$.contTrace.last = capture.stackDelayRes6$.contTrace.last.next;
    return capture.stackDelayRes6$
  }
  if (p1 instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (p1 instanceof NofibPrelude.Cons.class) {
    capture.param00$ = p1.head;
    capture.param11$ = p1.tail;
    capture.pjs2$ = capture.param00$;
    capture.t13$ = capture.param11$;
    runtime.stackDepth = runtime.stackDepth + 1;
    capture.tmp4$ = cryptarithm11.addj(j, capture.pjs2$);
    if (capture.tmp4$ instanceof runtime.EffectSig.class) {
      capture.tmp4$.contTrace.last.next = Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$$(j, p1, curDepth, capture, 51);
      capture.tmp4$.contTrace.last = capture.tmp4$.contTrace.last.next;
      return capture.tmp4$
    }
    capture.tmp4$ = runtime.resetDepth(capture.tmp4$, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return lscomp2$(j, p1, curDepth, capture, capture.tmp4$)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    capture.tmp5$ = new globalThis.Error("match error");
    if (capture.tmp5$ instanceof runtime.EffectSig.class) {
      capture.tmp5$.contTrace.last.next = Cont$func$lscomp1$cryptarithm1$_mls_L0_794_992$$(j, p1, curDepth, capture, 52);
      capture.tmp5$.contTrace.last = capture.tmp5$.contTrace.last.next;
      return capture.tmp5$
    }
    capture.tmp5$ = runtime.resetDepth(capture.tmp5$, curDepth);
    throw capture.tmp5$;
  }
};
lscomp1 = function lscomp1(j) {
  return (p1) => {
    return lscomp1$(j, p1)
  }
};
Cont$func$addj$cryptarithm1$_mls_L0_507_715$$ = function Cont$func$addj$cryptarithm1$_mls_L0_507_715$$(j$0, ls$1, param0$2, param1$3, k$4, ks$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13, pc) {
  let tmp;
  tmp = new Cont$func$addj$cryptarithm1$_mls_L0_507_715$1.class(pc);
  return tmp(j$0, ls$1, param0$2, param1$3, k$4, ks$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13)
};
Cont$func$addj$cryptarithm1$_mls_L0_507_715$$ctor = function Cont$func$addj$cryptarithm1$_mls_L0_507_715$$ctor(j$0, ls$1, param0$2, param1$3, k$4, ks$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$addj$cryptarithm1$_mls_L0_507_715$1.class(pc);
    return tmp(j$0, ls$1, param0$2, param1$3, k$4, ks$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13)
  }
};
Cont$func$addj$cryptarithm1$_mls_L0_507_715$1 = function Cont$func$addj$cryptarithm1$_mls_L0_507_715$(pc1) {
  return (j$01, ls$11, param0$21, param1$31, k$41, ks$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, curDepth$111, tmp$121, stackDelayRes$131) => {
    return new Cont$func$addj$cryptarithm1$_mls_L0_507_715$.class(pc1)(j$01, ls$11, param0$21, param1$31, k$41, ks$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, curDepth$111, tmp$121, stackDelayRes$131);
  }
};
Cont$func$addj$cryptarithm1$_mls_L0_507_715$1.class = class Cont$func$addj$cryptarithm1$_mls_L0_507_715$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (j$0, ls$1, param0$2, param1$3, k$4, ks$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13) => {
      let tmp;
      tmp = super(null);
      this.j$0 = j$0;
      this.ls$1 = ls$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.k$4 = k$4;
      this.ks$5 = ks$5;
      this.tmp$6 = tmp$6;
      this.tmp$7 = tmp$7;
      this.tmp$8 = tmp$8;
      this.tmp$9 = tmp$9;
      this.tmp$10 = tmp$10;
      this.curDepth$11 = curDepth$11;
      this.tmp$12 = tmp$12;
      this.stackDelayRes$13 = stackDelayRes$13;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 19) {
      this.stackDelayRes$13 = value$;
    } else if (this.pc === 33) {
      this.tmp$12 = value$;
    } else if (this.pc === 29) {
      this.tmp$7 = value$;
    } else if (this.pc === 30) {
      this.tmp$8 = value$;
    } else if (this.pc === 31) {
      this.tmp$9 = value$;
    } else if (this.pc === 32) {
      this.tmp$10 = value$;
    } else if (this.pc === 20) {
      this.tmp$6 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 19) {
        if (this.ls$1 instanceof NofibPrelude.Nil.class) {
          this.pc = 36;
          continue contLoop;
        } else if (this.ls$1 instanceof NofibPrelude.Cons.class) {
          this.param0$2 = this.ls$1.head;
          this.param1$3 = this.ls$1.tail;
          this.k$4 = this.param0$2;
          this.ks$5 = this.param1$3;
          this.pc = 41;
          continue contLoop;
          this.pc = 34;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$12 = new globalThis.Error("match error");
          if (this.tmp$12 instanceof runtime.EffectSig.class) {
            this.pc = 33;
            this.tmp$12.contTrace.last.next = this;
            this.tmp$12.contTrace.last = this;
            return this.tmp$12
          }
          this.pc = 33;
          continue contLoop;
        }
        this.pc = 34;
        continue contLoop;
      } else if (this.pc === 34) {
        break contLoop;
      } else if (this.pc === 33) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$11);
        throw this.tmp$12;
      } else if (this.pc === 37) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.tmp$8, this.tmp$10)
      } else if (this.pc === 40) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = NofibPrelude.Cons(this.j$0, this.tmp$7);
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 30;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 30;
        continue contLoop;
      } else if (this.pc === 41) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = NofibPrelude.Cons(this.k$4, this.ks$5);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 29;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 29;
        continue contLoop;
      } else if (this.pc === 29) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$11);
        this.pc = 40;
        continue contLoop;
      } else if (this.pc === 30) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$11);
        this.pc = 39;
        continue contLoop;
      } else if (this.pc === 38) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$10 = lscomp$(this.k$4, this.tmp$9);
        if (this.tmp$10 instanceof runtime.EffectSig.class) {
          this.pc = 32;
          this.tmp$10.contTrace.last.next = this;
          this.tmp$10.contTrace.last = this;
          return this.tmp$10
        }
        this.pc = 32;
        continue contLoop;
      } else if (this.pc === 39) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = cryptarithm11.addj(this.j$0, this.ks$5);
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 31;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 31;
        continue contLoop;
      } else if (this.pc === 31) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$11);
        this.pc = 38;
        continue contLoop;
      } else if (this.pc === 32) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$11);
        this.pc = 37;
        continue contLoop;
      } else if (this.pc === 35) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.tmp$6, NofibPrelude.Nil)
      } else if (this.pc === 36) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = NofibPrelude.Cons(this.j$0, NofibPrelude.Nil);
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 20;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 20;
        continue contLoop;
      } else if (this.pc === 20) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$11);
        this.pc = 35;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$addj$cryptarithm1$_mls_L0_507_715$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$$ = function Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$$(k$0, p1$1, param0$2, param1$3, h1$4, t1$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10, pc) {
  let tmp;
  tmp = new Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$1.class(pc);
  return tmp(k$0, p1$1, param0$2, param1$3, h1$4, t1$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
};
Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$$ctor = function Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$$ctor(k$0, p1$1, param0$2, param1$3, h1$4, t1$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$1.class(pc);
    return tmp(k$0, p1$1, param0$2, param1$3, h1$4, t1$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
  }
};
Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$1 = function Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$(pc1) {
  return (k$01, p1$11, param0$21, param1$31, h1$41, t1$51, tmp$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101) => {
    return new Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$.class(pc1)(k$01, p1$11, param0$21, param1$31, h1$41, t1$51, tmp$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101);
  }
};
Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$1.class = class Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (k$0, p1$1, param0$2, param1$3, h1$4, t1$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) => {
      let tmp;
      tmp = super(null);
      this.k$0 = k$0;
      this.p1$1 = p1$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.h1$4 = h1$4;
      this.t1$5 = t1$5;
      this.tmp$6 = tmp$6;
      this.tmp$7 = tmp$7;
      this.curDepth$8 = curDepth$8;
      this.tmp$9 = tmp$9;
      this.stackDelayRes$10 = stackDelayRes$10;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 21) {
      this.stackDelayRes$10 = value$;
    } else if (this.pc === 24) {
      this.tmp$9 = value$;
    } else if (this.pc === 22) {
      this.tmp$6 = value$;
    } else if (this.pc === 23) {
      this.tmp$7 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 21) {
        if (this.p1$1 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (this.p1$1 instanceof NofibPrelude.Cons.class) {
          this.param0$2 = this.p1$1.head;
          this.param1$3 = this.p1$1.tail;
          this.h1$4 = this.param0$2;
          this.t1$5 = this.param1$3;
          this.pc = 28;
          continue contLoop;
          this.pc = 25;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$9 = new globalThis.Error("match error");
          if (this.tmp$9 instanceof runtime.EffectSig.class) {
            this.pc = 24;
            this.tmp$9.contTrace.last.next = this;
            this.tmp$9.contTrace.last = this;
            return this.tmp$9
          }
          this.pc = 24;
          continue contLoop;
        }
        this.pc = 25;
        continue contLoop;
      } else if (this.pc === 25) {
        break contLoop;
      } else if (this.pc === 24) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$8);
        throw this.tmp$9;
      } else if (this.pc === 26) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.tmp$6, this.tmp$7)
      } else if (this.pc === 28) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = NofibPrelude.Cons(this.k$0, this.h1$4);
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 22;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 22;
        continue contLoop;
      } else if (this.pc === 22) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$8);
        this.pc = 27;
        continue contLoop;
      } else if (this.pc === 27) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = lscomp$(this.k$0, this.t1$5);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 23;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 23;
        continue contLoop;
      } else if (this.pc === 23) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$8);
        this.pc = 26;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lscomp$ = function lscomp$(k, p1) {
  let param0, param1, h1, t1, tmp, tmp1, curDepth, tmp2, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$$(k, p1, param0, param1, h1, t1, tmp, tmp1, curDepth, tmp2, stackDelayRes, 21);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (p1 instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (p1 instanceof NofibPrelude.Cons.class) {
    param0 = p1.head;
    param1 = p1.tail;
    h1 = param0;
    t1 = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = NofibPrelude.Cons(k, h1);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$$(k, p1, param0, param1, h1, t1, tmp, tmp1, curDepth, tmp2, stackDelayRes, 22);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = lscomp$(k, t1);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$$(k, p1, param0, param1, h1, t1, tmp, tmp1, curDepth, tmp2, stackDelayRes, 23);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.Cons(tmp, tmp1)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = new globalThis.Error("match error");
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$lscomp$cryptarithm1$_mls_L0_582_666$$(k, p1, param0, param1, h1, t1, tmp, tmp1, curDepth, tmp2, stackDelayRes, 24);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    throw tmp2;
  }
};
lscomp = function lscomp(k) {
  return (p1) => {
    return lscomp$(k, p1)
  }
};
Cont$func$condition$cryptarithm1$_mls_L0_310_501$$ = function Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn$0, param0$1, param1$2, t$3, param0$4, param1$5, h$6, param0$7, param1$8, i$9, param0$10, param1$11, r$12, param0$13, param1$14, y$15, param0$16, param1$17, w$18, param0$19, param1$20, e$21, param0$22, param1$23, l$24, param0$25, param1$26, v$27, param0$28, param1$29, n$30, tmp$31, tmp$32, tmp$33, tmp$34, tmp$35, curDepth$36, tmp$37, tmp$38, tmp$39, tmp$40, tmp$41, tmp$42, tmp$43, tmp$44, tmp$45, tmp$46, tmp$47, stackDelayRes$48, pc) {
  let tmp;
  tmp = new Cont$func$condition$cryptarithm1$_mls_L0_310_501$1.class(pc);
  return tmp(thirywelvn$0, param0$1, param1$2, t$3, param0$4, param1$5, h$6, param0$7, param1$8, i$9, param0$10, param1$11, r$12, param0$13, param1$14, y$15, param0$16, param1$17, w$18, param0$19, param1$20, e$21, param0$22, param1$23, l$24, param0$25, param1$26, v$27, param0$28, param1$29, n$30, tmp$31, tmp$32, tmp$33, tmp$34, tmp$35, curDepth$36, tmp$37, tmp$38, tmp$39, tmp$40, tmp$41, tmp$42, tmp$43, tmp$44, tmp$45, tmp$46, tmp$47, stackDelayRes$48)
};
Cont$func$condition$cryptarithm1$_mls_L0_310_501$$ctor = function Cont$func$condition$cryptarithm1$_mls_L0_310_501$$ctor(thirywelvn$0, param0$1, param1$2, t$3, param0$4, param1$5, h$6, param0$7, param1$8, i$9, param0$10, param1$11, r$12, param0$13, param1$14, y$15, param0$16, param1$17, w$18, param0$19, param1$20, e$21, param0$22, param1$23, l$24, param0$25, param1$26, v$27, param0$28, param1$29, n$30, tmp$31, tmp$32, tmp$33, tmp$34, tmp$35, curDepth$36, tmp$37, tmp$38, tmp$39, tmp$40, tmp$41, tmp$42, tmp$43, tmp$44, tmp$45, tmp$46, tmp$47, stackDelayRes$48) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$condition$cryptarithm1$_mls_L0_310_501$1.class(pc);
    return tmp(thirywelvn$0, param0$1, param1$2, t$3, param0$4, param1$5, h$6, param0$7, param1$8, i$9, param0$10, param1$11, r$12, param0$13, param1$14, y$15, param0$16, param1$17, w$18, param0$19, param1$20, e$21, param0$22, param1$23, l$24, param0$25, param1$26, v$27, param0$28, param1$29, n$30, tmp$31, tmp$32, tmp$33, tmp$34, tmp$35, curDepth$36, tmp$37, tmp$38, tmp$39, tmp$40, tmp$41, tmp$42, tmp$43, tmp$44, tmp$45, tmp$46, tmp$47, stackDelayRes$48)
  }
};
Cont$func$condition$cryptarithm1$_mls_L0_310_501$1 = function Cont$func$condition$cryptarithm1$_mls_L0_310_501$(pc1) {
  return (thirywelvn$01, param0$11, param1$21, t$31, param0$41, param1$51, h$61, param0$71, param1$81, i$91, param0$101, param1$111, r$121, param0$131, param1$141, y$151, param0$161, param1$171, w$181, param0$191, param1$201, e$211, param0$221, param1$231, l$241, param0$251, param1$261, v$271, param0$281, param1$291, n$301, tmp$311, tmp$321, tmp$331, tmp$341, tmp$351, curDepth$361, tmp$371, tmp$381, tmp$391, tmp$401, tmp$411, tmp$421, tmp$431, tmp$441, tmp$451, tmp$461, tmp$471, stackDelayRes$481) => {
    return new Cont$func$condition$cryptarithm1$_mls_L0_310_501$.class(pc1)(thirywelvn$01, param0$11, param1$21, t$31, param0$41, param1$51, h$61, param0$71, param1$81, i$91, param0$101, param1$111, r$121, param0$131, param1$141, y$151, param0$161, param1$171, w$181, param0$191, param1$201, e$211, param0$221, param1$231, l$241, param0$251, param1$261, v$271, param0$281, param1$291, n$301, tmp$311, tmp$321, tmp$331, tmp$341, tmp$351, curDepth$361, tmp$371, tmp$381, tmp$391, tmp$401, tmp$411, tmp$421, tmp$431, tmp$441, tmp$451, tmp$461, tmp$471, stackDelayRes$481);
  }
};
Cont$func$condition$cryptarithm1$_mls_L0_310_501$1.class = class Cont$func$condition$cryptarithm1$_mls_L0_310_501$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (thirywelvn$0, param0$1, param1$2, t$3, param0$4, param1$5, h$6, param0$7, param1$8, i$9, param0$10, param1$11, r$12, param0$13, param1$14, y$15, param0$16, param1$17, w$18, param0$19, param1$20, e$21, param0$22, param1$23, l$24, param0$25, param1$26, v$27, param0$28, param1$29, n$30, tmp$31, tmp$32, tmp$33, tmp$34, tmp$35, curDepth$36, tmp$37, tmp$38, tmp$39, tmp$40, tmp$41, tmp$42, tmp$43, tmp$44, tmp$45, tmp$46, tmp$47, stackDelayRes$48) => {
      let tmp;
      tmp = super(null);
      this.thirywelvn$0 = thirywelvn$0;
      this.param0$1 = param0$1;
      this.param1$2 = param1$2;
      this.t$3 = t$3;
      this.param0$4 = param0$4;
      this.param1$5 = param1$5;
      this.h$6 = h$6;
      this.param0$7 = param0$7;
      this.param1$8 = param1$8;
      this.i$9 = i$9;
      this.param0$10 = param0$10;
      this.param1$11 = param1$11;
      this.r$12 = r$12;
      this.param0$13 = param0$13;
      this.param1$14 = param1$14;
      this.y$15 = y$15;
      this.param0$16 = param0$16;
      this.param1$17 = param1$17;
      this.w$18 = w$18;
      this.param0$19 = param0$19;
      this.param1$20 = param1$20;
      this.e$21 = e$21;
      this.param0$22 = param0$22;
      this.param1$23 = param1$23;
      this.l$24 = l$24;
      this.param0$25 = param0$25;
      this.param1$26 = param1$26;
      this.v$27 = v$27;
      this.param0$28 = param0$28;
      this.param1$29 = param1$29;
      this.n$30 = n$30;
      this.tmp$31 = tmp$31;
      this.tmp$32 = tmp$32;
      this.tmp$33 = tmp$33;
      this.tmp$34 = tmp$34;
      this.tmp$35 = tmp$35;
      this.curDepth$36 = curDepth$36;
      this.tmp$37 = tmp$37;
      this.tmp$38 = tmp$38;
      this.tmp$39 = tmp$39;
      this.tmp$40 = tmp$40;
      this.tmp$41 = tmp$41;
      this.tmp$42 = tmp$42;
      this.tmp$43 = tmp$43;
      this.tmp$44 = tmp$44;
      this.tmp$45 = tmp$45;
      this.tmp$46 = tmp$46;
      this.tmp$47 = tmp$47;
      this.stackDelayRes$48 = stackDelayRes$48;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 0) {
      this.stackDelayRes$48 = value$;
    } else if (this.pc === 14) {
      this.tmp$47 = value$;
    } else if (this.pc === 13) {
      this.tmp$46 = value$;
    } else if (this.pc === 12) {
      this.tmp$45 = value$;
    } else if (this.pc === 11) {
      this.tmp$44 = value$;
    } else if (this.pc === 10) {
      this.tmp$43 = value$;
    } else if (this.pc === 9) {
      this.tmp$42 = value$;
    } else if (this.pc === 8) {
      this.tmp$41 = value$;
    } else if (this.pc === 7) {
      this.tmp$40 = value$;
    } else if (this.pc === 6) {
      this.tmp$39 = value$;
    } else if (this.pc === 5) {
      this.tmp$38 = value$;
    } else if (this.pc === 4) {
      this.tmp$37 = value$;
    } else if (this.pc === 1) {
      this.tmp$31 = value$;
    } else if (this.pc === 2) {
      this.tmp$32 = value$;
    } else if (this.pc === 3) {
      this.tmp$35 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 0) {
        if (this.thirywelvn$0 instanceof NofibPrelude.Cons.class) {
          this.param0$1 = this.thirywelvn$0.head;
          this.param1$2 = this.thirywelvn$0.tail;
          this.t$3 = this.param0$1;
          if (this.param1$2 instanceof NofibPrelude.Cons.class) {
            this.param0$4 = this.param1$2.head;
            this.param1$5 = this.param1$2.tail;
            this.h$6 = this.param0$4;
            if (this.param1$5 instanceof NofibPrelude.Cons.class) {
              this.param0$7 = this.param1$5.head;
              this.param1$8 = this.param1$5.tail;
              this.i$9 = this.param0$7;
              if (this.param1$8 instanceof NofibPrelude.Cons.class) {
                this.param0$10 = this.param1$8.head;
                this.param1$11 = this.param1$8.tail;
                this.r$12 = this.param0$10;
                if (this.param1$11 instanceof NofibPrelude.Cons.class) {
                  this.param0$13 = this.param1$11.head;
                  this.param1$14 = this.param1$11.tail;
                  this.y$15 = this.param0$13;
                  if (this.param1$14 instanceof NofibPrelude.Cons.class) {
                    this.param0$16 = this.param1$14.head;
                    this.param1$17 = this.param1$14.tail;
                    this.w$18 = this.param0$16;
                    if (this.param1$17 instanceof NofibPrelude.Cons.class) {
                      this.param0$19 = this.param1$17.head;
                      this.param1$20 = this.param1$17.tail;
                      this.e$21 = this.param0$19;
                      if (this.param1$20 instanceof NofibPrelude.Cons.class) {
                        this.param0$22 = this.param1$20.head;
                        this.param1$23 = this.param1$20.tail;
                        this.l$24 = this.param0$22;
                        if (this.param1$23 instanceof NofibPrelude.Cons.class) {
                          this.param0$25 = this.param1$23.head;
                          this.param1$26 = this.param1$23.tail;
                          this.v$27 = this.param0$25;
                          if (this.param1$26 instanceof NofibPrelude.Cons.class) {
                            this.param0$28 = this.param1$26.head;
                            this.param1$29 = this.param1$26.tail;
                            this.n$30 = this.param0$28;
                            if (this.param1$29 instanceof NofibPrelude.Nil.class) {
                              this.pc = 18;
                              continue contLoop;
                            } else {
                              runtime.stackDepth = runtime.stackDepth + 1;
                              this.tmp$37 = new globalThis.Error("match error");
                              if (this.tmp$37 instanceof runtime.EffectSig.class) {
                                this.pc = 4;
                                this.tmp$37.contTrace.last.next = this;
                                this.tmp$37.contTrace.last = this;
                                return this.tmp$37
                              }
                              this.pc = 4;
                              continue contLoop;
                            }
                            this.pc = 15;
                            continue contLoop;
                          } else {
                            runtime.stackDepth = runtime.stackDepth + 1;
                            this.tmp$38 = new globalThis.Error("match error");
                            if (this.tmp$38 instanceof runtime.EffectSig.class) {
                              this.pc = 5;
                              this.tmp$38.contTrace.last.next = this;
                              this.tmp$38.contTrace.last = this;
                              return this.tmp$38
                            }
                            this.pc = 5;
                            continue contLoop;
                          }
                          this.pc = 15;
                          continue contLoop;
                        } else {
                          runtime.stackDepth = runtime.stackDepth + 1;
                          this.tmp$39 = new globalThis.Error("match error");
                          if (this.tmp$39 instanceof runtime.EffectSig.class) {
                            this.pc = 6;
                            this.tmp$39.contTrace.last.next = this;
                            this.tmp$39.contTrace.last = this;
                            return this.tmp$39
                          }
                          this.pc = 6;
                          continue contLoop;
                        }
                        this.pc = 15;
                        continue contLoop;
                      } else {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        this.tmp$40 = new globalThis.Error("match error");
                        if (this.tmp$40 instanceof runtime.EffectSig.class) {
                          this.pc = 7;
                          this.tmp$40.contTrace.last.next = this;
                          this.tmp$40.contTrace.last = this;
                          return this.tmp$40
                        }
                        this.pc = 7;
                        continue contLoop;
                      }
                      this.pc = 15;
                      continue contLoop;
                    } else {
                      runtime.stackDepth = runtime.stackDepth + 1;
                      this.tmp$41 = new globalThis.Error("match error");
                      if (this.tmp$41 instanceof runtime.EffectSig.class) {
                        this.pc = 8;
                        this.tmp$41.contTrace.last.next = this;
                        this.tmp$41.contTrace.last = this;
                        return this.tmp$41
                      }
                      this.pc = 8;
                      continue contLoop;
                    }
                    this.pc = 15;
                    continue contLoop;
                  } else {
                    runtime.stackDepth = runtime.stackDepth + 1;
                    this.tmp$42 = new globalThis.Error("match error");
                    if (this.tmp$42 instanceof runtime.EffectSig.class) {
                      this.pc = 9;
                      this.tmp$42.contTrace.last.next = this;
                      this.tmp$42.contTrace.last = this;
                      return this.tmp$42
                    }
                    this.pc = 9;
                    continue contLoop;
                  }
                  this.pc = 15;
                  continue contLoop;
                } else {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  this.tmp$43 = new globalThis.Error("match error");
                  if (this.tmp$43 instanceof runtime.EffectSig.class) {
                    this.pc = 10;
                    this.tmp$43.contTrace.last.next = this;
                    this.tmp$43.contTrace.last = this;
                    return this.tmp$43
                  }
                  this.pc = 10;
                  continue contLoop;
                }
                this.pc = 15;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.tmp$44 = new globalThis.Error("match error");
                if (this.tmp$44 instanceof runtime.EffectSig.class) {
                  this.pc = 11;
                  this.tmp$44.contTrace.last.next = this;
                  this.tmp$44.contTrace.last = this;
                  return this.tmp$44
                }
                this.pc = 11;
                continue contLoop;
              }
              this.pc = 15;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.tmp$45 = new globalThis.Error("match error");
              if (this.tmp$45 instanceof runtime.EffectSig.class) {
                this.pc = 12;
                this.tmp$45.contTrace.last.next = this;
                this.tmp$45.contTrace.last = this;
                return this.tmp$45
              }
              this.pc = 12;
              continue contLoop;
            }
            this.pc = 15;
            continue contLoop;
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.tmp$46 = new globalThis.Error("match error");
            if (this.tmp$46 instanceof runtime.EffectSig.class) {
              this.pc = 13;
              this.tmp$46.contTrace.last.next = this;
              this.tmp$46.contTrace.last = this;
              return this.tmp$46
            }
            this.pc = 13;
            continue contLoop;
          }
          this.pc = 15;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$47 = new globalThis.Error("match error");
          if (this.tmp$47 instanceof runtime.EffectSig.class) {
            this.pc = 14;
            this.tmp$47.contTrace.last.next = this;
            this.tmp$47.contTrace.last = this;
            return this.tmp$47
          }
          this.pc = 14;
          continue contLoop;
        }
        this.pc = 15;
        continue contLoop;
      } else if (this.pc === 15) {
        break contLoop;
      } else if (this.pc === 14) {
        this.tmp$47 = runtime.resetDepth(this.tmp$47, this.curDepth$36);
        throw this.tmp$47;
      } else if (this.pc === 13) {
        this.tmp$46 = runtime.resetDepth(this.tmp$46, this.curDepth$36);
        throw this.tmp$46;
      } else if (this.pc === 12) {
        this.tmp$45 = runtime.resetDepth(this.tmp$45, this.curDepth$36);
        throw this.tmp$45;
      } else if (this.pc === 11) {
        this.tmp$44 = runtime.resetDepth(this.tmp$44, this.curDepth$36);
        throw this.tmp$44;
      } else if (this.pc === 10) {
        this.tmp$43 = runtime.resetDepth(this.tmp$43, this.curDepth$36);
        throw this.tmp$43;
      } else if (this.pc === 9) {
        this.tmp$42 = runtime.resetDepth(this.tmp$42, this.curDepth$36);
        throw this.tmp$42;
      } else if (this.pc === 8) {
        this.tmp$41 = runtime.resetDepth(this.tmp$41, this.curDepth$36);
        throw this.tmp$41;
      } else if (this.pc === 7) {
        this.tmp$40 = runtime.resetDepth(this.tmp$40, this.curDepth$36);
        throw this.tmp$40;
      } else if (this.pc === 6) {
        this.tmp$39 = runtime.resetDepth(this.tmp$39, this.curDepth$36);
        throw this.tmp$39;
      } else if (this.pc === 5) {
        this.tmp$38 = runtime.resetDepth(this.tmp$38, this.curDepth$36);
        throw this.tmp$38;
      } else if (this.pc === 4) {
        this.tmp$37 = runtime.resetDepth(this.tmp$37, this.curDepth$36);
        throw this.tmp$37;
      } else if (this.pc === 18) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$31 = cryptarithm11.expand(this.t$3, this.h$6, this.i$9, this.r$12, this.t$3, this.y$15);
        if (this.tmp$31 instanceof runtime.EffectSig.class) {
          this.pc = 1;
          this.tmp$31.contTrace.last.next = this;
          this.tmp$31.contTrace.last = this;
          return this.tmp$31
        }
        this.pc = 1;
        continue contLoop;
      } else if (this.pc === 1) {
        this.tmp$31 = runtime.resetDepth(this.tmp$31, this.curDepth$36);
        this.pc = 17;
        continue contLoop;
      } else if (this.pc === 17) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$32 = cryptarithm11.expand(this.t$3, this.w$18, this.e$21, this.l$24, this.v$27, this.e$21);
        if (this.tmp$32 instanceof runtime.EffectSig.class) {
          this.pc = 2;
          this.tmp$32.contTrace.last.next = this;
          this.tmp$32.contTrace.last = this;
          return this.tmp$32
        }
        this.pc = 2;
        continue contLoop;
      } else if (this.pc === 2) {
        this.tmp$32 = runtime.resetDepth(this.tmp$32, this.curDepth$36);
        this.tmp$33 = 5 * this.tmp$32;
        this.tmp$34 = this.tmp$31 + this.tmp$33;
        this.pc = 16;
        continue contLoop;
      } else if (this.pc === 16) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$35 = cryptarithm11.expand(this.n$30, this.i$9, this.n$30, this.e$21, this.t$3, this.y$15);
        if (this.tmp$35 instanceof runtime.EffectSig.class) {
          this.pc = 3;
          this.tmp$35.contTrace.last.next = this;
          this.tmp$35.contTrace.last = this;
          return this.tmp$35
        }
        this.pc = 3;
        continue contLoop;
      } else if (this.pc === 3) {
        this.tmp$35 = runtime.resetDepth(this.tmp$35, this.curDepth$36);
        return this.tmp$34 == this.tmp$35
      }
      break;
    }
  }
  toString() { return "Cont$func$condition$cryptarithm1$_mls_L0_310_501$(" + globalThis.Predef.render(this.pc) + ")"; }
};
cryptarithm11 = class cryptarithm1 {
  static {
    cryptarithm11 = cryptarithm1;
    let lambda1, res, lambda2;
    lambda1 = (undefined, function () {
      let tmp, curDepth, stackDelayRes;
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = Cont$func$lambda$$$(tmp, curDepth, stackDelayRes, 74);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = cryptarithm1.testCryptarithm_nofib(1);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$lambda$$$(tmp, curDepth, stackDelayRes, 75);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return BenchmarkPrelude.print(tmp)
    });
    lambda2 = (undefined, function () {
      return BenchmarkPrelude.benchmark(lambda1)
    });
    res = runtime.runStackSafe(500, lambda2);
    if (res instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    res
  }
  static expand(a, b, c, d, e, f) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    tmp = e * 10;
    tmp1 = f + tmp;
    tmp2 = d * 100;
    tmp3 = tmp1 + tmp2;
    tmp4 = c * 1000;
    tmp5 = tmp3 + tmp4;
    tmp6 = b * 10000;
    tmp7 = tmp5 + tmp6;
    tmp8 = a * 100000;
    return tmp7 + tmp8
  } 
  static condition(thirywelvn) {
    let param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 0);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    if (thirywelvn instanceof NofibPrelude.Cons.class) {
      param0 = thirywelvn.head;
      param1 = thirywelvn.tail;
      t = param0;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        h = param01;
        if (param11 instanceof NofibPrelude.Cons.class) {
          param02 = param11.head;
          param12 = param11.tail;
          i = param02;
          if (param12 instanceof NofibPrelude.Cons.class) {
            param03 = param12.head;
            param13 = param12.tail;
            r = param03;
            if (param13 instanceof NofibPrelude.Cons.class) {
              param04 = param13.head;
              param14 = param13.tail;
              y = param04;
              if (param14 instanceof NofibPrelude.Cons.class) {
                param05 = param14.head;
                param15 = param14.tail;
                w = param05;
                if (param15 instanceof NofibPrelude.Cons.class) {
                  param06 = param15.head;
                  param16 = param15.tail;
                  e1 = param06;
                  if (param16 instanceof NofibPrelude.Cons.class) {
                    param07 = param16.head;
                    param17 = param16.tail;
                    l = param07;
                    if (param17 instanceof NofibPrelude.Cons.class) {
                      param08 = param17.head;
                      param18 = param17.tail;
                      v = param08;
                      if (param18 instanceof NofibPrelude.Cons.class) {
                        param09 = param18.head;
                        param19 = param18.tail;
                        n = param09;
                        if (param19 instanceof NofibPrelude.Nil.class) {
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp = cryptarithm1.expand(t, h, i, r, t, y);
                          if (tmp instanceof runtime.EffectSig.class) {
                            tmp.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 1);
                            tmp.contTrace.last = tmp.contTrace.last.next;
                            return tmp
                          }
                          tmp = runtime.resetDepth(tmp, curDepth);
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp1 = cryptarithm1.expand(t, w, e1, l, v, e1);
                          if (tmp1 instanceof runtime.EffectSig.class) {
                            tmp1.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 2);
                            tmp1.contTrace.last = tmp1.contTrace.last.next;
                            return tmp1
                          }
                          tmp1 = runtime.resetDepth(tmp1, curDepth);
                          tmp2 = 5 * tmp1;
                          tmp3 = tmp + tmp2;
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp4 = cryptarithm1.expand(n, i, n, e1, t, y);
                          if (tmp4 instanceof runtime.EffectSig.class) {
                            tmp4.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 3);
                            tmp4.contTrace.last = tmp4.contTrace.last.next;
                            return tmp4
                          }
                          tmp4 = runtime.resetDepth(tmp4, curDepth);
                          return tmp3 == tmp4
                        } else {
                          runtime.stackDepth = runtime.stackDepth + 1;
                          tmp5 = new globalThis.Error("match error");
                          if (tmp5 instanceof runtime.EffectSig.class) {
                            tmp5.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 4);
                            tmp5.contTrace.last = tmp5.contTrace.last.next;
                            return tmp5
                          }
                          tmp5 = runtime.resetDepth(tmp5, curDepth);
                          throw tmp5;
                        }
                      } else {
                        runtime.stackDepth = runtime.stackDepth + 1;
                        tmp6 = new globalThis.Error("match error");
                        if (tmp6 instanceof runtime.EffectSig.class) {
                          tmp6.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 5);
                          tmp6.contTrace.last = tmp6.contTrace.last.next;
                          return tmp6
                        }
                        tmp6 = runtime.resetDepth(tmp6, curDepth);
                        throw tmp6;
                      }
                    } else {
                      runtime.stackDepth = runtime.stackDepth + 1;
                      tmp7 = new globalThis.Error("match error");
                      if (tmp7 instanceof runtime.EffectSig.class) {
                        tmp7.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 6);
                        tmp7.contTrace.last = tmp7.contTrace.last.next;
                        return tmp7
                      }
                      tmp7 = runtime.resetDepth(tmp7, curDepth);
                      throw tmp7;
                    }
                  } else {
                    runtime.stackDepth = runtime.stackDepth + 1;
                    tmp8 = new globalThis.Error("match error");
                    if (tmp8 instanceof runtime.EffectSig.class) {
                      tmp8.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 7);
                      tmp8.contTrace.last = tmp8.contTrace.last.next;
                      return tmp8
                    }
                    tmp8 = runtime.resetDepth(tmp8, curDepth);
                    throw tmp8;
                  }
                } else {
                  runtime.stackDepth = runtime.stackDepth + 1;
                  tmp9 = new globalThis.Error("match error");
                  if (tmp9 instanceof runtime.EffectSig.class) {
                    tmp9.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 8);
                    tmp9.contTrace.last = tmp9.contTrace.last.next;
                    return tmp9
                  }
                  tmp9 = runtime.resetDepth(tmp9, curDepth);
                  throw tmp9;
                }
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp10 = new globalThis.Error("match error");
                if (tmp10 instanceof runtime.EffectSig.class) {
                  tmp10.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 9);
                  tmp10.contTrace.last = tmp10.contTrace.last.next;
                  return tmp10
                }
                tmp10 = runtime.resetDepth(tmp10, curDepth);
                throw tmp10;
              }
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp11 = new globalThis.Error("match error");
              if (tmp11 instanceof runtime.EffectSig.class) {
                tmp11.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 10);
                tmp11.contTrace.last = tmp11.contTrace.last.next;
                return tmp11
              }
              tmp11 = runtime.resetDepth(tmp11, curDepth);
              throw tmp11;
            }
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp12 = new globalThis.Error("match error");
            if (tmp12 instanceof runtime.EffectSig.class) {
              tmp12.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 11);
              tmp12.contTrace.last = tmp12.contTrace.last.next;
              return tmp12
            }
            tmp12 = runtime.resetDepth(tmp12, curDepth);
            throw tmp12;
          }
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp13 = new globalThis.Error("match error");
          if (tmp13 instanceof runtime.EffectSig.class) {
            tmp13.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 12);
            tmp13.contTrace.last = tmp13.contTrace.last.next;
            return tmp13
          }
          tmp13 = runtime.resetDepth(tmp13, curDepth);
          throw tmp13;
        }
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp14 = new globalThis.Error("match error");
        if (tmp14 instanceof runtime.EffectSig.class) {
          tmp14.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 13);
          tmp14.contTrace.last = tmp14.contTrace.last.next;
          return tmp14
        }
        tmp14 = runtime.resetDepth(tmp14, curDepth);
        throw tmp14;
      }
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp15 = new globalThis.Error("match error");
      if (tmp15 instanceof runtime.EffectSig.class) {
        tmp15.contTrace.last.next = Cont$func$condition$cryptarithm1$_mls_L0_310_501$$(thirywelvn, param0, param1, t, param01, param11, h, param02, param12, i, param03, param13, r, param04, param14, y, param05, param15, w, param06, param16, e1, param07, param17, l, param08, param18, v, param09, param19, n, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, stackDelayRes, 14);
        tmp15.contTrace.last = tmp15.contTrace.last.next;
        return tmp15
      }
      tmp15 = runtime.resetDepth(tmp15, curDepth);
      throw tmp15;
    }
  } 
  static addj(j, ls) {
    let param0, param1, k, ks, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$addj$cryptarithm1$_mls_L0_507_715$$(j, ls, param0, param1, k, ks, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 19);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    if (ls instanceof NofibPrelude.Nil.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = NofibPrelude.Cons(j, NofibPrelude.Nil);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$addj$cryptarithm1$_mls_L0_507_715$$(j, ls, param0, param1, k, ks, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 20);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.Cons(tmp, NofibPrelude.Nil)
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      k = param0;
      ks = param1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = NofibPrelude.Cons(k, ks);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = Cont$func$addj$cryptarithm1$_mls_L0_507_715$$(j, ls, param0, param1, k, ks, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 29);
        tmp1.contTrace.last = tmp1.contTrace.last.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = NofibPrelude.Cons(j, tmp1);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.contTrace.last.next = Cont$func$addj$cryptarithm1$_mls_L0_507_715$$(j, ls, param0, param1, k, ks, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 30);
        tmp2.contTrace.last = tmp2.contTrace.last.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = cryptarithm1.addj(j, ks);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.contTrace.last.next = Cont$func$addj$cryptarithm1$_mls_L0_507_715$$(j, ls, param0, param1, k, ks, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 31);
        tmp3.contTrace.last = tmp3.contTrace.last.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = lscomp$(k, tmp3);
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.contTrace.last.next = Cont$func$addj$cryptarithm1$_mls_L0_507_715$$(j, ls, param0, param1, k, ks, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 32);
        tmp4.contTrace.last = tmp4.contTrace.last.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.Cons(tmp2, tmp4)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp5 = new globalThis.Error("match error");
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.contTrace.last.next = Cont$func$addj$cryptarithm1$_mls_L0_507_715$$(j, ls, param0, param1, k, ks, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 33);
        tmp5.contTrace.last = tmp5.contTrace.last.next;
        return tmp5
      }
      tmp5 = runtime.resetDepth(tmp5, curDepth);
      throw tmp5;
    }
  } 
  static permutations(ls1) {
    let param0, param1, j1, js, tmp, curDepth, tmp1, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$$(ls1, param0, param1, j1, js, tmp, curDepth, tmp1, stackDelayRes, 42);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    if (ls1 instanceof NofibPrelude.Nil.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil)
    } else if (ls1 instanceof NofibPrelude.Cons.class) {
      param0 = ls1.head;
      param1 = ls1.tail;
      j1 = param0;
      js = param1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = cryptarithm1.permutations(js);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$$(ls1, param0, param1, j1, js, tmp, curDepth, tmp1, stackDelayRes, 56);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return lscomp1$(j1, tmp)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = new globalThis.Error("match error");
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = Cont$func$permutations$cryptarithm1$_mls_L0_721_1027$$(ls1, param0, param1, j1, js, tmp, curDepth, tmp1, stackDelayRes, 57);
        tmp1.contTrace.last = tmp1.contTrace.last.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      throw tmp1;
    }
  } 
  static testCryptarithm_nofib(n) {
    let tmp, tmp1, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$$(n, tmp, tmp1, curDepth, stackDelayRes, 62);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    tmp = lambda;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = NofibPrelude.enumFromTo(1, n);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$testCryptarithm_nofib$cryptarithm1$_mls_L0_1033_1171$$(n, tmp, tmp1, curDepth, stackDelayRes, 71);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.map(tmp, tmp1)
  }
  static toString() { return "cryptarithm1"; }
};
let cryptarithm1 = cryptarithm11; export default cryptarithm1;
