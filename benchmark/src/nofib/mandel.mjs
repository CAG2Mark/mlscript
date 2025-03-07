import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let infiniteMandel, walkIt, lscomp2, windowToViewport, lscomp1, prettyRGB, mandel_, comp_times, Complex1, comp_plus, comp_magnitude, mandelset, testMandel_nofib, whenDiverge, parallelMandel, createPixmap, Pixmap1, diverge, lambda, lambda1, lambda2, lambda3, res, Cont$func$createPixmap$mandel$_mls_L0_195_274$1, Cont$func$comp_magnitude$mandel$_mls_L0_311_377$1, Cont$func$comp_times$mandel$_mls_L0_383_499$1, Cont$func$comp_plus$mandel$_mls_L0_505_596$1, Cont$func$lambda$$4, Cont$func$lambda$$5, Cont$func$infiniteMandel$mandel$_mls_L0_621_650$1, Cont$func$mandel_$mandel$_mls_L0_602_751$1, Cont$func$diverge$mandel$_mls_L0_757_814$1, Cont$func$walkIt$mandel$_mls_L0_858_983$1, Cont$func$whenDiverge$mandel$_mls_L0_820_1026$1, Cont$func$lambda$$6, Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$1, Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$1, Cont$func$lscomp2$mandel$_mls_L0_1415_1527$1, Cont$func$lscomp1$mandel$_mls_L0_1346_1565$1, Cont$func$mandelset$mandel$_mls_L0_1119_1730$1, Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$1, Cont$func$lambda$$7, lambda4, Cont$func$createPixmap$mandel$_mls_L0_195_274$$ctor, Cont$func$createPixmap$mandel$_mls_L0_195_274$$, Cont$func$comp_magnitude$mandel$_mls_L0_311_377$$ctor, Cont$func$comp_magnitude$mandel$_mls_L0_311_377$$, Cont$func$comp_times$mandel$_mls_L0_383_499$$ctor, Cont$func$comp_times$mandel$_mls_L0_383_499$$, Cont$func$comp_plus$mandel$_mls_L0_505_596$$ctor, Cont$func$comp_plus$mandel$_mls_L0_505_596$$, infiniteMandel$, lambda$, lambda$1, Cont$func$lambda$$$ctor, Cont$func$lambda$$$, Cont$func$lambda$$$ctor1, Cont$func$lambda$$$1, Cont$func$infiniteMandel$mandel$_mls_L0_621_650$$ctor, Cont$func$infiniteMandel$mandel$_mls_L0_621_650$$, Cont$func$mandel_$mandel$_mls_L0_602_751$$ctor, Cont$func$mandel_$mandel$_mls_L0_602_751$$, infiniteMandel$capture1, Cont$func$diverge$mandel$_mls_L0_757_814$$ctor, Cont$func$diverge$mandel$_mls_L0_757_814$$, walkIt$, Cont$func$walkIt$mandel$_mls_L0_858_983$$ctor, Cont$func$walkIt$mandel$_mls_L0_858_983$$, Cont$func$whenDiverge$mandel$_mls_L0_820_1026$$ctor, Cont$func$whenDiverge$mandel$_mls_L0_820_1026$$, lambda$2, Cont$func$lambda$$$ctor2, Cont$func$lambda$$$2, Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$$ctor, Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$$, lscomp1$, lscomp2$, Cont$func$lscomp2$mandel$_mls_L0_1415_1527$$ctor, Cont$func$lscomp2$mandel$_mls_L0_1415_1527$$, Cont$func$lscomp1$mandel$_mls_L0_1346_1565$$ctor, Cont$func$lscomp1$mandel$_mls_L0_1346_1565$$, windowToViewport$, Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$$ctor, Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$$, prettyRGB$, Cont$func$mandelset$mandel$_mls_L0_1119_1730$$ctor, Cont$func$mandelset$mandel$_mls_L0_1119_1730$$, lscomp1$capture1, Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$$ctor, Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$$, Cont$func$lambda$$$ctor3, Cont$func$lambda$$$3;
Cont$func$createPixmap$mandel$_mls_L0_195_274$$ = function Cont$func$createPixmap$mandel$_mls_L0_195_274$$(width$0, height$1, max$2, colours$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$createPixmap$mandel$_mls_L0_195_274$1.class(pc);
  return tmp(width$0, height$1, max$2, colours$3, stackDelayRes$4)
};
Cont$func$createPixmap$mandel$_mls_L0_195_274$$ctor = function Cont$func$createPixmap$mandel$_mls_L0_195_274$$ctor(width$0, height$1, max$2, colours$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$createPixmap$mandel$_mls_L0_195_274$1.class(pc);
    return tmp(width$0, height$1, max$2, colours$3, stackDelayRes$4)
  }
};
Cont$func$createPixmap$mandel$_mls_L0_195_274$1 = function Cont$func$createPixmap$mandel$_mls_L0_195_274$(pc1) {
  return (width$01, height$11, max$21, colours$31, stackDelayRes$41) => {
    return new Cont$func$createPixmap$mandel$_mls_L0_195_274$.class(pc1)(width$01, height$11, max$21, colours$31, stackDelayRes$41);
  }
};
Cont$func$createPixmap$mandel$_mls_L0_195_274$1.class = class Cont$func$createPixmap$mandel$_mls_L0_195_274$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (width$0, height$1, max$2, colours$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.width$0 = width$0;
      this.height$1 = height$1;
      this.max$2 = max$2;
      this.colours$3 = colours$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 0) {
      this.stackDelayRes$4 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 0) {
        this.pc = 1;
        continue contLoop;
      } else if (this.pc === 1) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Pixmap1(this.width$0, this.height$1, this.max$2, this.colours$3)
      }
      break;
    }
  }
  toString() { return "Cont$func$createPixmap$mandel$_mls_L0_195_274$(" + globalThis.Predef.render(this.pc) + ")"; }
};
createPixmap = function createPixmap(width, height, max, colours) {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$createPixmap$mandel$_mls_L0_195_274$$(width, height, max, colours, stackDelayRes, 0);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return Pixmap1(width, height, max, colours)
};
Cont$func$comp_magnitude$mandel$_mls_L0_311_377$$ = function Cont$func$comp_magnitude$mandel$_mls_L0_311_377$$(c$0, param0$1, param1$2, a$3, b$4, tmp$5, tmp$6, tmp$7, tmp$8, curDepth$9, stackDelayRes$10, pc) {
  let tmp;
  tmp = new Cont$func$comp_magnitude$mandel$_mls_L0_311_377$1.class(pc);
  return tmp(c$0, param0$1, param1$2, a$3, b$4, tmp$5, tmp$6, tmp$7, tmp$8, curDepth$9, stackDelayRes$10)
};
Cont$func$comp_magnitude$mandel$_mls_L0_311_377$$ctor = function Cont$func$comp_magnitude$mandel$_mls_L0_311_377$$ctor(c$0, param0$1, param1$2, a$3, b$4, tmp$5, tmp$6, tmp$7, tmp$8, curDepth$9, stackDelayRes$10) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$comp_magnitude$mandel$_mls_L0_311_377$1.class(pc);
    return tmp(c$0, param0$1, param1$2, a$3, b$4, tmp$5, tmp$6, tmp$7, tmp$8, curDepth$9, stackDelayRes$10)
  }
};
Cont$func$comp_magnitude$mandel$_mls_L0_311_377$1 = function Cont$func$comp_magnitude$mandel$_mls_L0_311_377$(pc1) {
  return (c$01, param0$11, param1$21, a$31, b$41, tmp$51, tmp$61, tmp$71, tmp$81, curDepth$91, stackDelayRes$101) => {
    return new Cont$func$comp_magnitude$mandel$_mls_L0_311_377$.class(pc1)(c$01, param0$11, param1$21, a$31, b$41, tmp$51, tmp$61, tmp$71, tmp$81, curDepth$91, stackDelayRes$101);
  }
};
Cont$func$comp_magnitude$mandel$_mls_L0_311_377$1.class = class Cont$func$comp_magnitude$mandel$_mls_L0_311_377$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (c$0, param0$1, param1$2, a$3, b$4, tmp$5, tmp$6, tmp$7, tmp$8, curDepth$9, stackDelayRes$10) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.c$0 = c$0;
      this.param0$1 = param0$1;
      this.param1$2 = param1$2;
      this.a$3 = a$3;
      this.b$4 = b$4;
      this.tmp$5 = tmp$5;
      this.tmp$6 = tmp$6;
      this.tmp$7 = tmp$7;
      this.tmp$8 = tmp$8;
      this.curDepth$9 = curDepth$9;
      this.stackDelayRes$10 = stackDelayRes$10;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 2) {
      this.stackDelayRes$10 = value$;
    } else if (this.pc === 3) {
      this.tmp$8 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 2) {
        if (this.c$0 instanceof Complex1.class) {
          this.param0$1 = this.c$0.r;
          this.param1$2 = this.c$0.i;
          this.a$3 = this.param0$1;
          this.b$4 = this.param1$2;
          this.tmp$5 = this.a$3 * this.a$3;
          this.tmp$6 = this.b$4 * this.b$4;
          this.tmp$7 = this.tmp$5 + this.tmp$6;
          this.pc = 5;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$8 = new globalThis.Error("match error");
          if (this.tmp$8 instanceof runtime.EffectSig.class) {
            this.pc = 3;
            this.tmp$8.contTrace.last.next = this;
            this.tmp$8.contTrace.last = this;
            return this.tmp$8
          }
          this.pc = 3;
          continue contLoop;
        }
        this.pc = 4;
        continue contLoop;
      } else if (this.pc === 4) {
        break contLoop;
      } else if (this.pc === 3) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$9);
        throw this.tmp$8;
      } else if (this.pc === 5) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.sqrt(this.tmp$7)
      }
      break;
    }
  }
  toString() { return "Cont$func$comp_magnitude$mandel$_mls_L0_311_377$(" + globalThis.Predef.render(this.pc) + ")"; }
};
comp_magnitude = function comp_magnitude(c) {
  let param0, param1, a, b, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$comp_magnitude$mandel$_mls_L0_311_377$$(c, param0, param1, a, b, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 2);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (c instanceof Complex1.class) {
    param0 = c.r;
    param1 = c.i;
    a = param0;
    b = param1;
    tmp = a * a;
    tmp1 = b * b;
    tmp2 = tmp + tmp1;
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.sqrt(tmp2)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp3 = new globalThis.Error("match error");
    if (tmp3 instanceof runtime.EffectSig.class) {
      tmp3.contTrace.last.next = Cont$func$comp_magnitude$mandel$_mls_L0_311_377$$(c, param0, param1, a, b, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 3);
      tmp3.contTrace.last = tmp3.contTrace.last.next;
      return tmp3
    }
    tmp3 = runtime.resetDepth(tmp3, curDepth);
    throw tmp3;
  }
};
Cont$func$comp_times$mandel$_mls_L0_383_499$$ = function Cont$func$comp_times$mandel$_mls_L0_383_499$$(x$0, y$1, param0$2, param1$3, a$4, b$5, param0$6, param1$7, c$8, d$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, stackDelayRes$19, pc) {
  let tmp;
  tmp = new Cont$func$comp_times$mandel$_mls_L0_383_499$1.class(pc);
  return tmp(x$0, y$1, param0$2, param1$3, a$4, b$5, param0$6, param1$7, c$8, d$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, stackDelayRes$19)
};
Cont$func$comp_times$mandel$_mls_L0_383_499$$ctor = function Cont$func$comp_times$mandel$_mls_L0_383_499$$ctor(x$0, y$1, param0$2, param1$3, a$4, b$5, param0$6, param1$7, c$8, d$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, stackDelayRes$19) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$comp_times$mandel$_mls_L0_383_499$1.class(pc);
    return tmp(x$0, y$1, param0$2, param1$3, a$4, b$5, param0$6, param1$7, c$8, d$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, stackDelayRes$19)
  }
};
Cont$func$comp_times$mandel$_mls_L0_383_499$1 = function Cont$func$comp_times$mandel$_mls_L0_383_499$(pc1) {
  return (x$01, y$11, param0$21, param1$31, a$41, b$51, param0$61, param1$71, c$81, d$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, curDepth$171, tmp$181, stackDelayRes$191) => {
    return new Cont$func$comp_times$mandel$_mls_L0_383_499$.class(pc1)(x$01, y$11, param0$21, param1$31, a$41, b$51, param0$61, param1$71, c$81, d$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, curDepth$171, tmp$181, stackDelayRes$191);
  }
};
Cont$func$comp_times$mandel$_mls_L0_383_499$1.class = class Cont$func$comp_times$mandel$_mls_L0_383_499$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, y$1, param0$2, param1$3, a$4, b$5, param0$6, param1$7, c$8, d$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, stackDelayRes$19) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$0 = x$0;
      this.y$1 = y$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.a$4 = a$4;
      this.b$5 = b$5;
      this.param0$6 = param0$6;
      this.param1$7 = param1$7;
      this.c$8 = c$8;
      this.d$9 = d$9;
      this.tmp$10 = tmp$10;
      this.tmp$11 = tmp$11;
      this.tmp$12 = tmp$12;
      this.tmp$13 = tmp$13;
      this.tmp$14 = tmp$14;
      this.tmp$15 = tmp$15;
      this.tmp$16 = tmp$16;
      this.curDepth$17 = curDepth$17;
      this.tmp$18 = tmp$18;
      this.stackDelayRes$19 = stackDelayRes$19;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 6) {
      this.stackDelayRes$19 = value$;
    } else if (this.pc === 8) {
      this.tmp$18 = value$;
    } else if (this.pc === 7) {
      this.tmp$16 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 6) {
        if (this.x$0 instanceof Complex1.class) {
          this.param0$2 = this.x$0.r;
          this.param1$3 = this.x$0.i;
          this.a$4 = this.param0$2;
          this.b$5 = this.param1$3;
          if (this.y$1 instanceof Complex1.class) {
            this.param0$6 = this.y$1.r;
            this.param1$7 = this.y$1.i;
            this.c$8 = this.param0$6;
            this.d$9 = this.param1$7;
            this.tmp$10 = this.a$4 * this.c$8;
            this.tmp$11 = this.b$5 * this.d$9;
            this.tmp$12 = this.tmp$10 - this.tmp$11;
            this.tmp$13 = this.a$4 * this.d$9;
            this.tmp$14 = this.b$5 * this.c$8;
            this.tmp$15 = this.tmp$13 + this.tmp$14;
            this.pc = 10;
            continue contLoop;
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.tmp$16 = new globalThis.Error("match error");
            if (this.tmp$16 instanceof runtime.EffectSig.class) {
              this.pc = 7;
              this.tmp$16.contTrace.last.next = this;
              this.tmp$16.contTrace.last = this;
              return this.tmp$16
            }
            this.pc = 7;
            continue contLoop;
          }
          this.pc = 9;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$18 = new globalThis.Error("match error");
          if (this.tmp$18 instanceof runtime.EffectSig.class) {
            this.pc = 8;
            this.tmp$18.contTrace.last.next = this;
            this.tmp$18.contTrace.last = this;
            return this.tmp$18
          }
          this.pc = 8;
          continue contLoop;
        }
        this.pc = 9;
        continue contLoop;
      } else if (this.pc === 9) {
        break contLoop;
      } else if (this.pc === 8) {
        this.tmp$18 = runtime.resetDepth(this.tmp$18, this.curDepth$17);
        throw this.tmp$18;
      } else if (this.pc === 7) {
        this.tmp$16 = runtime.resetDepth(this.tmp$16, this.curDepth$17);
        throw this.tmp$16;
      } else if (this.pc === 10) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Complex1(this.tmp$12, this.tmp$15)
      }
      break;
    }
  }
  toString() { return "Cont$func$comp_times$mandel$_mls_L0_383_499$(" + globalThis.Predef.render(this.pc) + ")"; }
};
comp_times = function comp_times(x, y) {
  let param0, param1, a, b, param01, param11, c, d, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, curDepth, tmp7, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$comp_times$mandel$_mls_L0_383_499$$(x, y, param0, param1, a, b, param01, param11, c, d, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, curDepth, tmp7, stackDelayRes, 6);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (x instanceof Complex1.class) {
    param0 = x.r;
    param1 = x.i;
    a = param0;
    b = param1;
    if (y instanceof Complex1.class) {
      param01 = y.r;
      param11 = y.i;
      c = param01;
      d = param11;
      tmp = a * c;
      tmp1 = b * d;
      tmp2 = tmp - tmp1;
      tmp3 = a * d;
      tmp4 = b * c;
      tmp5 = tmp3 + tmp4;
      runtime.stackDepth = runtime.stackDepth + 1;
      return Complex1(tmp2, tmp5)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp6 = new globalThis.Error("match error");
      if (tmp6 instanceof runtime.EffectSig.class) {
        tmp6.contTrace.last.next = Cont$func$comp_times$mandel$_mls_L0_383_499$$(x, y, param0, param1, a, b, param01, param11, c, d, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, curDepth, tmp7, stackDelayRes, 7);
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
      tmp7.contTrace.last.next = Cont$func$comp_times$mandel$_mls_L0_383_499$$(x, y, param0, param1, a, b, param01, param11, c, d, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, curDepth, tmp7, stackDelayRes, 8);
      tmp7.contTrace.last = tmp7.contTrace.last.next;
      return tmp7
    }
    tmp7 = runtime.resetDepth(tmp7, curDepth);
    throw tmp7;
  }
};
Cont$func$comp_plus$mandel$_mls_L0_505_596$$ = function Cont$func$comp_plus$mandel$_mls_L0_505_596$$(x$0, y$1, param0$2, param1$3, a$4, b$5, param0$6, param1$7, c$8, d$9, tmp$10, tmp$11, tmp$12, curDepth$13, tmp$14, stackDelayRes$15, pc) {
  let tmp;
  tmp = new Cont$func$comp_plus$mandel$_mls_L0_505_596$1.class(pc);
  return tmp(x$0, y$1, param0$2, param1$3, a$4, b$5, param0$6, param1$7, c$8, d$9, tmp$10, tmp$11, tmp$12, curDepth$13, tmp$14, stackDelayRes$15)
};
Cont$func$comp_plus$mandel$_mls_L0_505_596$$ctor = function Cont$func$comp_plus$mandel$_mls_L0_505_596$$ctor(x$0, y$1, param0$2, param1$3, a$4, b$5, param0$6, param1$7, c$8, d$9, tmp$10, tmp$11, tmp$12, curDepth$13, tmp$14, stackDelayRes$15) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$comp_plus$mandel$_mls_L0_505_596$1.class(pc);
    return tmp(x$0, y$1, param0$2, param1$3, a$4, b$5, param0$6, param1$7, c$8, d$9, tmp$10, tmp$11, tmp$12, curDepth$13, tmp$14, stackDelayRes$15)
  }
};
Cont$func$comp_plus$mandel$_mls_L0_505_596$1 = function Cont$func$comp_plus$mandel$_mls_L0_505_596$(pc1) {
  return (x$01, y$11, param0$21, param1$31, a$41, b$51, param0$61, param1$71, c$81, d$91, tmp$101, tmp$111, tmp$121, curDepth$131, tmp$141, stackDelayRes$151) => {
    return new Cont$func$comp_plus$mandel$_mls_L0_505_596$.class(pc1)(x$01, y$11, param0$21, param1$31, a$41, b$51, param0$61, param1$71, c$81, d$91, tmp$101, tmp$111, tmp$121, curDepth$131, tmp$141, stackDelayRes$151);
  }
};
Cont$func$comp_plus$mandel$_mls_L0_505_596$1.class = class Cont$func$comp_plus$mandel$_mls_L0_505_596$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, y$1, param0$2, param1$3, a$4, b$5, param0$6, param1$7, c$8, d$9, tmp$10, tmp$11, tmp$12, curDepth$13, tmp$14, stackDelayRes$15) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$0 = x$0;
      this.y$1 = y$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.a$4 = a$4;
      this.b$5 = b$5;
      this.param0$6 = param0$6;
      this.param1$7 = param1$7;
      this.c$8 = c$8;
      this.d$9 = d$9;
      this.tmp$10 = tmp$10;
      this.tmp$11 = tmp$11;
      this.tmp$12 = tmp$12;
      this.curDepth$13 = curDepth$13;
      this.tmp$14 = tmp$14;
      this.stackDelayRes$15 = stackDelayRes$15;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 11) {
      this.stackDelayRes$15 = value$;
    } else if (this.pc === 13) {
      this.tmp$14 = value$;
    } else if (this.pc === 12) {
      this.tmp$12 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 11) {
        if (this.x$0 instanceof Complex1.class) {
          this.param0$2 = this.x$0.r;
          this.param1$3 = this.x$0.i;
          this.a$4 = this.param0$2;
          this.b$5 = this.param1$3;
          if (this.y$1 instanceof Complex1.class) {
            this.param0$6 = this.y$1.r;
            this.param1$7 = this.y$1.i;
            this.c$8 = this.param0$6;
            this.d$9 = this.param1$7;
            this.tmp$10 = this.a$4 + this.c$8;
            this.tmp$11 = this.b$5 + this.d$9;
            this.pc = 15;
            continue contLoop;
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.tmp$12 = new globalThis.Error("match error");
            if (this.tmp$12 instanceof runtime.EffectSig.class) {
              this.pc = 12;
              this.tmp$12.contTrace.last.next = this;
              this.tmp$12.contTrace.last = this;
              return this.tmp$12
            }
            this.pc = 12;
            continue contLoop;
          }
          this.pc = 14;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$14 = new globalThis.Error("match error");
          if (this.tmp$14 instanceof runtime.EffectSig.class) {
            this.pc = 13;
            this.tmp$14.contTrace.last.next = this;
            this.tmp$14.contTrace.last = this;
            return this.tmp$14
          }
          this.pc = 13;
          continue contLoop;
        }
        this.pc = 14;
        continue contLoop;
      } else if (this.pc === 14) {
        break contLoop;
      } else if (this.pc === 13) {
        this.tmp$14 = runtime.resetDepth(this.tmp$14, this.curDepth$13);
        throw this.tmp$14;
      } else if (this.pc === 12) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$13);
        throw this.tmp$12;
      } else if (this.pc === 15) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Complex1(this.tmp$10, this.tmp$11)
      }
      break;
    }
  }
  toString() { return "Cont$func$comp_plus$mandel$_mls_L0_505_596$(" + globalThis.Predef.render(this.pc) + ")"; }
};
comp_plus = function comp_plus(x, y) {
  let param0, param1, a, b, param01, param11, c, d, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$comp_plus$mandel$_mls_L0_505_596$$(x, y, param0, param1, a, b, param01, param11, c, d, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 11);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (x instanceof Complex1.class) {
    param0 = x.r;
    param1 = x.i;
    a = param0;
    b = param1;
    if (y instanceof Complex1.class) {
      param01 = y.r;
      param11 = y.i;
      c = param01;
      d = param11;
      tmp = a + c;
      tmp1 = b + d;
      runtime.stackDepth = runtime.stackDepth + 1;
      return Complex1(tmp, tmp1)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = new globalThis.Error("match error");
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.contTrace.last.next = Cont$func$comp_plus$mandel$_mls_L0_505_596$$(x, y, param0, param1, a, b, param01, param11, c, d, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 12);
        tmp2.contTrace.last = tmp2.contTrace.last.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      throw tmp2;
    }
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp3 = new globalThis.Error("match error");
    if (tmp3 instanceof runtime.EffectSig.class) {
      tmp3.contTrace.last.next = Cont$func$comp_plus$mandel$_mls_L0_505_596$$(x, y, param0, param1, a, b, param01, param11, c, d, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 13);
      tmp3.contTrace.last = tmp3.contTrace.last.next;
      return tmp3
    }
    tmp3 = runtime.resetDepth(tmp3, curDepth);
    throw tmp3;
  }
};
Cont$func$mandel_$mandel$_mls_L0_602_751$$ = function Cont$func$mandel_$mandel$_mls_L0_602_751$$(c$0, stackDelayRes$1, pc) {
  let tmp;
  tmp = new Cont$func$mandel_$mandel$_mls_L0_602_751$1.class(pc);
  return tmp(c$0, stackDelayRes$1)
};
Cont$func$mandel_$mandel$_mls_L0_602_751$$ctor = function Cont$func$mandel_$mandel$_mls_L0_602_751$$ctor(c$0, stackDelayRes$1) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$mandel_$mandel$_mls_L0_602_751$1.class(pc);
    return tmp(c$0, stackDelayRes$1)
  }
};
Cont$func$mandel_$mandel$_mls_L0_602_751$1 = function Cont$func$mandel_$mandel$_mls_L0_602_751$(pc1) {
  return (c$01, stackDelayRes$11) => {
    return new Cont$func$mandel_$mandel$_mls_L0_602_751$.class(pc1)(c$01, stackDelayRes$11);
  }
};
Cont$func$mandel_$mandel$_mls_L0_602_751$1.class = class Cont$func$mandel_$mandel$_mls_L0_602_751$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (c$0, stackDelayRes$1) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.c$0 = c$0;
      this.stackDelayRes$1 = stackDelayRes$1;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 16) {
      this.stackDelayRes$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 16) {
        this.pc = 29;
        continue contLoop;
      } else if (this.pc === 29) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return infiniteMandel$(this.c$0)
      }
      break;
    }
  }
  toString() { return "Cont$func$mandel_$mandel$_mls_L0_602_751$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$infiniteMandel$mandel$_mls_L0_621_650$$ = function Cont$func$infiniteMandel$mandel$_mls_L0_621_650$$(c$1, infiniteMandel$capture$0, pc) {
  let tmp;
  tmp = new Cont$func$infiniteMandel$mandel$_mls_L0_621_650$1.class(pc);
  return tmp(c$1, infiniteMandel$capture$0)
};
Cont$func$infiniteMandel$mandel$_mls_L0_621_650$$ctor = function Cont$func$infiniteMandel$mandel$_mls_L0_621_650$$ctor(c$1, infiniteMandel$capture$0) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$infiniteMandel$mandel$_mls_L0_621_650$1.class(pc);
    return tmp(c$1, infiniteMandel$capture$0)
  }
};
Cont$func$infiniteMandel$mandel$_mls_L0_621_650$1 = function Cont$func$infiniteMandel$mandel$_mls_L0_621_650$(pc1) {
  return (c$11, infiniteMandel$capture$01) => {
    return new Cont$func$infiniteMandel$mandel$_mls_L0_621_650$.class(pc1)(c$11, infiniteMandel$capture$01);
  }
};
Cont$func$infiniteMandel$mandel$_mls_L0_621_650$1.class = class Cont$func$infiniteMandel$mandel$_mls_L0_621_650$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (c$1, infiniteMandel$capture$0) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.c$1 = c$1;
      this.infiniteMandel$capture$0 = infiniteMandel$capture$0;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 17) {
      this.infiniteMandel$capture$0.stackDelayRes1$ = value$;
    }
    contLoop: while (true) {
      if (this.pc === 17) {
        this.infiniteMandel$capture$0.tmp0$ = runtime.safeCall(lambda(this.c$1, this.infiniteMandel$capture$0));
        this.pc = 28;
        continue contLoop;
      } else if (this.pc === 28) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.lazy(this.infiniteMandel$capture$0.tmp0$)
      }
      break;
    }
  }
  toString() { return "Cont$func$infiniteMandel$mandel$_mls_L0_621_650$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$1 = function Cont$func$lambda$$$(c$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5, infiniteMandel$capture$0, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$5.class(pc);
  return tmp(c$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5, infiniteMandel$capture$0)
};
Cont$func$lambda$$$ctor1 = function Cont$func$lambda$$$ctor(c$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5, infiniteMandel$capture$0) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$5.class(pc);
    return tmp(c$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5, infiniteMandel$capture$0)
  }
};
Cont$func$lambda$$5 = function Cont$func$lambda$$(pc1) {
  return (c$11, tmp$21, tmp$31, curDepth$41, stackDelayRes$51, infiniteMandel$capture$01) => {
    return new Cont$func$lambda$$.class(pc1)(c$11, tmp$21, tmp$31, curDepth$41, stackDelayRes$51, infiniteMandel$capture$01);
  }
};
Cont$func$lambda$$5.class = class Cont$func$lambda$$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (c$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5, infiniteMandel$capture$0) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.c$1 = c$1;
      this.tmp$2 = tmp$2;
      this.tmp$3 = tmp$3;
      this.curDepth$4 = curDepth$4;
      this.stackDelayRes$5 = stackDelayRes$5;
      this.infiniteMandel$capture$0 = infiniteMandel$capture$0;
      return this;
    }
  }
  resume(value$) {
    let lambda$this;
    if (this.pc === 18) {
      this.stackDelayRes$5 = value$;
    } else if (this.pc === 19) {
      this.tmp$2 = value$;
    } else if (this.pc === 24) {
      this.tmp$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 18) {
        this.pc = 27;
        continue contLoop;
      } else if (this.pc === 25) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.LzCons(this.c$1, this.tmp$3)
      } else if (this.pc === 26) {
        runtime.stackDepth = runtime.stackDepth + 1;
        lambda$this = runtime.safeCall(lambda1(this.c$1));
        this.tmp$3 = NofibPrelude.map_lz(lambda$this, this.tmp$2);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 24;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 24;
        continue contLoop;
      } else if (this.pc === 27) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = infiniteMandel$(this.c$1);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 19;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 19;
        continue contLoop;
      } else if (this.pc === 19) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$4);
        this.pc = 26;
        continue contLoop;
      } else if (this.pc === 24) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$4);
        this.pc = 25;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$ = function Cont$func$lambda$$$(c$0, z$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$4.class(pc);
  return tmp(c$0, z$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$lambda$$$ctor = function Cont$func$lambda$$$ctor(c$0, z$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$4.class(pc);
    return tmp(c$0, z$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$lambda$$4 = function Cont$func$lambda$$(pc1) {
  return (c$01, z$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$lambda$$.class(pc1)(c$01, z$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$lambda$$4.class = class Cont$func$lambda$$1 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (c$0, z$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.c$0 = c$0;
      this.z$1 = z$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 20) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 21) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 20) {
        this.pc = 23;
        continue contLoop;
      } else if (this.pc === 22) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return comp_plus(this.tmp$2, this.c$0)
      } else if (this.pc === 23) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = comp_times(this.z$1, this.z$1);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 21;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 21;
        continue contLoop;
      } else if (this.pc === 21) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        this.pc = 22;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda$1 = function lambda$(c, z) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$(c, z, tmp, curDepth, stackDelayRes, 20);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = comp_times(z, z);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$(c, z, tmp, curDepth, stackDelayRes, 21);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return comp_plus(tmp, c)
};
lambda1 = (undefined, function (c) {
  return (z) => {
    return lambda$1(c, z)
  }
});
lambda$ = function lambda$(c, infiniteMandel$capture2) {
  let tmp, tmp1, curDepth, stackDelayRes, lambda$this;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$1(c, tmp, tmp1, curDepth, stackDelayRes, infiniteMandel$capture2, 18);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = infiniteMandel$(c);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$1(c, tmp, tmp1, curDepth, stackDelayRes, infiniteMandel$capture2, 19);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  lambda$this = runtime.safeCall(lambda1(c));
  tmp1 = NofibPrelude.map_lz(lambda$this, tmp);
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$lambda$$$1(c, tmp, tmp1, curDepth, stackDelayRes, infiniteMandel$capture2, 24);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return NofibPrelude.LzCons(c, tmp1)
};
lambda = (undefined, function (c, infiniteMandel$capture2) {
  return () => {
    return lambda$(c, infiniteMandel$capture2)
  }
});
infiniteMandel$capture1 = function infiniteMandel$capture(tmp0$1, stackDelayRes1$1) {
  return new infiniteMandel$capture.class(tmp0$1, stackDelayRes1$1);
};
infiniteMandel$capture1.class = class infiniteMandel$capture {
  constructor(tmp0$, stackDelayRes1$) {
    this.tmp0$ = tmp0$;
    this.stackDelayRes1$ = stackDelayRes1$;
  }
  toString() { return "infiniteMandel$capture(" + globalThis.Predef.render(this.tmp0$) + ", " + globalThis.Predef.render(this.stackDelayRes1$) + ")"; }
};
infiniteMandel$ = function infiniteMandel$(c) {
  let capture;
  capture = new infiniteMandel$capture1(null, null);
  capture.stackDelayRes1$ = runtime.checkDepth();
  if (capture.stackDelayRes1$ instanceof runtime.EffectSig.class) {
    capture.stackDelayRes1$.contTrace.last.next = Cont$func$infiniteMandel$mandel$_mls_L0_621_650$$(c, capture, 17);
    capture.stackDelayRes1$.contTrace.last = capture.stackDelayRes1$.contTrace.last.next;
    return capture.stackDelayRes1$
  }
  capture.tmp0$ = runtime.safeCall(lambda(c, capture));
  runtime.stackDepth = runtime.stackDepth + 1;
  return NofibPrelude.lazy(capture.tmp0$)
};
infiniteMandel = function infiniteMandel(c) {
  return () => {
    return infiniteMandel$(c)
  }
};
mandel_ = function mandel_(c) {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$mandel_$mandel$_mls_L0_602_751$$(c, stackDelayRes, 16);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return infiniteMandel$(c)
};
Cont$func$diverge$mandel$_mls_L0_757_814$$ = function Cont$func$diverge$mandel$_mls_L0_757_814$$(cmplx$0, radius$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$diverge$mandel$_mls_L0_757_814$1.class(pc);
  return tmp(cmplx$0, radius$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$diverge$mandel$_mls_L0_757_814$$ctor = function Cont$func$diverge$mandel$_mls_L0_757_814$$ctor(cmplx$0, radius$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$diverge$mandel$_mls_L0_757_814$1.class(pc);
    return tmp(cmplx$0, radius$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$diverge$mandel$_mls_L0_757_814$1 = function Cont$func$diverge$mandel$_mls_L0_757_814$(pc1) {
  return (cmplx$01, radius$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$diverge$mandel$_mls_L0_757_814$.class(pc1)(cmplx$01, radius$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$diverge$mandel$_mls_L0_757_814$1.class = class Cont$func$diverge$mandel$_mls_L0_757_814$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (cmplx$0, radius$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.cmplx$0 = cmplx$0;
      this.radius$1 = radius$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 30) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 31) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 30) {
        this.pc = 32;
        continue contLoop;
      } else if (this.pc === 32) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = comp_magnitude(this.cmplx$0);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 31;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 31;
        continue contLoop;
      } else if (this.pc === 31) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        return this.tmp$2 > this.radius$1
      }
      break;
    }
  }
  toString() { return "Cont$func$diverge$mandel$_mls_L0_757_814$(" + globalThis.Predef.render(this.pc) + ")"; }
};
diverge = function diverge(cmplx, radius) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$diverge$mandel$_mls_L0_757_814$$(cmplx, radius, tmp, curDepth, stackDelayRes, 30);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = comp_magnitude(cmplx);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$diverge$mandel$_mls_L0_757_814$$(cmplx, radius, tmp, curDepth, stackDelayRes, 31);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  return tmp > radius
};
Cont$func$whenDiverge$mandel$_mls_L0_820_1026$$ = function Cont$func$whenDiverge$mandel$_mls_L0_820_1026$$(limit$0, radius$1, c$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6, pc) {
  let tmp;
  tmp = new Cont$func$whenDiverge$mandel$_mls_L0_820_1026$1.class(pc);
  return tmp(limit$0, radius$1, c$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6)
};
Cont$func$whenDiverge$mandel$_mls_L0_820_1026$$ctor = function Cont$func$whenDiverge$mandel$_mls_L0_820_1026$$ctor(limit$0, radius$1, c$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$whenDiverge$mandel$_mls_L0_820_1026$1.class(pc);
    return tmp(limit$0, radius$1, c$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6)
  }
};
Cont$func$whenDiverge$mandel$_mls_L0_820_1026$1 = function Cont$func$whenDiverge$mandel$_mls_L0_820_1026$(pc1) {
  return (limit$01, radius$11, c$21, tmp$31, tmp$41, curDepth$51, stackDelayRes$61) => {
    return new Cont$func$whenDiverge$mandel$_mls_L0_820_1026$.class(pc1)(limit$01, radius$11, c$21, tmp$31, tmp$41, curDepth$51, stackDelayRes$61);
  }
};
Cont$func$whenDiverge$mandel$_mls_L0_820_1026$1.class = class Cont$func$whenDiverge$mandel$_mls_L0_820_1026$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (limit$0, radius$1, c$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.limit$0 = limit$0;
      this.radius$1 = radius$1;
      this.c$2 = c$2;
      this.tmp$3 = tmp$3;
      this.tmp$4 = tmp$4;
      this.curDepth$5 = curDepth$5;
      this.stackDelayRes$6 = stackDelayRes$6;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 33) {
      this.stackDelayRes$6 = value$;
    } else if (this.pc === 43) {
      this.tmp$3 = value$;
    } else if (this.pc === 44) {
      this.tmp$4 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 33) {
        this.pc = 47;
        continue contLoop;
      } else if (this.pc === 45) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return walkIt$(this.radius$1, this.tmp$4)
      } else if (this.pc === 46) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$4 = NofibPrelude.take_lz_lz(this.limit$0, this.tmp$3);
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 44;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 44;
        continue contLoop;
      } else if (this.pc === 47) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = mandel_(this.c$2);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 43;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 43;
        continue contLoop;
      } else if (this.pc === 43) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$5);
        this.pc = 46;
        continue contLoop;
      } else if (this.pc === 44) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$5);
        this.pc = 45;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$whenDiverge$mandel$_mls_L0_820_1026$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$walkIt$mandel$_mls_L0_858_983$$ = function Cont$func$walkIt$mandel$_mls_L0_858_983$$(radius$0, ls$1, scrut$2, param0$3, param1$4, x$5, xs$6, scrut$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11, pc) {
  let tmp;
  tmp = new Cont$func$walkIt$mandel$_mls_L0_858_983$1.class(pc);
  return tmp(radius$0, ls$1, scrut$2, param0$3, param1$4, x$5, xs$6, scrut$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11)
};
Cont$func$walkIt$mandel$_mls_L0_858_983$$ctor = function Cont$func$walkIt$mandel$_mls_L0_858_983$$ctor(radius$0, ls$1, scrut$2, param0$3, param1$4, x$5, xs$6, scrut$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$walkIt$mandel$_mls_L0_858_983$1.class(pc);
    return tmp(radius$0, ls$1, scrut$2, param0$3, param1$4, x$5, xs$6, scrut$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11)
  }
};
Cont$func$walkIt$mandel$_mls_L0_858_983$1 = function Cont$func$walkIt$mandel$_mls_L0_858_983$(pc1) {
  return (radius$01, ls$11, scrut$21, param0$31, param1$41, x$51, xs$61, scrut$71, tmp$81, curDepth$91, tmp$101, stackDelayRes$111) => {
    return new Cont$func$walkIt$mandel$_mls_L0_858_983$.class(pc1)(radius$01, ls$11, scrut$21, param0$31, param1$41, x$51, xs$61, scrut$71, tmp$81, curDepth$91, tmp$101, stackDelayRes$111);
  }
};
Cont$func$walkIt$mandel$_mls_L0_858_983$1.class = class Cont$func$walkIt$mandel$_mls_L0_858_983$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (radius$0, ls$1, scrut$2, param0$3, param1$4, x$5, xs$6, scrut$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.radius$0 = radius$0;
      this.ls$1 = ls$1;
      this.scrut$2 = scrut$2;
      this.param0$3 = param0$3;
      this.param1$4 = param1$4;
      this.x$5 = x$5;
      this.xs$6 = xs$6;
      this.scrut$7 = scrut$7;
      this.tmp$8 = tmp$8;
      this.curDepth$9 = curDepth$9;
      this.tmp$10 = tmp$10;
      this.stackDelayRes$11 = stackDelayRes$11;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 34) {
      this.stackDelayRes$11 = value$;
    } else if (this.pc === 35) {
      this.scrut$2 = value$;
    } else if (this.pc === 38) {
      this.tmp$10 = value$;
    } else if (this.pc === 36) {
      this.scrut$7 = value$;
    } else if (this.pc === 37) {
      this.tmp$8 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 34) {
        this.pc = 42;
        continue contLoop;
      } else if (this.pc === 42) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$2 = NofibPrelude.force(this.ls$1);
        if (this.scrut$2 instanceof runtime.EffectSig.class) {
          this.pc = 35;
          this.scrut$2.contTrace.last.next = this;
          this.scrut$2.contTrace.last = this;
          return this.scrut$2
        }
        this.pc = 35;
        continue contLoop;
      } else if (this.pc === 35) {
        this.scrut$2 = runtime.resetDepth(this.scrut$2, this.curDepth$9);
        if (this.scrut$2 instanceof NofibPrelude.LzNil.class) {
          return 0
        } else if (this.scrut$2 instanceof NofibPrelude.LzCons.class) {
          this.param0$3 = this.scrut$2.head;
          this.param1$4 = this.scrut$2.tail;
          this.x$5 = this.param0$3;
          this.xs$6 = this.param1$4;
          this.pc = 41;
          continue contLoop;
          this.pc = 39;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$10 = new globalThis.Error("match error");
          if (this.tmp$10 instanceof runtime.EffectSig.class) {
            this.pc = 38;
            this.tmp$10.contTrace.last.next = this;
            this.tmp$10.contTrace.last = this;
            return this.tmp$10
          }
          this.pc = 38;
          continue contLoop;
        }
        this.pc = 39;
        continue contLoop;
      } else if (this.pc === 39) {
        break contLoop;
      } else if (this.pc === 38) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$9);
        throw this.tmp$10;
      } else if (this.pc === 41) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$7 = diverge(this.x$5, this.radius$0);
        if (this.scrut$7 instanceof runtime.EffectSig.class) {
          this.pc = 36;
          this.scrut$7.contTrace.last.next = this;
          this.scrut$7.contTrace.last = this;
          return this.scrut$7
        }
        this.pc = 36;
        continue contLoop;
      } else if (this.pc === 36) {
        this.scrut$7 = runtime.resetDepth(this.scrut$7, this.curDepth$9);
        if (this.scrut$7 === true) {
          return 0
        } else {
          this.pc = 40;
          continue contLoop;
        }
        this.pc = 39;
        continue contLoop;
      } else if (this.pc === 40) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = walkIt$(this.radius$0, this.xs$6);
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 37;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 37;
        continue contLoop;
      } else if (this.pc === 37) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$9);
        return 1 + this.tmp$8
      }
      break;
    }
  }
  toString() { return "Cont$func$walkIt$mandel$_mls_L0_858_983$(" + globalThis.Predef.render(this.pc) + ")"; }
};
walkIt$ = function walkIt$(radius, ls) {
  let scrut, param0, param1, x, xs, scrut1, tmp, curDepth, tmp1, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$walkIt$mandel$_mls_L0_858_983$$(radius, ls, scrut, param0, param1, x, xs, scrut1, tmp, curDepth, tmp1, stackDelayRes, 34);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  scrut = NofibPrelude.force(ls);
  if (scrut instanceof runtime.EffectSig.class) {
    scrut.contTrace.last.next = Cont$func$walkIt$mandel$_mls_L0_858_983$$(radius, ls, scrut, param0, param1, x, xs, scrut1, tmp, curDepth, tmp1, stackDelayRes, 35);
    scrut.contTrace.last = scrut.contTrace.last.next;
    return scrut
  }
  scrut = runtime.resetDepth(scrut, curDepth);
  if (scrut instanceof NofibPrelude.LzNil.class) {
    return 0
  } else if (scrut instanceof NofibPrelude.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    x = param0;
    xs = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    scrut1 = diverge(x, radius);
    if (scrut1 instanceof runtime.EffectSig.class) {
      scrut1.contTrace.last.next = Cont$func$walkIt$mandel$_mls_L0_858_983$$(radius, ls, scrut, param0, param1, x, xs, scrut1, tmp, curDepth, tmp1, stackDelayRes, 36);
      scrut1.contTrace.last = scrut1.contTrace.last.next;
      return scrut1
    }
    scrut1 = runtime.resetDepth(scrut1, curDepth);
    if (scrut1 === true) {
      return 0
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = walkIt$(radius, xs);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$walkIt$mandel$_mls_L0_858_983$$(radius, ls, scrut, param0, param1, x, xs, scrut1, tmp, curDepth, tmp1, stackDelayRes, 37);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      return 1 + tmp
    }
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = new globalThis.Error("match error");
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$walkIt$mandel$_mls_L0_858_983$$(radius, ls, scrut, param0, param1, x, xs, scrut1, tmp, curDepth, tmp1, stackDelayRes, 38);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    throw tmp1;
  }
};
walkIt = function walkIt(radius) {
  return (ls) => {
    return walkIt$(radius, ls)
  }
};
whenDiverge = function whenDiverge(limit, radius, c) {
  let tmp, tmp1, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$whenDiverge$mandel$_mls_L0_820_1026$$(limit, radius, c, tmp, tmp1, curDepth, stackDelayRes, 33);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = mandel_(c);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$whenDiverge$mandel$_mls_L0_820_1026$$(limit, radius, c, tmp, tmp1, curDepth, stackDelayRes, 43);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = NofibPrelude.take_lz_lz(limit, tmp);
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$whenDiverge$mandel$_mls_L0_820_1026$$(limit, radius, c, tmp, tmp1, curDepth, stackDelayRes, 44);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return walkIt$(radius, tmp1)
};
Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$$ = function Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$$(mat$0, limit$1, radius$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$1.class(pc);
  return tmp(mat$0, limit$1, radius$2, stackDelayRes$3)
};
Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$$ctor = function Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$$ctor(mat$0, limit$1, radius$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$1.class(pc);
    return tmp(mat$0, limit$1, radius$2, stackDelayRes$3)
  }
};
Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$1 = function Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$(pc1) {
  return (mat$01, limit$11, radius$21, stackDelayRes$31) => {
    return new Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$.class(pc1)(mat$01, limit$11, radius$21, stackDelayRes$31);
  }
};
Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$1.class = class Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (mat$0, limit$1, radius$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.mat$0 = mat$0;
      this.limit$1 = limit$1;
      this.radius$2 = radius$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      return this;
    }
  }
  resume(value$) {
    let lambda$this;
    if (this.pc === 48) {
      this.stackDelayRes$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 48) {
        this.pc = 51;
        continue contLoop;
      } else if (this.pc === 51) {
        runtime.stackDepth = runtime.stackDepth + 1;
        lambda$this = runtime.safeCall(lambda2(this.limit$1, this.radius$2));
        return NofibPrelude.map(lambda$this, this.mat$0)
      }
      break;
    }
  }
  toString() { return "Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$2 = function Cont$func$lambda$$$(limit$0, radius$1, c$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$6.class(pc);
  return tmp(limit$0, radius$1, c$2, stackDelayRes$3)
};
Cont$func$lambda$$$ctor2 = function Cont$func$lambda$$$ctor(limit$0, radius$1, c$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$6.class(pc);
    return tmp(limit$0, radius$1, c$2, stackDelayRes$3)
  }
};
Cont$func$lambda$$6 = function Cont$func$lambda$$(pc1) {
  return (limit$01, radius$11, c$21, stackDelayRes$31) => {
    return new Cont$func$lambda$$.class(pc1)(limit$01, radius$11, c$21, stackDelayRes$31);
  }
};
Cont$func$lambda$$6.class = class Cont$func$lambda$$2 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (limit$0, radius$1, c$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.limit$0 = limit$0;
      this.radius$1 = radius$1;
      this.c$2 = c$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 49) {
      this.stackDelayRes$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 49) {
        this.pc = 50;
        continue contLoop;
      } else if (this.pc === 50) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return whenDiverge(this.limit$0, this.radius$1, this.c$2)
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda$2 = function lambda$(limit, radius, c) {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$2(limit, radius, c, stackDelayRes, 49);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return whenDiverge(limit, radius, c)
};
lambda2 = (undefined, function (limit, radius) {
  return (c) => {
    return lambda$2(limit, radius, c)
  }
});
parallelMandel = function parallelMandel(mat, limit, radius) {
  let stackDelayRes, lambda$this;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$parallelMandel$mandel$_mls_L0_1032_1113$$(mat, limit, radius, stackDelayRes, 48);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  lambda$this = runtime.safeCall(lambda2(limit, radius));
  return NofibPrelude.map(lambda$this, mat)
};
Cont$func$mandelset$mandel$_mls_L0_1119_1730$$ = function Cont$func$mandelset$mandel$_mls_L0_1119_1730$$(x$0, y$1, x_$2, y_$3, screenX$4, screenY$5, lIMIT$6, result$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, stackDelayRes$17, pc) {
  let tmp;
  tmp = new Cont$func$mandelset$mandel$_mls_L0_1119_1730$1.class(pc);
  return tmp(x$0, y$1, x_$2, y_$3, screenX$4, screenY$5, lIMIT$6, result$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, stackDelayRes$17)
};
Cont$func$mandelset$mandel$_mls_L0_1119_1730$$ctor = function Cont$func$mandelset$mandel$_mls_L0_1119_1730$$ctor(x$0, y$1, x_$2, y_$3, screenX$4, screenY$5, lIMIT$6, result$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, stackDelayRes$17) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$mandelset$mandel$_mls_L0_1119_1730$1.class(pc);
    return tmp(x$0, y$1, x_$2, y_$3, screenX$4, screenY$5, lIMIT$6, result$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, stackDelayRes$17)
  }
};
Cont$func$mandelset$mandel$_mls_L0_1119_1730$1 = function Cont$func$mandelset$mandel$_mls_L0_1119_1730$(pc1) {
  return (x$01, y$11, x_$21, y_$31, screenX$41, screenY$51, lIMIT$61, result$71, tmp$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, curDepth$161, stackDelayRes$171) => {
    return new Cont$func$mandelset$mandel$_mls_L0_1119_1730$.class(pc1)(x$01, y$11, x_$21, y_$31, screenX$41, screenY$51, lIMIT$61, result$71, tmp$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, curDepth$161, stackDelayRes$171);
  }
};
Cont$func$mandelset$mandel$_mls_L0_1119_1730$1.class = class Cont$func$mandelset$mandel$_mls_L0_1119_1730$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, y$1, x_$2, y_$3, screenX$4, screenY$5, lIMIT$6, result$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, stackDelayRes$17) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$0 = x$0;
      this.y$1 = y$1;
      this.x_$2 = x_$2;
      this.y_$3 = y_$3;
      this.screenX$4 = screenX$4;
      this.screenY$5 = screenY$5;
      this.lIMIT$6 = lIMIT$6;
      this.result$7 = result$7;
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
    let prettyRGB$this;
    if (this.pc === 52) {
      this.stackDelayRes$17 = value$;
    } else if (this.pc === 70) {
      this.tmp$8 = value$;
    } else if (this.pc === 71) {
      this.tmp$9 = value$;
    } else if (this.pc === 72) {
      this.tmp$12 = value$;
    } else if (this.pc === 73) {
      this.tmp$14 = value$;
    } else if (this.pc === 74) {
      this.tmp$15 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 52) {
        this.pc = 80;
        continue contLoop;
      } else if (this.pc === 77) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$14 = parallelMandel(this.tmp$9, this.lIMIT$6, this.tmp$13);
        if (this.tmp$14 instanceof runtime.EffectSig.class) {
          this.pc = 73;
          this.tmp$14.contTrace.last.next = this;
          this.tmp$14.contTrace.last = this;
          return this.tmp$14
        }
        this.pc = 73;
        continue contLoop;
      } else if (this.pc === 79) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = lscomp1$(this.x$0, this.y$1, this.x_$2, this.y_$3, this.screenX$4, this.screenY$5, this.tmp$8);
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 71;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 71;
        continue contLoop;
      } else if (this.pc === 80) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = NofibPrelude.enumFromTo(1, this.screenY$5);
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 70;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 70;
        continue contLoop;
      } else if (this.pc === 70) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$16);
        this.pc = 79;
        continue contLoop;
      } else if (this.pc === 71) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$16);
        this.tmp$10 = this.x_$2 - this.x$0;
        this.tmp$11 = this.y_$3 - this.y$1;
        this.pc = 78;
        continue contLoop;
      } else if (this.pc === 78) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$12 = NofibPrelude.max(this.tmp$10, this.tmp$11);
        if (this.tmp$12 instanceof runtime.EffectSig.class) {
          this.pc = 72;
          this.tmp$12.contTrace.last.next = this;
          this.tmp$12.contTrace.last = this;
          return this.tmp$12
        }
        this.pc = 72;
        continue contLoop;
      } else if (this.pc === 72) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$16);
        this.tmp$13 = this.tmp$12 / 2;
        this.pc = 77;
        continue contLoop;
      } else if (this.pc === 73) {
        this.tmp$14 = runtime.resetDepth(this.tmp$14, this.curDepth$16);
        this.result$7 = this.tmp$14;
        this.pc = 76;
        continue contLoop;
      } else if (this.pc === 75) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return createPixmap(this.screenX$4, this.screenY$5, this.lIMIT$6, this.tmp$15)
      } else if (this.pc === 76) {
        runtime.stackDepth = runtime.stackDepth + 1;
        prettyRGB$this = runtime.safeCall(prettyRGB(this.lIMIT$6));
        this.tmp$15 = NofibPrelude.map(prettyRGB$this, this.result$7);
        if (this.tmp$15 instanceof runtime.EffectSig.class) {
          this.pc = 74;
          this.tmp$15.contTrace.last.next = this;
          this.tmp$15.contTrace.last = this;
          return this.tmp$15
        }
        this.pc = 74;
        continue contLoop;
      } else if (this.pc === 74) {
        this.tmp$15 = runtime.resetDepth(this.tmp$15, this.curDepth$16);
        this.pc = 75;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$mandelset$mandel$_mls_L0_1119_1730$(" + globalThis.Predef.render(this.pc) + ")"; }
};
prettyRGB$ = function prettyRGB$(lIMIT, s) {
  let t, tmp;
  tmp = lIMIT - s;
  t = tmp;
  return [
    s,
    t,
    t
  ]
};
prettyRGB = function prettyRGB(lIMIT) {
  return (s) => {
    return prettyRGB$(lIMIT, s)
  }
};
Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$$ = function Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$$(x$0, y$1, x_$2, y_$3, screenX$4, screenY$5, s$6, t$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, stackDelayRes$16, pc) {
  let tmp;
  tmp = new Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$1.class(pc);
  return tmp(x$0, y$1, x_$2, y_$3, screenX$4, screenY$5, s$6, t$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, stackDelayRes$16)
};
Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$$ctor = function Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$$ctor(x$0, y$1, x_$2, y_$3, screenX$4, screenY$5, s$6, t$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, stackDelayRes$16) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$1.class(pc);
    return tmp(x$0, y$1, x_$2, y_$3, screenX$4, screenY$5, s$6, t$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, stackDelayRes$16)
  }
};
Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$1 = function Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$(pc1) {
  return (x$01, y$11, x_$21, y_$31, screenX$41, screenY$51, s$61, t$71, tmp$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, stackDelayRes$161) => {
    return new Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$.class(pc1)(x$01, y$11, x_$21, y_$31, screenX$41, screenY$51, s$61, t$71, tmp$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, stackDelayRes$161);
  }
};
Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$1.class = class Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, y$1, x_$2, y_$3, screenX$4, screenY$5, s$6, t$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, stackDelayRes$16) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$0 = x$0;
      this.y$1 = y$1;
      this.x_$2 = x_$2;
      this.y_$3 = y_$3;
      this.screenX$4 = screenX$4;
      this.screenY$5 = screenY$5;
      this.s$6 = s$6;
      this.t$7 = t$7;
      this.tmp$8 = tmp$8;
      this.tmp$9 = tmp$9;
      this.tmp$10 = tmp$10;
      this.tmp$11 = tmp$11;
      this.tmp$12 = tmp$12;
      this.tmp$13 = tmp$13;
      this.tmp$14 = tmp$14;
      this.tmp$15 = tmp$15;
      this.stackDelayRes$16 = stackDelayRes$16;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 53) {
      this.stackDelayRes$16 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 53) {
        this.tmp$8 = this.x_$2 - this.x$0;
        this.tmp$9 = this.s$6 * this.tmp$8;
        this.tmp$10 = this.tmp$9 / this.screenX$4;
        this.tmp$11 = this.x$0 + this.tmp$10;
        this.tmp$12 = this.y_$3 - this.y$1;
        this.tmp$13 = this.t$7 * this.tmp$12;
        this.tmp$14 = this.tmp$13 / this.screenY$5;
        this.tmp$15 = this.y$1 + this.tmp$14;
        this.pc = 54;
        continue contLoop;
      } else if (this.pc === 54) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Complex1(this.tmp$11, this.tmp$15)
      }
      break;
    }
  }
  toString() { return "Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$(" + globalThis.Predef.render(this.pc) + ")"; }
};
windowToViewport$ = function windowToViewport$(x, y, x_, y_, screenX, screenY, s, t) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$windowToViewport$mandel$_mls_L0_1236_1336$$(x, y, x_, y_, screenX, screenY, s, t, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, stackDelayRes, 53);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  tmp = x_ - x;
  tmp1 = s * tmp;
  tmp2 = tmp1 / screenX;
  tmp3 = x + tmp2;
  tmp4 = y_ - y;
  tmp5 = t * tmp4;
  tmp6 = tmp5 / screenY;
  tmp7 = y + tmp6;
  runtime.stackDepth = runtime.stackDepth + 1;
  return Complex1(tmp3, tmp7)
};
windowToViewport = function windowToViewport(x, y, x_, y_, screenX, screenY) {
  return (s, t) => {
    return windowToViewport$(x, y, x_, y_, screenX, screenY, s, t)
  }
};
Cont$func$lscomp1$mandel$_mls_L0_1346_1565$$ = function Cont$func$lscomp1$mandel$_mls_L0_1346_1565$$(x$1, y$2, x_$3, y_$4, screenX$5, screenY$6, ls1$7, curDepth$8, lscomp1$capture$0, pc) {
  let tmp;
  tmp = new Cont$func$lscomp1$mandel$_mls_L0_1346_1565$1.class(pc);
  return tmp(x$1, y$2, x_$3, y_$4, screenX$5, screenY$6, ls1$7, curDepth$8, lscomp1$capture$0)
};
Cont$func$lscomp1$mandel$_mls_L0_1346_1565$$ctor = function Cont$func$lscomp1$mandel$_mls_L0_1346_1565$$ctor(x$1, y$2, x_$3, y_$4, screenX$5, screenY$6, ls1$7, curDepth$8, lscomp1$capture$0) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lscomp1$mandel$_mls_L0_1346_1565$1.class(pc);
    return tmp(x$1, y$2, x_$3, y_$4, screenX$5, screenY$6, ls1$7, curDepth$8, lscomp1$capture$0)
  }
};
Cont$func$lscomp1$mandel$_mls_L0_1346_1565$1 = function Cont$func$lscomp1$mandel$_mls_L0_1346_1565$(pc1) {
  return (x$11, y$21, x_$31, y_$41, screenX$51, screenY$61, ls1$71, curDepth$81, lscomp1$capture$01) => {
    return new Cont$func$lscomp1$mandel$_mls_L0_1346_1565$.class(pc1)(x$11, y$21, x_$31, y_$41, screenX$51, screenY$61, ls1$71, curDepth$81, lscomp1$capture$01);
  }
};
Cont$func$lscomp1$mandel$_mls_L0_1346_1565$1.class = class Cont$func$lscomp1$mandel$_mls_L0_1346_1565$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$1, y$2, x_$3, y_$4, screenX$5, screenY$6, ls1$7, curDepth$8, lscomp1$capture$0) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$1 = x$1;
      this.y$2 = y$2;
      this.x_$3 = x_$3;
      this.y_$4 = y_$4;
      this.screenX$5 = screenX$5;
      this.screenY$6 = screenY$6;
      this.ls1$7 = ls1$7;
      this.curDepth$8 = curDepth$8;
      this.lscomp1$capture$0 = lscomp1$capture$0;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 55) {
      this.lscomp1$capture$0.stackDelayRes4$ = value$;
    } else if (this.pc === 66) {
      this.lscomp1$capture$0.tmp1$ = value$;
    } else if (this.pc === 65) {
      this.lscomp1$capture$0.tmp3$ = value$;
    }
    contLoop: while (true) {
      if (this.pc === 55) {
        if (this.ls1$7 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (this.ls1$7 instanceof NofibPrelude.Cons.class) {
          this.lscomp1$capture$0.param05$ = this.ls1$7.head;
          this.lscomp1$capture$0.param10$ = this.ls1$7.tail;
          this.lscomp1$capture$0.t2$ = this.lscomp1$capture$0.param05$;
          this.lscomp1$capture$0.t16$ = this.lscomp1$capture$0.param10$;
          this.pc = 69;
          continue contLoop;
          this.pc = 67;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.lscomp1$capture$0.tmp1$ = new globalThis.Error("match error");
          if (this.lscomp1$capture$0.tmp1$ instanceof runtime.EffectSig.class) {
            this.pc = 66;
            this.lscomp1$capture$0.tmp1$.contTrace.last.next = this;
            this.lscomp1$capture$0.tmp1$.contTrace.last = this;
            return this.lscomp1$capture$0.tmp1$
          }
          this.pc = 66;
          continue contLoop;
        }
        this.pc = 67;
        continue contLoop;
      } else if (this.pc === 67) {
        break contLoop;
      } else if (this.pc === 66) {
        this.lscomp1$capture$0.tmp1$ = runtime.resetDepth(this.lscomp1$capture$0.tmp1$, this.curDepth$8);
        throw this.lscomp1$capture$0.tmp1$;
      } else if (this.pc === 68) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return lscomp2$(this.x$1, this.y$2, this.x_$3, this.y_$4, this.screenX$5, this.screenY$6, this.ls1$7, this.curDepth$8, this.lscomp1$capture$0, this.lscomp1$capture$0.tmp3$)
      } else if (this.pc === 69) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.lscomp1$capture$0.tmp3$ = NofibPrelude.enumFromTo(1, this.screenX$5);
        if (this.lscomp1$capture$0.tmp3$ instanceof runtime.EffectSig.class) {
          this.pc = 65;
          this.lscomp1$capture$0.tmp3$.contTrace.last.next = this;
          this.lscomp1$capture$0.tmp3$.contTrace.last = this;
          return this.lscomp1$capture$0.tmp3$
        }
        this.pc = 65;
        continue contLoop;
      } else if (this.pc === 65) {
        this.lscomp1$capture$0.tmp3$ = runtime.resetDepth(this.lscomp1$capture$0.tmp3$, this.curDepth$8);
        this.pc = 68;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lscomp1$mandel$_mls_L0_1346_1565$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lscomp2$mandel$_mls_L0_1415_1527$$ = function Cont$func$lscomp2$mandel$_mls_L0_1415_1527$$(x$1, y$2, x_$3, y_$4, screenX$5, screenY$6, ls1$7, ls2$8, param0$9, param1$10, s$11, t2$12, tmp$13, tmp$14, curDepth$15, tmp$16, stackDelayRes$17, curDepth$18, lscomp1$capture$0, pc) {
  let tmp;
  tmp = new Cont$func$lscomp2$mandel$_mls_L0_1415_1527$1.class(pc);
  return tmp(x$1, y$2, x_$3, y_$4, screenX$5, screenY$6, ls1$7, ls2$8, param0$9, param1$10, s$11, t2$12, tmp$13, tmp$14, curDepth$15, tmp$16, stackDelayRes$17, curDepth$18, lscomp1$capture$0)
};
Cont$func$lscomp2$mandel$_mls_L0_1415_1527$$ctor = function Cont$func$lscomp2$mandel$_mls_L0_1415_1527$$ctor(x$1, y$2, x_$3, y_$4, screenX$5, screenY$6, ls1$7, ls2$8, param0$9, param1$10, s$11, t2$12, tmp$13, tmp$14, curDepth$15, tmp$16, stackDelayRes$17, curDepth$18, lscomp1$capture$0) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lscomp2$mandel$_mls_L0_1415_1527$1.class(pc);
    return tmp(x$1, y$2, x_$3, y_$4, screenX$5, screenY$6, ls1$7, ls2$8, param0$9, param1$10, s$11, t2$12, tmp$13, tmp$14, curDepth$15, tmp$16, stackDelayRes$17, curDepth$18, lscomp1$capture$0)
  }
};
Cont$func$lscomp2$mandel$_mls_L0_1415_1527$1 = function Cont$func$lscomp2$mandel$_mls_L0_1415_1527$(pc1) {
  return (x$11, y$21, x_$31, y_$41, screenX$51, screenY$61, ls1$71, ls2$81, param0$91, param1$101, s$111, t2$121, tmp$131, tmp$141, curDepth$151, tmp$161, stackDelayRes$171, curDepth$181, lscomp1$capture$01) => {
    return new Cont$func$lscomp2$mandel$_mls_L0_1415_1527$.class(pc1)(x$11, y$21, x_$31, y_$41, screenX$51, screenY$61, ls1$71, ls2$81, param0$91, param1$101, s$111, t2$121, tmp$131, tmp$141, curDepth$151, tmp$161, stackDelayRes$171, curDepth$181, lscomp1$capture$01);
  }
};
Cont$func$lscomp2$mandel$_mls_L0_1415_1527$1.class = class Cont$func$lscomp2$mandel$_mls_L0_1415_1527$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$1, y$2, x_$3, y_$4, screenX$5, screenY$6, ls1$7, ls2$8, param0$9, param1$10, s$11, t2$12, tmp$13, tmp$14, curDepth$15, tmp$16, stackDelayRes$17, curDepth$18, lscomp1$capture$0) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$1 = x$1;
      this.y$2 = y$2;
      this.x_$3 = x_$3;
      this.y_$4 = y_$4;
      this.screenX$5 = screenX$5;
      this.screenY$6 = screenY$6;
      this.ls1$7 = ls1$7;
      this.ls2$8 = ls2$8;
      this.param0$9 = param0$9;
      this.param1$10 = param1$10;
      this.s$11 = s$11;
      this.t2$12 = t2$12;
      this.tmp$13 = tmp$13;
      this.tmp$14 = tmp$14;
      this.curDepth$15 = curDepth$15;
      this.tmp$16 = tmp$16;
      this.stackDelayRes$17 = stackDelayRes$17;
      this.curDepth$18 = curDepth$18;
      this.lscomp1$capture$0 = lscomp1$capture$0;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 56) {
      this.stackDelayRes$17 = value$;
    } else if (this.pc === 59) {
      this.tmp$16 = value$;
    } else if (this.pc === 57) {
      this.tmp$13 = value$;
    } else if (this.pc === 58) {
      this.tmp$14 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 56) {
        if (this.ls2$8 instanceof NofibPrelude.Nil.class) {
          this.pc = 61;
          continue contLoop;
        } else if (this.ls2$8 instanceof NofibPrelude.Cons.class) {
          this.param0$9 = this.ls2$8.head;
          this.param1$10 = this.ls2$8.tail;
          this.s$11 = this.param0$9;
          this.t2$12 = this.param1$10;
          this.pc = 64;
          continue contLoop;
          this.pc = 60;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$16 = new globalThis.Error("match error");
          if (this.tmp$16 instanceof runtime.EffectSig.class) {
            this.pc = 59;
            this.tmp$16.contTrace.last.next = this;
            this.tmp$16.contTrace.last = this;
            return this.tmp$16
          }
          this.pc = 59;
          continue contLoop;
        }
        this.pc = 60;
        continue contLoop;
      } else if (this.pc === 60) {
        break contLoop;
      } else if (this.pc === 59) {
        this.tmp$16 = runtime.resetDepth(this.tmp$16, this.curDepth$15);
        throw this.tmp$16;
      } else if (this.pc === 62) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.tmp$13, this.tmp$14)
      } else if (this.pc === 64) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$13 = windowToViewport$(this.x$1, this.y$2, this.x_$3, this.y_$4, this.screenX$5, this.screenY$6, this.s$11, this.lscomp1$capture$0.t2$);
        if (this.tmp$13 instanceof runtime.EffectSig.class) {
          this.pc = 57;
          this.tmp$13.contTrace.last.next = this;
          this.tmp$13.contTrace.last = this;
          return this.tmp$13
        }
        this.pc = 57;
        continue contLoop;
      } else if (this.pc === 57) {
        this.tmp$13 = runtime.resetDepth(this.tmp$13, this.curDepth$15);
        this.pc = 63;
        continue contLoop;
      } else if (this.pc === 63) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$14 = lscomp2$(this.x$1, this.y$2, this.x_$3, this.y_$4, this.screenX$5, this.screenY$6, this.ls1$7, this.curDepth$18, this.lscomp1$capture$0, this.t2$12);
        if (this.tmp$14 instanceof runtime.EffectSig.class) {
          this.pc = 58;
          this.tmp$14.contTrace.last.next = this;
          this.tmp$14.contTrace.last = this;
          return this.tmp$14
        }
        this.pc = 58;
        continue contLoop;
      } else if (this.pc === 58) {
        this.tmp$14 = runtime.resetDepth(this.tmp$14, this.curDepth$15);
        this.pc = 62;
        continue contLoop;
      } else if (this.pc === 61) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return lscomp1$(this.x$1, this.y$2, this.x_$3, this.y_$4, this.screenX$5, this.screenY$6, this.lscomp1$capture$0.t16$)
      }
      break;
    }
  }
  toString() { return "Cont$func$lscomp2$mandel$_mls_L0_1415_1527$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lscomp2$ = function lscomp2$(x, y, x_, y_, screenX, screenY, ls1, curDepth, lscomp1$capture2, ls2) {
  let param0, param1, s, t2, tmp, tmp1, curDepth1, tmp2, stackDelayRes;
  curDepth1 = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lscomp2$mandel$_mls_L0_1415_1527$$(x, y, x_, y_, screenX, screenY, ls1, ls2, param0, param1, s, t2, tmp, tmp1, curDepth1, tmp2, stackDelayRes, curDepth, lscomp1$capture2, 56);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (ls2 instanceof NofibPrelude.Nil.class) {
    runtime.stackDepth = runtime.stackDepth + 1;
    return lscomp1$(x, y, x_, y_, screenX, screenY, lscomp1$capture2.t16$)
  } else if (ls2 instanceof NofibPrelude.Cons.class) {
    param0 = ls2.head;
    param1 = ls2.tail;
    s = param0;
    t2 = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = windowToViewport$(x, y, x_, y_, screenX, screenY, s, lscomp1$capture2.t2$);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$lscomp2$mandel$_mls_L0_1415_1527$$(x, y, x_, y_, screenX, screenY, ls1, ls2, param0, param1, s, t2, tmp, tmp1, curDepth1, tmp2, stackDelayRes, curDepth, lscomp1$capture2, 57);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth1);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = lscomp2$(x, y, x_, y_, screenX, screenY, ls1, curDepth, lscomp1$capture2, t2);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$lscomp2$mandel$_mls_L0_1415_1527$$(x, y, x_, y_, screenX, screenY, ls1, ls2, param0, param1, s, t2, tmp, tmp1, curDepth1, tmp2, stackDelayRes, curDepth, lscomp1$capture2, 58);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth1);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.Cons(tmp, tmp1)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = new globalThis.Error("match error");
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$lscomp2$mandel$_mls_L0_1415_1527$$(x, y, x_, y_, screenX, screenY, ls1, ls2, param0, param1, s, t2, tmp, tmp1, curDepth1, tmp2, stackDelayRes, curDepth, lscomp1$capture2, 59);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth1);
    throw tmp2;
  }
};
lscomp2 = function lscomp2(x, y, x_, y_, screenX, screenY, ls1, curDepth, lscomp1$capture2) {
  return (ls2) => {
    return lscomp2$(x, y, x_, y_, screenX, screenY, ls1, curDepth, lscomp1$capture2, ls2)
  }
};
lscomp1$capture1 = function lscomp1$capture(param10$1, tmp1$1, t2$1, tmp3$1, stackDelayRes4$1, param05$1, t16$1) {
  return new lscomp1$capture.class(param10$1, tmp1$1, t2$1, tmp3$1, stackDelayRes4$1, param05$1, t16$1);
};
lscomp1$capture1.class = class lscomp1$capture {
  constructor(param10$, tmp1$, t2$, tmp3$, stackDelayRes4$, param05$, t16$) {
    this.param10$ = param10$;
    this.tmp1$ = tmp1$;
    this.t2$ = t2$;
    this.tmp3$ = tmp3$;
    this.stackDelayRes4$ = stackDelayRes4$;
    this.param05$ = param05$;
    this.t16$ = t16$;
  }
  toString() { return "lscomp1$capture(" + globalThis.Predef.render(this.param10$) + ", " + globalThis.Predef.render(this.tmp1$) + ", " + globalThis.Predef.render(this.t2$) + ", " + globalThis.Predef.render(this.tmp3$) + ", " + globalThis.Predef.render(this.stackDelayRes4$) + ", " + globalThis.Predef.render(this.param05$) + ", " + globalThis.Predef.render(this.t16$) + ")"; }
};
lscomp1$ = function lscomp1$(x, y, x_, y_, screenX, screenY, ls1) {
  let curDepth, capture;
  capture = new lscomp1$capture1(null, null, null, null, null, null, null);
  curDepth = runtime.stackDepth;
  capture.stackDelayRes4$ = runtime.checkDepth();
  if (capture.stackDelayRes4$ instanceof runtime.EffectSig.class) {
    capture.stackDelayRes4$.contTrace.last.next = Cont$func$lscomp1$mandel$_mls_L0_1346_1565$$(x, y, x_, y_, screenX, screenY, ls1, curDepth, capture, 55);
    capture.stackDelayRes4$.contTrace.last = capture.stackDelayRes4$.contTrace.last.next;
    return capture.stackDelayRes4$
  }
  if (ls1 instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls1 instanceof NofibPrelude.Cons.class) {
    capture.param05$ = ls1.head;
    capture.param10$ = ls1.tail;
    capture.t2$ = capture.param05$;
    capture.t16$ = capture.param10$;
    runtime.stackDepth = runtime.stackDepth + 1;
    capture.tmp3$ = NofibPrelude.enumFromTo(1, screenX);
    if (capture.tmp3$ instanceof runtime.EffectSig.class) {
      capture.tmp3$.contTrace.last.next = Cont$func$lscomp1$mandel$_mls_L0_1346_1565$$(x, y, x_, y_, screenX, screenY, ls1, curDepth, capture, 65);
      capture.tmp3$.contTrace.last = capture.tmp3$.contTrace.last.next;
      return capture.tmp3$
    }
    capture.tmp3$ = runtime.resetDepth(capture.tmp3$, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return lscomp2$(x, y, x_, y_, screenX, screenY, ls1, curDepth, capture, capture.tmp3$)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    capture.tmp1$ = new globalThis.Error("match error");
    if (capture.tmp1$ instanceof runtime.EffectSig.class) {
      capture.tmp1$.contTrace.last.next = Cont$func$lscomp1$mandel$_mls_L0_1346_1565$$(x, y, x_, y_, screenX, screenY, ls1, curDepth, capture, 66);
      capture.tmp1$.contTrace.last = capture.tmp1$.contTrace.last.next;
      return capture.tmp1$
    }
    capture.tmp1$ = runtime.resetDepth(capture.tmp1$, curDepth);
    throw capture.tmp1$;
  }
};
lscomp1 = function lscomp1(x, y, x_, y_, screenX, screenY) {
  return (ls1) => {
    return lscomp1$(x, y, x_, y_, screenX, screenY, ls1)
  }
};
mandelset = function mandelset(x, y, x_, y_, screenX, screenY, lIMIT) {
  let result, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, prettyRGB$this;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$mandelset$mandel$_mls_L0_1119_1730$$(x, y, x_, y_, screenX, screenY, lIMIT, result, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 52);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = NofibPrelude.enumFromTo(1, screenY);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$mandelset$mandel$_mls_L0_1119_1730$$(x, y, x_, y_, screenX, screenY, lIMIT, result, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 70);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = lscomp1$(x, y, x_, y_, screenX, screenY, tmp);
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$mandelset$mandel$_mls_L0_1119_1730$$(x, y, x_, y_, screenX, screenY, lIMIT, result, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 71);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  tmp2 = x_ - x;
  tmp3 = y_ - y;
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp4 = NofibPrelude.max(tmp2, tmp3);
  if (tmp4 instanceof runtime.EffectSig.class) {
    tmp4.contTrace.last.next = Cont$func$mandelset$mandel$_mls_L0_1119_1730$$(x, y, x_, y_, screenX, screenY, lIMIT, result, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 72);
    tmp4.contTrace.last = tmp4.contTrace.last.next;
    return tmp4
  }
  tmp4 = runtime.resetDepth(tmp4, curDepth);
  tmp5 = tmp4 / 2;
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp6 = parallelMandel(tmp1, lIMIT, tmp5);
  if (tmp6 instanceof runtime.EffectSig.class) {
    tmp6.contTrace.last.next = Cont$func$mandelset$mandel$_mls_L0_1119_1730$$(x, y, x_, y_, screenX, screenY, lIMIT, result, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 73);
    tmp6.contTrace.last = tmp6.contTrace.last.next;
    return tmp6
  }
  tmp6 = runtime.resetDepth(tmp6, curDepth);
  result = tmp6;
  runtime.stackDepth = runtime.stackDepth + 1;
  prettyRGB$this = runtime.safeCall(prettyRGB(lIMIT));
  tmp7 = NofibPrelude.map(prettyRGB$this, result);
  if (tmp7 instanceof runtime.EffectSig.class) {
    tmp7.contTrace.last.next = Cont$func$mandelset$mandel$_mls_L0_1119_1730$$(x, y, x_, y_, screenX, screenY, lIMIT, result, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 74);
    tmp7.contTrace.last = tmp7.contTrace.last.next;
    return tmp7
  }
  tmp7 = runtime.resetDepth(tmp7, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return createPixmap(screenX, screenY, lIMIT, tmp7)
};
Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$$ = function Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$$(minx$0, miny$1, maxx$2, maxy$3, screenX$4, screenY$5, limit$6, tmp$7, tmp$8, stackDelayRes$9, pc) {
  let tmp;
  tmp = new Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$1.class(pc);
  return tmp(minx$0, miny$1, maxx$2, maxy$3, screenX$4, screenY$5, limit$6, tmp$7, tmp$8, stackDelayRes$9)
};
Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$$ctor = function Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$$ctor(minx$0, miny$1, maxx$2, maxy$3, screenX$4, screenY$5, limit$6, tmp$7, tmp$8, stackDelayRes$9) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$1.class(pc);
    return tmp(minx$0, miny$1, maxx$2, maxy$3, screenX$4, screenY$5, limit$6, tmp$7, tmp$8, stackDelayRes$9)
  }
};
Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$1 = function Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$(pc1) {
  return (minx$01, miny$11, maxx$21, maxy$31, screenX$41, screenY$51, limit$61, tmp$71, tmp$81, stackDelayRes$91) => {
    return new Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$.class(pc1)(minx$01, miny$11, maxx$21, maxy$31, screenX$41, screenY$51, limit$61, tmp$71, tmp$81, stackDelayRes$91);
  }
};
Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$1.class = class Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (minx$0, miny$1, maxx$2, maxy$3, screenX$4, screenY$5, limit$6, tmp$7, tmp$8, stackDelayRes$9) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.minx$0 = minx$0;
      this.miny$1 = miny$1;
      this.maxx$2 = maxx$2;
      this.maxy$3 = maxy$3;
      this.screenX$4 = screenX$4;
      this.screenY$5 = screenY$5;
      this.limit$6 = limit$6;
      this.tmp$7 = tmp$7;
      this.tmp$8 = tmp$8;
      this.stackDelayRes$9 = stackDelayRes$9;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 81) {
      this.stackDelayRes$9 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 81) {
        this.tmp$7 = - 2.0;
        this.minx$0 = this.tmp$7;
        this.tmp$8 = - 2.0;
        this.miny$1 = this.tmp$8;
        this.maxx$2 = 2.0;
        this.maxy$3 = 2.0;
        this.screenX$4 = 25;
        this.screenY$5 = 25;
        this.limit$6 = 75;
        this.pc = 82;
        continue contLoop;
      } else if (this.pc === 82) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return mandelset(this.minx$0, this.miny$1, this.maxx$2, this.maxy$3, this.screenX$4, this.screenY$5, this.limit$6)
      }
      break;
    }
  }
  toString() { return "Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$(" + globalThis.Predef.render(this.pc) + ")"; }
};
testMandel_nofib = function testMandel_nofib(dummy) {
  let minx, miny, maxx, maxy, screenX, screenY, limit, tmp, tmp1, stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$testMandel_nofib$mandel$_mls_L0_1737_1948$$(minx, miny, maxx, maxy, screenX, screenY, limit, tmp, tmp1, stackDelayRes, 81);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  tmp = - 2.0;
  minx = tmp;
  tmp1 = - 2.0;
  miny = tmp1;
  maxx = 2.0;
  maxy = 2.0;
  screenX = 25;
  screenY = 25;
  limit = 75;
  runtime.stackDepth = runtime.stackDepth + 1;
  return mandelset(minx, miny, maxx, maxy, screenX, screenY, limit)
};
Pixmap1 = function Pixmap(a1, b1, c1, d1) {
  return new Pixmap.class(a1, b1, c1, d1);
};
Pixmap1.class = class Pixmap {
  constructor(a, b, c, d) {
    this.a = a;
    this.b = b;
    this.c = c;
    this.d = d;
  }
  toString() { return "Pixmap(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.c) + ", " + globalThis.Predef.render(this.d) + ")"; }
};
Complex1 = function Complex(r1, i1) {
  return new Complex.class(r1, i1);
};
Complex1.class = class Complex {
  constructor(r, i) {
    this.r = r;
    this.i = i;
  }
  toString() { return "Complex(" + globalThis.Predef.render(this.r) + ", " + globalThis.Predef.render(this.i) + ")"; }
};
Cont$func$lambda$$$3 = function Cont$func$lambda$$$(tmp$0, curDepth$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$7.class(pc);
  return tmp(tmp$0, curDepth$1, stackDelayRes$2)
};
Cont$func$lambda$$$ctor3 = function Cont$func$lambda$$$ctor(tmp$0, curDepth$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$7.class(pc);
    return tmp(tmp$0, curDepth$1, stackDelayRes$2)
  }
};
Cont$func$lambda$$7 = function Cont$func$lambda$$(pc1) {
  return (tmp$01, curDepth$11, stackDelayRes$21) => {
    return new Cont$func$lambda$$.class(pc1)(tmp$01, curDepth$11, stackDelayRes$21);
  }
};
Cont$func$lambda$$7.class = class Cont$func$lambda$$3 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (tmp$0, curDepth$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.tmp$0 = tmp$0;
      this.curDepth$1 = curDepth$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 83) {
      this.stackDelayRes$2 = value$;
    } else if (this.pc === 84) {
      this.tmp$0 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 83) {
        this.pc = 86;
        continue contLoop;
      } else if (this.pc === 86) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$0 = testMandel_nofib(0);
        if (this.tmp$0 instanceof runtime.EffectSig.class) {
          this.pc = 84;
          this.tmp$0.contTrace.last.next = this;
          this.tmp$0.contTrace.last = this;
          return this.tmp$0
        }
        this.pc = 84;
        continue contLoop;
      } else if (this.pc === 84) {
        this.tmp$0 = runtime.resetDepth(this.tmp$0, this.curDepth$1);
        this.pc = 85;
        continue contLoop;
      } else if (this.pc === 85) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.tmp$0.toString())
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda3 = (undefined, function () {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$3(tmp, curDepth, stackDelayRes, 83);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = testMandel_nofib(0);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$3(tmp, curDepth, stackDelayRes, 84);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return runtime.safeCall(tmp.toString())
});
lambda4 = (undefined, function () {
  return BenchmarkPrelude.benchmark(lambda3)
});
res = runtime.runStackSafe(500, lambda4);
if (res instanceof runtime.EffectSig.class) {
  throw new this.Error("Unhandled effects");
}
res