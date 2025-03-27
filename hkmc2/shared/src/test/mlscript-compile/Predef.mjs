import runtime from "./Runtime.mjs";
import Runtime from "./Runtime.mjs";
let Predef1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, Cont$func$apply$Predef$_mls_L0_94_128$1, Cont$func$pipeInto$Predef$_mls_L0_134_160$1, Cont$func$pipeFrom$Predef$_mls_L0_165_191$1, Cont$func$tap$Predef$_mls_L0_197_221$1, Cont$func$pat$Predef$_mls_L0_226_250$1, Cont$func$andThen$Predef$_mls_L0_256_287$1, Cont$func$compose$Predef$_mls_L0_292_323$1, Cont$func$passTo$Predef$_mls_L0_329_384$1, Cont$func$call$Predef$_mls_L0_390_450$1, Cont$func$pass1$Predef$_mls_L0_456_481$1, Cont$func$pass2$Predef$_mls_L0_486_517$1, Cont$func$pass3$Predef$_mls_L0_522_559$1, Cont$func$passing$Predef$_mls_L0_565_608$1, Cont$func$print$Predef$_mls_L0_615_671$1, Cont$func$printRaw$Predef$_mls_L0_677_715$1, Cont$func$interleave$Predef$_mls_L0_721_998$1, Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$1, Cont$func$lambda$$3, Cont$func$lambda$$4, Cont$func$render$Predef$_mls_L0_1070_2080$1, Cont$func$notImplemented$Predef$_mls_L0_2115_2180$1, Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$1, Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$1, Cont$func$tupleGet$Predef$_mls_L0_2481_2617$1, Cont$func$map$Predef$_mls_L0_2623_2655$1, Cont$func$fold$Predef$_mls_L0_2661_2803$1, Cont$func$foldr$Predef$_mls_L0_2886_3101$1, Cont$func$lambda$$5, Cont$func$mkStr$Predef$_mls_L0_3107_3176$1, Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$1, Cont$func$stringGet$Predef$_mls_L0_3249_3284$1, Cont$func$stringDrop$Predef$_mls_L0_3290_3329$1, Cont$func$unreachable$Predef$_mls_L0_3336_3376$1, Cont$func$checkArgs$Predef$_mls_L0_3382_3927$1, Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$1, Cont$func$log$Predef$_mls_L0_4207_4345$1, Cont$func$log$Predef$_mls_L0_4207_4345$$ctor, Cont$func$log$Predef$_mls_L0_4207_4345$$, Cont$func$apply$Predef$_mls_L0_94_128$$ctor, Cont$func$apply$Predef$_mls_L0_94_128$$, Cont$func$pipeInto$Predef$_mls_L0_134_160$$ctor, Cont$func$pipeInto$Predef$_mls_L0_134_160$$, Cont$func$pipeFrom$Predef$_mls_L0_165_191$$ctor, Cont$func$pipeFrom$Predef$_mls_L0_165_191$$, Cont$func$tap$Predef$_mls_L0_197_221$$ctor, Cont$func$tap$Predef$_mls_L0_197_221$$, Cont$func$pat$Predef$_mls_L0_226_250$$ctor, Cont$func$pat$Predef$_mls_L0_226_250$$, Cont$func$andThen$Predef$_mls_L0_256_287$$ctor, Cont$func$andThen$Predef$_mls_L0_256_287$$, Cont$func$compose$Predef$_mls_L0_292_323$$ctor, Cont$func$compose$Predef$_mls_L0_292_323$$, Cont$func$passTo$Predef$_mls_L0_329_384$$ctor, Cont$func$passTo$Predef$_mls_L0_329_384$$, Cont$func$call$Predef$_mls_L0_390_450$$ctor, Cont$func$call$Predef$_mls_L0_390_450$$, Cont$func$pass1$Predef$_mls_L0_456_481$$ctor, Cont$func$pass1$Predef$_mls_L0_456_481$$, Cont$func$pass2$Predef$_mls_L0_486_517$$ctor, Cont$func$pass2$Predef$_mls_L0_486_517$$, Cont$func$pass3$Predef$_mls_L0_522_559$$ctor, Cont$func$pass3$Predef$_mls_L0_522_559$$, Cont$func$passing$Predef$_mls_L0_565_608$$ctor, Cont$func$passing$Predef$_mls_L0_565_608$$, Cont$func$print$Predef$_mls_L0_615_671$$ctor, Cont$func$print$Predef$_mls_L0_615_671$$, Cont$func$printRaw$Predef$_mls_L0_677_715$$ctor, Cont$func$printRaw$Predef$_mls_L0_677_715$$, Cont$func$interleave$Predef$_mls_L0_721_998$$ctor, Cont$func$interleave$Predef$_mls_L0_721_998$$, Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$$ctor, Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$$, Cont$func$lambda$$$ctor, Cont$func$lambda$$$, Cont$func$lambda$$$ctor1, Cont$func$lambda$$$1, Cont$func$render$Predef$_mls_L0_1070_2080$$ctor, Cont$func$render$Predef$_mls_L0_1070_2080$$, Cont$func$notImplemented$Predef$_mls_L0_2115_2180$$ctor, Cont$func$notImplemented$Predef$_mls_L0_2115_2180$$, Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$$ctor, Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$$, Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$$ctor, Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$$, Cont$func$tupleGet$Predef$_mls_L0_2481_2617$$ctor, Cont$func$tupleGet$Predef$_mls_L0_2481_2617$$, Cont$func$map$Predef$_mls_L0_2623_2655$$ctor, Cont$func$map$Predef$_mls_L0_2623_2655$$, Cont$func$fold$Predef$_mls_L0_2661_2803$$ctor, Cont$func$fold$Predef$_mls_L0_2661_2803$$, Cont$func$foldr$Predef$_mls_L0_2886_3101$$ctor, Cont$func$foldr$Predef$_mls_L0_2886_3101$$, Cont$func$lambda$$$ctor2, Cont$func$lambda$$$2, Cont$func$mkStr$Predef$_mls_L0_3107_3176$$ctor, Cont$func$mkStr$Predef$_mls_L0_3107_3176$$, Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$$ctor, Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$$, Cont$func$stringGet$Predef$_mls_L0_3249_3284$$ctor, Cont$func$stringGet$Predef$_mls_L0_3249_3284$$, Cont$func$stringDrop$Predef$_mls_L0_3290_3329$$ctor, Cont$func$stringDrop$Predef$_mls_L0_3290_3329$$, Cont$func$unreachable$Predef$_mls_L0_3336_3376$$ctor, Cont$func$unreachable$Predef$_mls_L0_3336_3376$$, Cont$func$checkArgs$Predef$_mls_L0_3382_3927$$ctor, Cont$func$checkArgs$Predef$_mls_L0_3382_3927$$, Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$$ctor, Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$$;
Cont$func$log$Predef$_mls_L0_4207_4345$$ = function Cont$func$log$Predef$_mls_L0_4207_4345$$(TraceLogger$instance$9, msg$0, scrut$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8, pc) {
  let tmp;
  tmp = new Cont$func$log$Predef$_mls_L0_4207_4345$1.class(pc);
  return tmp(TraceLogger$instance$9, msg$0, scrut$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8)
};
Cont$func$log$Predef$_mls_L0_4207_4345$$ctor = function Cont$func$log$Predef$_mls_L0_4207_4345$$ctor(TraceLogger$instance$9, msg$0, scrut$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$log$Predef$_mls_L0_4207_4345$1.class(pc);
    return tmp(TraceLogger$instance$9, msg$0, scrut$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8)
  }
};
Cont$func$log$Predef$_mls_L0_4207_4345$1 = function Cont$func$log$Predef$_mls_L0_4207_4345$(pc1) {
  return (TraceLogger$instance$91, msg$01, scrut$11, tmp$21, tmp$31, tmp$41, tmp$51, tmp$61, curDepth$71, stackDelayRes$81) => {
    return new Cont$func$log$Predef$_mls_L0_4207_4345$.class(pc1)(TraceLogger$instance$91, msg$01, scrut$11, tmp$21, tmp$31, tmp$41, tmp$51, tmp$61, curDepth$71, stackDelayRes$81);
  }
};
Cont$func$log$Predef$_mls_L0_4207_4345$1.class = class Cont$func$log$Predef$_mls_L0_4207_4345$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (TraceLogger$instance$9, msg$0, scrut$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8) => {
      let tmp;
      tmp = super(null);
      this.TraceLogger$instance$9 = TraceLogger$instance$9;
      this.msg$0 = msg$0;
      this.scrut$1 = scrut$1;
      this.tmp$2 = tmp$2;
      this.tmp$3 = tmp$3;
      this.tmp$4 = tmp$4;
      this.tmp$5 = tmp$5;
      this.tmp$6 = tmp$6;
      this.curDepth$7 = curDepth$7;
      this.stackDelayRes$8 = stackDelayRes$8;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 192) {
      this.stackDelayRes$8 = value$;
    } else if (this.pc === 193) {
      this.tmp$2 = value$;
    } else if (this.pc === 194) {
      this.tmp$3 = value$;
    } else if (this.pc === 195) {
      this.tmp$5 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 192) {
        this.scrut$1 = this.TraceLogger$instance$9.enabled;
        if (this.scrut$1 === true) {
          this.pc = 200;
          continue contLoop;
        } else {
          return runtime.Unit
        }
        this.pc = 196;
        continue contLoop;
      } else if (this.pc === 196) {
        break contLoop;
      } else if (this.pc === 197) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(globalThis.console.log(this.tmp$6))
      } else if (this.pc === 200) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = runtime.safeCall("| ".repeat(this.TraceLogger$instance$9.indentLvl));
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 193;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 193;
        continue contLoop;
      } else if (this.pc === 193) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$7);
        this.pc = 199;
        continue contLoop;
      } else if (this.pc === 198) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = this.msg$0.replaceAll("\n", this.tmp$4);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 195;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 195;
        continue contLoop;
      } else if (this.pc === 199) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = runtime.safeCall("  ".repeat(this.TraceLogger$instance$9.indentLvl));
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 194;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 194;
        continue contLoop;
      } else if (this.pc === 194) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$7);
        this.tmp$4 = "\n" + this.tmp$3;
        this.pc = 198;
        continue contLoop;
      } else if (this.pc === 195) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$7);
        this.tmp$6 = this.tmp$2 + this.tmp$5;
        this.pc = 197;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$log$Predef$_mls_L0_4207_4345$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$$ = function Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$$(handler$0, body$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$1.class(pc);
  return tmp(handler$0, body$1, stackDelayRes$2)
};
Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$$ctor = function Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$$ctor(handler$0, body$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$1.class(pc);
    return tmp(handler$0, body$1, stackDelayRes$2)
  }
};
Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$1 = function Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$(pc1) {
  return (handler$01, body$11, stackDelayRes$21) => {
    return new Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$.class(pc1)(handler$01, body$11, stackDelayRes$21);
  }
};
Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$1.class = class Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (handler$0, body$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.handler$0 = handler$0;
      this.body$1 = body$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 190) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 190) {
        this.pc = 191;
        continue contLoop;
      } else if (this.pc === 191) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Runtime.enterHandleBlock(this.handler$0, this.body$1)
      }
      break;
    }
  }
  toString() { return "Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$checkArgs$Predef$_mls_L0_3382_3927$$ = function Cont$func$checkArgs$Predef$_mls_L0_3382_3927$$(functionName$0, expected$1, isUB$2, got$3, scrut$4, name$5, scrut$6, scrut$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, stackDelayRes$19, pc) {
  let tmp;
  tmp = new Cont$func$checkArgs$Predef$_mls_L0_3382_3927$1.class(pc);
  return tmp(functionName$0, expected$1, isUB$2, got$3, scrut$4, name$5, scrut$6, scrut$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, stackDelayRes$19)
};
Cont$func$checkArgs$Predef$_mls_L0_3382_3927$$ctor = function Cont$func$checkArgs$Predef$_mls_L0_3382_3927$$ctor(functionName$0, expected$1, isUB$2, got$3, scrut$4, name$5, scrut$6, scrut$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, stackDelayRes$19) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$checkArgs$Predef$_mls_L0_3382_3927$1.class(pc);
    return tmp(functionName$0, expected$1, isUB$2, got$3, scrut$4, name$5, scrut$6, scrut$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, stackDelayRes$19)
  }
};
Cont$func$checkArgs$Predef$_mls_L0_3382_3927$1 = function Cont$func$checkArgs$Predef$_mls_L0_3382_3927$(pc1) {
  return (functionName$01, expected$11, isUB$21, got$31, scrut$41, name$51, scrut$61, scrut$71, tmp$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, curDepth$171, tmp$181, stackDelayRes$191) => {
    return new Cont$func$checkArgs$Predef$_mls_L0_3382_3927$.class(pc1)(functionName$01, expected$11, isUB$21, got$31, scrut$41, name$51, scrut$61, scrut$71, tmp$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, curDepth$171, tmp$181, stackDelayRes$191);
  }
};
Cont$func$checkArgs$Predef$_mls_L0_3382_3927$1.class = class Cont$func$checkArgs$Predef$_mls_L0_3382_3927$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (functionName$0, expected$1, isUB$2, got$3, scrut$4, name$5, scrut$6, scrut$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, stackDelayRes$19) => {
      let tmp;
      tmp = super(null);
      this.functionName$0 = functionName$0;
      this.expected$1 = expected$1;
      this.isUB$2 = isUB$2;
      this.got$3 = got$3;
      this.scrut$4 = scrut$4;
      this.name$5 = name$5;
      this.scrut$6 = scrut$6;
      this.scrut$7 = scrut$7;
      this.tmp$8 = tmp$8;
      this.tmp$9 = tmp$9;
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
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 180) {
      this.stackDelayRes$19 = value$;
    } else if (this.pc === 181) {
      this.tmp$13 = value$;
    } else if (this.pc === 182) {
      this.tmp$16 = value$;
    } else if (this.pc === 183) {
      this.tmp$18 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 180) {
        this.tmp$8 = this.got$3 < this.expected$1;
        this.tmp$9 = this.got$3 > this.expected$1;
        this.tmp$10 = this.isUB$2 && this.tmp$9;
        this.scrut$4 = this.tmp$8 || this.tmp$10;
        if (this.scrut$4 === true) {
          this.scrut$6 = this.functionName$0.length > 0;
          if (this.scrut$6 === true) {
            this.tmp$11 = " '" + this.functionName$0;
            this.tmp$12 = this.tmp$11 + "'";
            this.pc = 189;
            continue contLoop;
          } else {
            this.tmp$12 = "";
            this.pc = 189;
            continue contLoop;
          }
          this.pc = 189;
          continue contLoop;
        } else {
          return runtime.Unit
        }
        this.pc = 184;
        continue contLoop;
      } else if (this.pc === 184) {
        break contLoop;
      } else if (this.pc === 189) {
        this.name$5 = this.tmp$12;
        this.pc = 188;
        continue contLoop;
      } else if (this.pc === 185) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$18 = globalThis.Error(this.tmp$16);
        if (this.tmp$18 instanceof runtime.EffectSig.class) {
          this.pc = 183;
          this.tmp$18.contTrace.last.next = this;
          this.tmp$18.contTrace.last = this;
          return this.tmp$18
        }
        this.pc = 183;
        continue contLoop;
      } else if (this.pc === 188) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$13 = Predef1.fold(lambda8);
        if (this.tmp$13 instanceof runtime.EffectSig.class) {
          this.pc = 181;
          this.tmp$13.contTrace.last.next = this;
          this.tmp$13.contTrace.last = this;
          return this.tmp$13
        }
        this.pc = 181;
        continue contLoop;
      } else if (this.pc === 181) {
        this.tmp$13 = runtime.resetDepth(this.tmp$13, this.curDepth$17);
        if (this.isUB$2 === true) {
          this.tmp$14 = "";
          this.pc = 187;
          continue contLoop;
        } else {
          this.tmp$14 = "at least ";
          this.pc = 187;
          continue contLoop;
        }
        this.pc = 187;
        continue contLoop;
      } else if (this.pc === 186) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$16 = runtime.safeCall(this.tmp$13("Function", this.name$5, " expected ", this.tmp$14, this.expected$1, " argument", this.tmp$15, " but got ", this.got$3));
        if (this.tmp$16 instanceof runtime.EffectSig.class) {
          this.pc = 182;
          this.tmp$16.contTrace.last.next = this;
          this.tmp$16.contTrace.last = this;
          return this.tmp$16
        }
        this.pc = 182;
        continue contLoop;
      } else if (this.pc === 187) {
        this.scrut$7 = this.expected$1 === 1;
        if (this.scrut$7 === true) {
          this.tmp$15 = "";
          this.pc = 186;
          continue contLoop;
        } else {
          this.tmp$15 = "s";
          this.pc = 186;
          continue contLoop;
        }
        this.pc = 186;
        continue contLoop;
      } else if (this.pc === 182) {
        this.tmp$16 = runtime.resetDepth(this.tmp$16, this.curDepth$17);
        this.pc = 185;
        continue contLoop;
      } else if (this.pc === 183) {
        this.tmp$18 = runtime.resetDepth(this.tmp$18, this.curDepth$17);
        throw this.tmp$18;
      }
      break;
    }
  }
  toString() { return "Cont$func$checkArgs$Predef$_mls_L0_3382_3927$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda8 = (undefined, function (arg1, arg2) {
  return arg1 + arg2
});
Cont$func$unreachable$Predef$_mls_L0_3336_3376$$ = function Cont$func$unreachable$Predef$_mls_L0_3336_3376$$(tmp$0, curDepth$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$unreachable$Predef$_mls_L0_3336_3376$1.class(pc);
  return tmp(tmp$0, curDepth$1, stackDelayRes$2)
};
Cont$func$unreachable$Predef$_mls_L0_3336_3376$$ctor = function Cont$func$unreachable$Predef$_mls_L0_3336_3376$$ctor(tmp$0, curDepth$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$unreachable$Predef$_mls_L0_3336_3376$1.class(pc);
    return tmp(tmp$0, curDepth$1, stackDelayRes$2)
  }
};
Cont$func$unreachable$Predef$_mls_L0_3336_3376$1 = function Cont$func$unreachable$Predef$_mls_L0_3336_3376$(pc1) {
  return (tmp$01, curDepth$11, stackDelayRes$21) => {
    return new Cont$func$unreachable$Predef$_mls_L0_3336_3376$.class(pc1)(tmp$01, curDepth$11, stackDelayRes$21);
  }
};
Cont$func$unreachable$Predef$_mls_L0_3336_3376$1.class = class Cont$func$unreachable$Predef$_mls_L0_3336_3376$ extends runtime.FunctionContFrame.class {
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
    if (this.pc === 177) {
      this.stackDelayRes$2 = value$;
    } else if (this.pc === 178) {
      this.tmp$0 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 177) {
        this.pc = 179;
        continue contLoop;
      } else if (this.pc === 179) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$0 = globalThis.Error("unreachable");
        if (this.tmp$0 instanceof runtime.EffectSig.class) {
          this.pc = 178;
          this.tmp$0.contTrace.last.next = this;
          this.tmp$0.contTrace.last = this;
          return this.tmp$0
        }
        this.pc = 178;
        continue contLoop;
      } else if (this.pc === 178) {
        this.tmp$0 = runtime.resetDepth(this.tmp$0, this.curDepth$1);
        throw this.tmp$0;
      }
      break;
    }
  }
  toString() { return "Cont$func$unreachable$Predef$_mls_L0_3336_3376$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$stringDrop$Predef$_mls_L0_3290_3329$$ = function Cont$func$stringDrop$Predef$_mls_L0_3290_3329$$(string$0, n$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$stringDrop$Predef$_mls_L0_3290_3329$1.class(pc);
  return tmp(string$0, n$1, stackDelayRes$2)
};
Cont$func$stringDrop$Predef$_mls_L0_3290_3329$$ctor = function Cont$func$stringDrop$Predef$_mls_L0_3290_3329$$ctor(string$0, n$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$stringDrop$Predef$_mls_L0_3290_3329$1.class(pc);
    return tmp(string$0, n$1, stackDelayRes$2)
  }
};
Cont$func$stringDrop$Predef$_mls_L0_3290_3329$1 = function Cont$func$stringDrop$Predef$_mls_L0_3290_3329$(pc1) {
  return (string$01, n$11, stackDelayRes$21) => {
    return new Cont$func$stringDrop$Predef$_mls_L0_3290_3329$.class(pc1)(string$01, n$11, stackDelayRes$21);
  }
};
Cont$func$stringDrop$Predef$_mls_L0_3290_3329$1.class = class Cont$func$stringDrop$Predef$_mls_L0_3290_3329$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (string$0, n$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.string$0 = string$0;
      this.n$1 = n$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 175) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 175) {
        this.pc = 176;
        continue contLoop;
      } else if (this.pc === 176) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.string$0.slice(this.n$1))
      }
      break;
    }
  }
  toString() { return "Cont$func$stringDrop$Predef$_mls_L0_3290_3329$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$stringGet$Predef$_mls_L0_3249_3284$$ = function Cont$func$stringGet$Predef$_mls_L0_3249_3284$$(string$0, i$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$stringGet$Predef$_mls_L0_3249_3284$1.class(pc);
  return tmp(string$0, i$1, stackDelayRes$2)
};
Cont$func$stringGet$Predef$_mls_L0_3249_3284$$ctor = function Cont$func$stringGet$Predef$_mls_L0_3249_3284$$ctor(string$0, i$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$stringGet$Predef$_mls_L0_3249_3284$1.class(pc);
    return tmp(string$0, i$1, stackDelayRes$2)
  }
};
Cont$func$stringGet$Predef$_mls_L0_3249_3284$1 = function Cont$func$stringGet$Predef$_mls_L0_3249_3284$(pc1) {
  return (string$01, i$11, stackDelayRes$21) => {
    return new Cont$func$stringGet$Predef$_mls_L0_3249_3284$.class(pc1)(string$01, i$11, stackDelayRes$21);
  }
};
Cont$func$stringGet$Predef$_mls_L0_3249_3284$1.class = class Cont$func$stringGet$Predef$_mls_L0_3249_3284$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (string$0, i$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.string$0 = string$0;
      this.i$1 = i$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 173) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 173) {
        this.pc = 174;
        continue contLoop;
      } else if (this.pc === 174) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.string$0.at(this.i$1))
      }
      break;
    }
  }
  toString() { return "Cont$func$stringGet$Predef$_mls_L0_3249_3284$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$$ = function Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$$(string$0, prefix$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$1.class(pc);
  return tmp(string$0, prefix$1, stackDelayRes$2)
};
Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$$ctor = function Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$$ctor(string$0, prefix$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$1.class(pc);
    return tmp(string$0, prefix$1, stackDelayRes$2)
  }
};
Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$1 = function Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$(pc1) {
  return (string$01, prefix$11, stackDelayRes$21) => {
    return new Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$.class(pc1)(string$01, prefix$11, stackDelayRes$21);
  }
};
Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$1.class = class Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (string$0, prefix$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.string$0 = string$0;
      this.prefix$1 = prefix$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 171) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 171) {
        this.pc = 172;
        continue contLoop;
      } else if (this.pc === 172) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.string$0.startsWith(this.prefix$1))
      }
      break;
    }
  }
  toString() { return "Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$mkStr$Predef$_mls_L0_3107_3176$$ = function Cont$func$mkStr$Predef$_mls_L0_3107_3176$$(xs$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$mkStr$Predef$_mls_L0_3107_3176$1.class(pc);
  return tmp(xs$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$mkStr$Predef$_mls_L0_3107_3176$$ctor = function Cont$func$mkStr$Predef$_mls_L0_3107_3176$$ctor(xs$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$mkStr$Predef$_mls_L0_3107_3176$1.class(pc);
    return tmp(xs$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$mkStr$Predef$_mls_L0_3107_3176$1 = function Cont$func$mkStr$Predef$_mls_L0_3107_3176$(pc1) {
  return (xs$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$mkStr$Predef$_mls_L0_3107_3176$.class(pc1)(xs$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$mkStr$Predef$_mls_L0_3107_3176$1.class = class Cont$func$mkStr$Predef$_mls_L0_3107_3176$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (xs$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.xs$0 = xs$0;
      this.tmp$1 = tmp$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 164) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 168) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 164) {
        this.tmp$1 = lambda7;
        this.pc = 170;
        continue contLoop;
      } else if (this.pc === 170) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = Predef1.fold(this.tmp$1);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 168;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 168;
        continue contLoop;
      } else if (this.pc === 168) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        this.pc = 169;
        continue contLoop;
      } else if (this.pc === 169) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.tmp$2(...this.xs$0))
      }
      break;
    }
  }
  toString() { return "Cont$func$mkStr$Predef$_mls_L0_3107_3176$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$2 = function Cont$func$lambda$$$(acc$0, x$1, tmp$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$5.class(pc);
  return tmp(acc$0, x$1, tmp$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6)
};
Cont$func$lambda$$$ctor2 = function Cont$func$lambda$$$ctor(acc$0, x$1, tmp$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$5.class(pc);
    return tmp(acc$0, x$1, tmp$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6)
  }
};
Cont$func$lambda$$5 = function Cont$func$lambda$$(pc1) {
  return (acc$01, x$11, tmp$21, tmp$31, tmp$41, curDepth$51, stackDelayRes$61) => {
    return new Cont$func$lambda$$.class(pc1)(acc$01, x$11, tmp$21, tmp$31, tmp$41, curDepth$51, stackDelayRes$61);
  }
};
Cont$func$lambda$$5.class = class Cont$func$lambda$$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (acc$0, x$1, tmp$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6) => {
      let tmp;
      tmp = super(null);
      this.acc$0 = acc$0;
      this.x$1 = x$1;
      this.tmp$2 = tmp$2;
      this.tmp$3 = tmp$3;
      this.tmp$4 = tmp$4;
      this.curDepth$5 = curDepth$5;
      this.stackDelayRes$6 = stackDelayRes$6;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 165) {
      this.stackDelayRes$6 = value$;
    } else if (this.pc === 166) {
      this.tmp$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 165) {
        if (typeof this.x$1 === 'string') {
          this.tmp$2 = true;
          this.pc = 167;
          continue contLoop;
        } else {
          this.tmp$2 = false;
          this.pc = 167;
          continue contLoop;
        }
        this.pc = 167;
        continue contLoop;
      } else if (this.pc === 167) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = runtime.safeCall(Predef1.assert(this.tmp$2));
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 166;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 166;
        continue contLoop;
      } else if (this.pc === 166) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$5);
        this.tmp$4 = this.acc$0 + this.x$1;
        return (this.tmp$3 , this.tmp$4)
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda7 = (undefined, function (acc, x) {
  let tmp, tmp1, tmp2, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$2(acc, x, tmp, tmp1, tmp2, curDepth, stackDelayRes, 165);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (typeof x === 'string') {
    tmp = true;
  } else {
    tmp = false;
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = runtime.safeCall(Predef1.assert(tmp));
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$lambda$$$2(acc, x, tmp, tmp1, tmp2, curDepth, stackDelayRes, 166);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  tmp2 = acc + x;
  return (tmp1 , tmp2)
});
Cont$func$foldr$Predef$_mls_L0_2886_3101$$ = function Cont$func$foldr$Predef$_mls_L0_2886_3101$$(f$0, first$1, rest$2, len$3, i$4, init$5, scrut$6, scrut$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, curDepth$14, stackDelayRes$15, pc) {
  let tmp;
  tmp = new Cont$func$foldr$Predef$_mls_L0_2886_3101$1.class(pc);
  return tmp(f$0, first$1, rest$2, len$3, i$4, init$5, scrut$6, scrut$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, curDepth$14, stackDelayRes$15)
};
Cont$func$foldr$Predef$_mls_L0_2886_3101$$ctor = function Cont$func$foldr$Predef$_mls_L0_2886_3101$$ctor(f$0, first$1, rest$2, len$3, i$4, init$5, scrut$6, scrut$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, curDepth$14, stackDelayRes$15) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$foldr$Predef$_mls_L0_2886_3101$1.class(pc);
    return tmp(f$0, first$1, rest$2, len$3, i$4, init$5, scrut$6, scrut$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, curDepth$14, stackDelayRes$15)
  }
};
Cont$func$foldr$Predef$_mls_L0_2886_3101$1 = function Cont$func$foldr$Predef$_mls_L0_2886_3101$(pc1) {
  return (f$01, first$11, rest$21, len$31, i$41, init$51, scrut$61, scrut$71, tmp$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, curDepth$141, stackDelayRes$151) => {
    return new Cont$func$foldr$Predef$_mls_L0_2886_3101$.class(pc1)(f$01, first$11, rest$21, len$31, i$41, init$51, scrut$61, scrut$71, tmp$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, curDepth$141, stackDelayRes$151);
  }
};
Cont$func$foldr$Predef$_mls_L0_2886_3101$1.class = class Cont$func$foldr$Predef$_mls_L0_2886_3101$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, first$1, rest$2, len$3, i$4, init$5, scrut$6, scrut$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, curDepth$14, stackDelayRes$15) => {
      let tmp;
      tmp = super(null);
      this.f$0 = f$0;
      this.first$1 = first$1;
      this.rest$2 = rest$2;
      this.len$3 = len$3;
      this.i$4 = i$4;
      this.init$5 = init$5;
      this.scrut$6 = scrut$6;
      this.scrut$7 = scrut$7;
      this.tmp$8 = tmp$8;
      this.tmp$9 = tmp$9;
      this.tmp$10 = tmp$10;
      this.tmp$11 = tmp$11;
      this.tmp$12 = tmp$12;
      this.tmp$13 = tmp$13;
      this.curDepth$14 = curDepth$14;
      this.stackDelayRes$15 = stackDelayRes$15;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 154) {
      this.stackDelayRes$15 = value$;
    } else if (this.pc === 155) {
      this.tmp$9 = value$;
    } else if (this.pc === 156) {
      this.tmp$11 = value$;
    } else if (this.pc === 157) {
      this.tmp$12 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 154) {
        this.len$3 = this.rest$2.length;
        this.scrut$7 = this.len$3 == 0;
        if (this.scrut$7 === true) {
          return this.first$1
        } else {
          this.tmp$8 = this.len$3 - 1;
          this.i$4 = this.tmp$8;
          this.pc = 163;
          continue contLoop;
        }
        this.pc = 158;
        continue contLoop;
      } else if (this.pc === 158) {
        break contLoop;
      } else if (this.pc === 163) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = runtime.safeCall(this.rest$2.at(this.i$4));
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 155;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 155;
        continue contLoop;
      } else if (this.pc === 155) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$14);
        this.init$5 = this.tmp$9;
        this.pc = 160;
        continue contLoop;
      } else if (this.pc === 160) {
        this.scrut$6 = this.i$4 > 0;
        if (this.scrut$6 === true) {
          this.tmp$10 = this.i$4 - 1;
          this.i$4 = this.tmp$10;
          this.pc = 162;
          continue contLoop;
        } else {
          this.tmp$13 = runtime.Unit;
          this.pc = 159;
          continue contLoop;
        }
        this.pc = 159;
        continue contLoop;
      } else if (this.pc === 161) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$12 = runtime.safeCall(this.f$0(this.tmp$11, this.init$5));
        if (this.tmp$12 instanceof runtime.EffectSig.class) {
          this.pc = 157;
          this.tmp$12.contTrace.last.next = this;
          this.tmp$12.contTrace.last = this;
          return this.tmp$12
        }
        this.pc = 157;
        continue contLoop;
      } else if (this.pc === 162) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$11 = runtime.safeCall(this.rest$2.at(this.i$4));
        if (this.tmp$11 instanceof runtime.EffectSig.class) {
          this.pc = 156;
          this.tmp$11.contTrace.last.next = this;
          this.tmp$11.contTrace.last = this;
          return this.tmp$11
        }
        this.pc = 156;
        continue contLoop;
      } else if (this.pc === 156) {
        this.tmp$11 = runtime.resetDepth(this.tmp$11, this.curDepth$14);
        this.pc = 161;
        continue contLoop;
      } else if (this.pc === 157) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$14);
        this.init$5 = this.tmp$12;
        this.tmp$13 = runtime.Unit;
        this.pc = 160;
        continue contLoop;
      } else if (this.pc === 159) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.f$0(this.first$1, this.init$5))
      }
      break;
    }
  }
  toString() { return "Cont$func$foldr$Predef$_mls_L0_2886_3101$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$fold$Predef$_mls_L0_2661_2803$$ = function Cont$func$fold$Predef$_mls_L0_2661_2803$$(f$0, init$1, rest$2, i$3, len$4, scrut$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11, pc) {
  let tmp;
  tmp = new Cont$func$fold$Predef$_mls_L0_2661_2803$1.class(pc);
  return tmp(f$0, init$1, rest$2, i$3, len$4, scrut$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11)
};
Cont$func$fold$Predef$_mls_L0_2661_2803$$ctor = function Cont$func$fold$Predef$_mls_L0_2661_2803$$ctor(f$0, init$1, rest$2, i$3, len$4, scrut$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$fold$Predef$_mls_L0_2661_2803$1.class(pc);
    return tmp(f$0, init$1, rest$2, i$3, len$4, scrut$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11)
  }
};
Cont$func$fold$Predef$_mls_L0_2661_2803$1 = function Cont$func$fold$Predef$_mls_L0_2661_2803$(pc1) {
  return (f$01, init$11, rest$21, i$31, len$41, scrut$51, tmp$61, tmp$71, tmp$81, tmp$91, curDepth$101, stackDelayRes$111) => {
    return new Cont$func$fold$Predef$_mls_L0_2661_2803$.class(pc1)(f$01, init$11, rest$21, i$31, len$41, scrut$51, tmp$61, tmp$71, tmp$81, tmp$91, curDepth$101, stackDelayRes$111);
  }
};
Cont$func$fold$Predef$_mls_L0_2661_2803$1.class = class Cont$func$fold$Predef$_mls_L0_2661_2803$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, init$1, rest$2, i$3, len$4, scrut$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11) => {
      let tmp;
      tmp = super(null);
      this.f$0 = f$0;
      this.init$1 = init$1;
      this.rest$2 = rest$2;
      this.i$3 = i$3;
      this.len$4 = len$4;
      this.scrut$5 = scrut$5;
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
    if (this.pc === 147) {
      this.stackDelayRes$11 = value$;
    } else if (this.pc === 148) {
      this.tmp$6 = value$;
    } else if (this.pc === 149) {
      this.tmp$7 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 147) {
        this.i$3 = 0;
        this.len$4 = this.rest$2.length;
        this.pc = 151;
        continue contLoop;
      } else if (this.pc === 150) {
        return this.init$1
      } else if (this.pc === 151) {
        this.scrut$5 = this.i$3 < this.len$4;
        if (this.scrut$5 === true) {
          this.pc = 153;
          continue contLoop;
        } else {
          this.tmp$9 = runtime.Unit;
          this.pc = 150;
          continue contLoop;
        }
        this.pc = 150;
        continue contLoop;
      } else if (this.pc === 152) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = runtime.safeCall(this.f$0(this.init$1, this.tmp$6));
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 149;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 149;
        continue contLoop;
      } else if (this.pc === 153) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = runtime.safeCall(this.rest$2.at(this.i$3));
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 148;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 148;
        continue contLoop;
      } else if (this.pc === 148) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$10);
        this.pc = 152;
        continue contLoop;
      } else if (this.pc === 149) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$10);
        this.init$1 = this.tmp$7;
        this.tmp$8 = this.i$3 + 1;
        this.i$3 = this.tmp$8;
        this.tmp$9 = runtime.Unit;
        this.pc = 151;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$fold$Predef$_mls_L0_2661_2803$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$map$Predef$_mls_L0_2623_2655$$ = function Cont$func$map$Predef$_mls_L0_2623_2655$$(f$0, xs$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$map$Predef$_mls_L0_2623_2655$1.class(pc);
  return tmp(f$0, xs$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$map$Predef$_mls_L0_2623_2655$$ctor = function Cont$func$map$Predef$_mls_L0_2623_2655$$ctor(f$0, xs$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$map$Predef$_mls_L0_2623_2655$1.class(pc);
    return tmp(f$0, xs$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$map$Predef$_mls_L0_2623_2655$1 = function Cont$func$map$Predef$_mls_L0_2623_2655$(pc1) {
  return (f$01, xs$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$map$Predef$_mls_L0_2623_2655$.class(pc1)(f$01, xs$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$map$Predef$_mls_L0_2623_2655$1.class = class Cont$func$map$Predef$_mls_L0_2623_2655$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, xs$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.f$0 = f$0;
      this.xs$1 = xs$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 143) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 144) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 143) {
        this.pc = 146;
        continue contLoop;
      } else if (this.pc === 145) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.xs$1.map(this.tmp$2))
      } else if (this.pc === 146) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = Predef1.pass1(this.f$0);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 144;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 144;
        continue contLoop;
      } else if (this.pc === 144) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        this.pc = 145;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$map$Predef$_mls_L0_2623_2655$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$tupleGet$Predef$_mls_L0_2481_2617$$ = function Cont$func$tupleGet$Predef$_mls_L0_2481_2617$$(xs$0, i$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$tupleGet$Predef$_mls_L0_2481_2617$1.class(pc);
  return tmp(xs$0, i$1, stackDelayRes$2)
};
Cont$func$tupleGet$Predef$_mls_L0_2481_2617$$ctor = function Cont$func$tupleGet$Predef$_mls_L0_2481_2617$$ctor(xs$0, i$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$tupleGet$Predef$_mls_L0_2481_2617$1.class(pc);
    return tmp(xs$0, i$1, stackDelayRes$2)
  }
};
Cont$func$tupleGet$Predef$_mls_L0_2481_2617$1 = function Cont$func$tupleGet$Predef$_mls_L0_2481_2617$(pc1) {
  return (xs$01, i$11, stackDelayRes$21) => {
    return new Cont$func$tupleGet$Predef$_mls_L0_2481_2617$.class(pc1)(xs$01, i$11, stackDelayRes$21);
  }
};
Cont$func$tupleGet$Predef$_mls_L0_2481_2617$1.class = class Cont$func$tupleGet$Predef$_mls_L0_2481_2617$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (xs$0, i$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.xs$0 = xs$0;
      this.i$1 = i$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 141) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 141) {
        this.pc = 142;
        continue contLoop;
      } else if (this.pc === 142) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return globalThis.Array.prototype.at.call(this.xs$0, this.i$1)
      }
      break;
    }
  }
  toString() { return "Cont$func$tupleGet$Predef$_mls_L0_2481_2617$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$$ = function Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$$(xs$0, i$1, j$2, tmp$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$1.class(pc);
  return tmp(xs$0, i$1, j$2, tmp$3, stackDelayRes$4)
};
Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$$ctor = function Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$$ctor(xs$0, i$1, j$2, tmp$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$1.class(pc);
    return tmp(xs$0, i$1, j$2, tmp$3, stackDelayRes$4)
  }
};
Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$1 = function Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$(pc1) {
  return (xs$01, i$11, j$21, tmp$31, stackDelayRes$41) => {
    return new Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$.class(pc1)(xs$01, i$11, j$21, tmp$31, stackDelayRes$41);
  }
};
Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$1.class = class Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (xs$0, i$1, j$2, tmp$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.xs$0 = xs$0;
      this.i$1 = i$1;
      this.j$2 = j$2;
      this.tmp$3 = tmp$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 139) {
      this.stackDelayRes$4 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 139) {
        this.tmp$3 = this.xs$0.length - this.j$2;
        this.pc = 140;
        continue contLoop;
      } else if (this.pc === 140) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(globalThis.Array.prototype.slice.call(this.xs$0, this.i$1, this.tmp$3))
      }
      break;
    }
  }
  toString() { return "Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$$ = function Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$$(tmp$0, curDepth$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$1.class(pc);
  return tmp(tmp$0, curDepth$1, stackDelayRes$2)
};
Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$$ctor = function Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$$ctor(tmp$0, curDepth$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$1.class(pc);
    return tmp(tmp$0, curDepth$1, stackDelayRes$2)
  }
};
Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$1 = function Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$(pc1) {
  return (tmp$01, curDepth$11, stackDelayRes$21) => {
    return new Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$.class(pc1)(tmp$01, curDepth$11, stackDelayRes$21);
  }
};
Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$1.class = class Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$ extends runtime.FunctionContFrame.class {
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
    if (this.pc === 136) {
      this.stackDelayRes$2 = value$;
    } else if (this.pc === 137) {
      this.tmp$0 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 136) {
        this.pc = 138;
        continue contLoop;
      } else if (this.pc === 138) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$0 = globalThis.Error("Not implemented");
        if (this.tmp$0 instanceof runtime.EffectSig.class) {
          this.pc = 137;
          this.tmp$0.contTrace.last.next = this;
          this.tmp$0.contTrace.last = this;
          return this.tmp$0
        }
        this.pc = 137;
        continue contLoop;
      } else if (this.pc === 137) {
        this.tmp$0 = runtime.resetDepth(this.tmp$0, this.curDepth$1);
        throw this.tmp$0;
      }
      break;
    }
  }
  toString() { return "Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$notImplemented$Predef$_mls_L0_2115_2180$$ = function Cont$func$notImplemented$Predef$_mls_L0_2115_2180$$(msg$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$notImplemented$Predef$_mls_L0_2115_2180$1.class(pc);
  return tmp(msg$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$notImplemented$Predef$_mls_L0_2115_2180$$ctor = function Cont$func$notImplemented$Predef$_mls_L0_2115_2180$$ctor(msg$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$notImplemented$Predef$_mls_L0_2115_2180$1.class(pc);
    return tmp(msg$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$notImplemented$Predef$_mls_L0_2115_2180$1 = function Cont$func$notImplemented$Predef$_mls_L0_2115_2180$(pc1) {
  return (msg$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$notImplemented$Predef$_mls_L0_2115_2180$.class(pc1)(msg$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$notImplemented$Predef$_mls_L0_2115_2180$1.class = class Cont$func$notImplemented$Predef$_mls_L0_2115_2180$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (msg$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.msg$0 = msg$0;
      this.tmp$1 = tmp$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 133) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 134) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 133) {
        this.tmp$1 = "Not implemented: " + this.msg$0;
        this.pc = 135;
        continue contLoop;
      } else if (this.pc === 135) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = globalThis.Error(this.tmp$1);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 134;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 134;
        continue contLoop;
      } else if (this.pc === 134) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        throw this.tmp$2;
      }
      break;
    }
  }
  toString() { return "Cont$func$notImplemented$Predef$_mls_L0_2115_2180$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$render$Predef$_mls_L0_1070_2080$$ = function Cont$func$render$Predef$_mls_L0_1070_2080$$(arg$0, ts$1, scrut$2, es$3, p$4, scrut$5, scrut$6, scrut$7, nme$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, tmp$27, tmp$28, tmp$29, tmp$30, tmp$31, tmp$32, tmp$33, tmp$34, tmp$35, tmp$36, tmp$37, tmp$38, tmp$39, tmp$40, tmp$41, tmp$42, tmp$43, curDepth$44, stackDelayRes$45, pc) {
  let tmp;
  tmp = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(pc);
  return tmp(arg$0, ts$1, scrut$2, es$3, p$4, scrut$5, scrut$6, scrut$7, nme$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, tmp$27, tmp$28, tmp$29, tmp$30, tmp$31, tmp$32, tmp$33, tmp$34, tmp$35, tmp$36, tmp$37, tmp$38, tmp$39, tmp$40, tmp$41, tmp$42, tmp$43, curDepth$44, stackDelayRes$45)
};
Cont$func$render$Predef$_mls_L0_1070_2080$$ctor = function Cont$func$render$Predef$_mls_L0_1070_2080$$ctor(arg$0, ts$1, scrut$2, es$3, p$4, scrut$5, scrut$6, scrut$7, nme$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, tmp$27, tmp$28, tmp$29, tmp$30, tmp$31, tmp$32, tmp$33, tmp$34, tmp$35, tmp$36, tmp$37, tmp$38, tmp$39, tmp$40, tmp$41, tmp$42, tmp$43, curDepth$44, stackDelayRes$45) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$render$Predef$_mls_L0_1070_2080$1.class(pc);
    return tmp(arg$0, ts$1, scrut$2, es$3, p$4, scrut$5, scrut$6, scrut$7, nme$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, tmp$27, tmp$28, tmp$29, tmp$30, tmp$31, tmp$32, tmp$33, tmp$34, tmp$35, tmp$36, tmp$37, tmp$38, tmp$39, tmp$40, tmp$41, tmp$42, tmp$43, curDepth$44, stackDelayRes$45)
  }
};
Cont$func$render$Predef$_mls_L0_1070_2080$1 = function Cont$func$render$Predef$_mls_L0_1070_2080$(pc1) {
  return (arg$01, ts$11, scrut$21, es$31, p$41, scrut$51, scrut$61, scrut$71, nme$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, tmp$171, tmp$181, tmp$191, tmp$201, tmp$211, tmp$221, tmp$231, tmp$241, tmp$251, tmp$261, tmp$271, tmp$281, tmp$291, tmp$301, tmp$311, tmp$321, tmp$331, tmp$341, tmp$351, tmp$361, tmp$371, tmp$381, tmp$391, tmp$401, tmp$411, tmp$421, tmp$431, curDepth$441, stackDelayRes$451) => {
    return new Cont$func$render$Predef$_mls_L0_1070_2080$.class(pc1)(arg$01, ts$11, scrut$21, es$31, p$41, scrut$51, scrut$61, scrut$71, nme$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, tmp$171, tmp$181, tmp$191, tmp$201, tmp$211, tmp$221, tmp$231, tmp$241, tmp$251, tmp$261, tmp$271, tmp$281, tmp$291, tmp$301, tmp$311, tmp$321, tmp$331, tmp$341, tmp$351, tmp$361, tmp$371, tmp$381, tmp$391, tmp$401, tmp$411, tmp$421, tmp$431, curDepth$441, stackDelayRes$451);
  }
};
Cont$func$render$Predef$_mls_L0_1070_2080$1.class = class Cont$func$render$Predef$_mls_L0_1070_2080$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (arg$0, ts$1, scrut$2, es$3, p$4, scrut$5, scrut$6, scrut$7, nme$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, tmp$27, tmp$28, tmp$29, tmp$30, tmp$31, tmp$32, tmp$33, tmp$34, tmp$35, tmp$36, tmp$37, tmp$38, tmp$39, tmp$40, tmp$41, tmp$42, tmp$43, curDepth$44, stackDelayRes$45) => {
      let tmp;
      tmp = super(null);
      this.arg$0 = arg$0;
      this.ts$1 = ts$1;
      this.scrut$2 = scrut$2;
      this.es$3 = es$3;
      this.p$4 = p$4;
      this.scrut$5 = scrut$5;
      this.scrut$6 = scrut$6;
      this.scrut$7 = scrut$7;
      this.nme$8 = nme$8;
      this.tmp$9 = tmp$9;
      this.tmp$10 = tmp$10;
      this.tmp$11 = tmp$11;
      this.tmp$12 = tmp$12;
      this.tmp$13 = tmp$13;
      this.tmp$14 = tmp$14;
      this.tmp$15 = tmp$15;
      this.tmp$16 = tmp$16;
      this.tmp$17 = tmp$17;
      this.tmp$18 = tmp$18;
      this.tmp$19 = tmp$19;
      this.tmp$20 = tmp$20;
      this.tmp$21 = tmp$21;
      this.tmp$22 = tmp$22;
      this.tmp$23 = tmp$23;
      this.tmp$24 = tmp$24;
      this.tmp$25 = tmp$25;
      this.tmp$26 = tmp$26;
      this.tmp$27 = tmp$27;
      this.tmp$28 = tmp$28;
      this.tmp$29 = tmp$29;
      this.tmp$30 = tmp$30;
      this.tmp$31 = tmp$31;
      this.tmp$32 = tmp$32;
      this.tmp$33 = tmp$33;
      this.tmp$34 = tmp$34;
      this.tmp$35 = tmp$35;
      this.tmp$36 = tmp$36;
      this.tmp$37 = tmp$37;
      this.tmp$38 = tmp$38;
      this.tmp$39 = tmp$39;
      this.tmp$40 = tmp$40;
      this.tmp$41 = tmp$41;
      this.tmp$42 = tmp$42;
      this.tmp$43 = tmp$43;
      this.curDepth$44 = curDepth$44;
      this.stackDelayRes$45 = stackDelayRes$45;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 53) {
      this.stackDelayRes$45 = value$;
    } else if (this.pc === 81) {
      this.tmp$35 = value$;
    } else if (this.pc === 82) {
      this.tmp$36 = value$;
    } else if (this.pc === 83) {
      this.tmp$37 = value$;
    } else if (this.pc === 89) {
      this.tmp$39 = value$;
    } else if (this.pc === 90) {
      this.tmp$40 = value$;
    } else if (this.pc === 91) {
      this.tmp$41 = value$;
    } else if (this.pc === 69) {
      this.p$4 = value$;
    } else if (this.pc === 70) {
      this.tmp$28 = value$;
    } else if (this.pc === 71) {
      this.tmp$29 = value$;
    } else if (this.pc === 72) {
      this.tmp$30 = value$;
    } else if (this.pc === 78) {
      this.tmp$32 = value$;
    } else if (this.pc === 79) {
      this.tmp$33 = value$;
    } else if (this.pc === 80) {
      this.tmp$34 = value$;
    } else if (this.pc === 64) {
      this.tmp$19 = value$;
    } else if (this.pc === 65) {
      this.tmp$20 = value$;
    } else if (this.pc === 66) {
      this.tmp$21 = value$;
    } else if (this.pc === 67) {
      this.tmp$22 = value$;
    } else if (this.pc === 68) {
      this.tmp$23 = value$;
    } else if (this.pc === 59) {
      this.tmp$14 = value$;
    } else if (this.pc === 60) {
      this.tmp$15 = value$;
    } else if (this.pc === 61) {
      this.tmp$16 = value$;
    } else if (this.pc === 62) {
      this.tmp$17 = value$;
    } else if (this.pc === 63) {
      this.tmp$18 = value$;
    } else if (this.pc === 54) {
      this.tmp$9 = value$;
    } else if (this.pc === 55) {
      this.tmp$10 = value$;
    } else if (this.pc === 56) {
      this.tmp$11 = value$;
    } else if (this.pc === 57) {
      this.tmp$12 = value$;
    } else if (this.pc === 58) {
      this.tmp$13 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 53) {
        if (this.arg$0 === undefined) {
          return "undefined"
        } else if (this.arg$0 === null) {
          return "null";
          this.pc = 92;
          continue contLoop;
        } else if (this.arg$0 instanceof globalThis.Array) {
          this.pc = 98;
          continue contLoop;
          this.pc = 92;
          continue contLoop;
          this.pc = 92;
          continue contLoop;
        } else {
          if (typeof this.arg$0 === 'string') {
            this.pc = 99;
            continue contLoop;
          } else if (this.arg$0 instanceof globalThis.Set) {
            this.pc = 105;
            continue contLoop;
            this.pc = 92;
            continue contLoop;
          } else if (this.arg$0 instanceof globalThis.Map) {
            this.pc = 111;
            continue contLoop;
            this.pc = 92;
            continue contLoop;
            this.pc = 92;
            continue contLoop;
          } else if (this.arg$0 instanceof globalThis.Function) {
            this.pc = 123;
            continue contLoop;
            this.pc = 92;
            continue contLoop;
            this.pc = 92;
            continue contLoop;
            this.pc = 92;
            continue contLoop;
          } else if (this.arg$0 instanceof globalThis.Object) {
            this.scrut$2 = this.arg$0.constructor.name;
            if (this.scrut$2 === "Object") {
              this.pc = 130;
              continue contLoop;
            } else {
              this.pc = 131;
              continue contLoop;
            }
            this.pc = 92;
            continue contLoop;
            this.pc = 92;
            continue contLoop;
            this.pc = 92;
            continue contLoop;
            this.pc = 92;
            continue contLoop;
            this.pc = 92;
            continue contLoop;
          } else {
            this.ts$1 = this.arg$0["toString"];
            if (this.ts$1 === undefined) {
              this.tmp$42 = typeof this.arg$0;
              this.tmp$43 = "[" + this.tmp$42;
              return this.tmp$43 + "]"
            } else {
              this.pc = 132;
              continue contLoop;
            }
            this.pc = 92;
            continue contLoop;
          }
          this.pc = 92;
          continue contLoop;
        }
        this.pc = 92;
        continue contLoop;
      } else if (this.pc === 92) {
        break contLoop;
      } else if (this.pc === 132) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.ts$1.call(this.arg$0))
      } else if (this.pc === 131) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return globalThis.String(this.arg$0)
      } else if (this.pc === 130) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$35 = runtime.safeCall(globalThis.Object.entries(this.arg$0));
        if (this.tmp$35 instanceof runtime.EffectSig.class) {
          this.pc = 81;
          this.tmp$35.contTrace.last.next = this;
          this.tmp$35.contTrace.last = this;
          return this.tmp$35
        }
        this.pc = 81;
        continue contLoop;
      } else if (this.pc === 81) {
        this.tmp$35 = runtime.resetDepth(this.tmp$35, this.curDepth$44);
        this.es$3 = this.tmp$35;
        this.pc = 129;
        continue contLoop;
      } else if (this.pc === 129) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$36 = Predef1.fold(lambda5);
        if (this.tmp$36 instanceof runtime.EffectSig.class) {
          this.pc = 82;
          this.tmp$36.contTrace.last.next = this;
          this.tmp$36.contTrace.last = this;
          return this.tmp$36
        }
        this.pc = 82;
        continue contLoop;
      } else if (this.pc === 82) {
        this.tmp$36 = runtime.resetDepth(this.tmp$36, this.curDepth$44);
        this.pc = 128;
        continue contLoop;
      } else if (this.pc === 124) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.tmp$36("{", ...this.tmp$41, "}"))
      } else if (this.pc === 128) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$37 = Predef1.interleave(", ");
        if (this.tmp$37 instanceof runtime.EffectSig.class) {
          this.pc = 83;
          this.tmp$37.contTrace.last.next = this;
          this.tmp$37.contTrace.last = this;
          return this.tmp$37
        }
        this.pc = 83;
        continue contLoop;
      } else if (this.pc === 83) {
        this.tmp$37 = runtime.resetDepth(this.tmp$37, this.curDepth$44);
        this.tmp$38 = lambda6;
        this.pc = 127;
        continue contLoop;
      } else if (this.pc === 125) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$41 = runtime.safeCall(this.tmp$37(...this.tmp$40));
        if (this.tmp$41 instanceof runtime.EffectSig.class) {
          this.pc = 91;
          this.tmp$41.contTrace.last.next = this;
          this.tmp$41.contTrace.last = this;
          return this.tmp$41
        }
        this.pc = 91;
        continue contLoop;
      } else if (this.pc === 127) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$39 = Predef1.map(this.tmp$38);
        if (this.tmp$39 instanceof runtime.EffectSig.class) {
          this.pc = 89;
          this.tmp$39.contTrace.last.next = this;
          this.tmp$39.contTrace.last = this;
          return this.tmp$39
        }
        this.pc = 89;
        continue contLoop;
      } else if (this.pc === 89) {
        this.tmp$39 = runtime.resetDepth(this.tmp$39, this.curDepth$44);
        this.pc = 126;
        continue contLoop;
      } else if (this.pc === 126) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$40 = runtime.safeCall(this.tmp$39(...this.es$3));
        if (this.tmp$40 instanceof runtime.EffectSig.class) {
          this.pc = 90;
          this.tmp$40.contTrace.last.next = this;
          this.tmp$40.contTrace.last = this;
          return this.tmp$40
        }
        this.pc = 90;
        continue contLoop;
      } else if (this.pc === 90) {
        this.tmp$40 = runtime.resetDepth(this.tmp$40, this.curDepth$44);
        this.pc = 125;
        continue contLoop;
      } else if (this.pc === 91) {
        this.tmp$41 = runtime.resetDepth(this.tmp$41, this.curDepth$44);
        this.pc = 124;
        continue contLoop;
      } else if (this.pc === 123) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.p$4 = globalThis.Object.getOwnPropertyDescriptor(this.arg$0, "prototype");
        if (this.p$4 instanceof runtime.EffectSig.class) {
          this.pc = 69;
          this.p$4.contTrace.last.next = this;
          this.p$4.contTrace.last = this;
          return this.p$4
        }
        this.pc = 69;
        continue contLoop;
      } else if (this.pc === 69) {
        this.p$4 = runtime.resetDepth(this.p$4, this.curDepth$44);
        if (this.p$4 instanceof globalThis.Object) {
          this.scrut$5 = this.p$4["writable"];
          if (this.scrut$5 === true) {
            this.tmp$24 = true;
            this.pc = 122;
            continue contLoop;
          } else {
            this.tmp$24 = false;
            this.pc = 122;
            continue contLoop;
          }
          this.pc = 122;
          continue contLoop;
        } else {
          this.tmp$24 = false;
          this.pc = 122;
          continue contLoop;
        }
        this.pc = 122;
        continue contLoop;
      } else if (this.pc === 122) {
        if (this.p$4 === undefined) {
          this.tmp$25 = true;
          this.pc = 121;
          continue contLoop;
        } else {
          this.tmp$25 = false;
          this.pc = 121;
          continue contLoop;
        }
        this.pc = 121;
        continue contLoop;
      } else if (this.pc === 121) {
        this.scrut$6 = this.tmp$24 || this.tmp$25;
        if (this.scrut$6 === true) {
          this.scrut$7 = this.arg$0.name;
          if (this.scrut$7 === "") {
            this.tmp$26 = "";
            this.pc = 112;
            continue contLoop;
          } else {
            this.nme$8 = this.scrut$7;
            this.tmp$26 = " " + this.nme$8;
            this.pc = 112;
            continue contLoop;
          }
          this.pc = 112;
          continue contLoop;
        } else {
          this.scrut$2 = this.arg$0.constructor.name;
          if (this.scrut$2 === "Object") {
            this.pc = 119;
            continue contLoop;
          } else {
            this.pc = 120;
            continue contLoop;
          }
          this.pc = 92;
          continue contLoop;
        }
        this.pc = 92;
        continue contLoop;
      } else if (this.pc === 120) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return globalThis.String(this.arg$0)
      } else if (this.pc === 119) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$28 = runtime.safeCall(globalThis.Object.entries(this.arg$0));
        if (this.tmp$28 instanceof runtime.EffectSig.class) {
          this.pc = 70;
          this.tmp$28.contTrace.last.next = this;
          this.tmp$28.contTrace.last = this;
          return this.tmp$28
        }
        this.pc = 70;
        continue contLoop;
      } else if (this.pc === 70) {
        this.tmp$28 = runtime.resetDepth(this.tmp$28, this.curDepth$44);
        this.es$3 = this.tmp$28;
        this.pc = 118;
        continue contLoop;
      } else if (this.pc === 118) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$29 = Predef1.fold(lambda3);
        if (this.tmp$29 instanceof runtime.EffectSig.class) {
          this.pc = 71;
          this.tmp$29.contTrace.last.next = this;
          this.tmp$29.contTrace.last = this;
          return this.tmp$29
        }
        this.pc = 71;
        continue contLoop;
      } else if (this.pc === 71) {
        this.tmp$29 = runtime.resetDepth(this.tmp$29, this.curDepth$44);
        this.pc = 117;
        continue contLoop;
      } else if (this.pc === 113) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.tmp$29("{", ...this.tmp$34, "}"))
      } else if (this.pc === 117) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$30 = Predef1.interleave(", ");
        if (this.tmp$30 instanceof runtime.EffectSig.class) {
          this.pc = 72;
          this.tmp$30.contTrace.last.next = this;
          this.tmp$30.contTrace.last = this;
          return this.tmp$30
        }
        this.pc = 72;
        continue contLoop;
      } else if (this.pc === 72) {
        this.tmp$30 = runtime.resetDepth(this.tmp$30, this.curDepth$44);
        this.tmp$31 = lambda4;
        this.pc = 116;
        continue contLoop;
      } else if (this.pc === 114) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$34 = runtime.safeCall(this.tmp$30(...this.tmp$33));
        if (this.tmp$34 instanceof runtime.EffectSig.class) {
          this.pc = 80;
          this.tmp$34.contTrace.last.next = this;
          this.tmp$34.contTrace.last = this;
          return this.tmp$34
        }
        this.pc = 80;
        continue contLoop;
      } else if (this.pc === 116) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$32 = Predef1.map(this.tmp$31);
        if (this.tmp$32 instanceof runtime.EffectSig.class) {
          this.pc = 78;
          this.tmp$32.contTrace.last.next = this;
          this.tmp$32.contTrace.last = this;
          return this.tmp$32
        }
        this.pc = 78;
        continue contLoop;
      } else if (this.pc === 78) {
        this.tmp$32 = runtime.resetDepth(this.tmp$32, this.curDepth$44);
        this.pc = 115;
        continue contLoop;
      } else if (this.pc === 115) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$33 = runtime.safeCall(this.tmp$32(...this.es$3));
        if (this.tmp$33 instanceof runtime.EffectSig.class) {
          this.pc = 79;
          this.tmp$33.contTrace.last.next = this;
          this.tmp$33.contTrace.last = this;
          return this.tmp$33
        }
        this.pc = 79;
        continue contLoop;
      } else if (this.pc === 79) {
        this.tmp$33 = runtime.resetDepth(this.tmp$33, this.curDepth$44);
        this.pc = 114;
        continue contLoop;
      } else if (this.pc === 80) {
        this.tmp$34 = runtime.resetDepth(this.tmp$34, this.curDepth$44);
        this.pc = 113;
        continue contLoop;
      } else if (this.pc === 112) {
        this.tmp$27 = "[function" + this.tmp$26;
        return this.tmp$27 + "]"
      } else if (this.pc === 111) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$19 = Predef1.fold(lambda2);
        if (this.tmp$19 instanceof runtime.EffectSig.class) {
          this.pc = 64;
          this.tmp$19.contTrace.last.next = this;
          this.tmp$19.contTrace.last = this;
          return this.tmp$19
        }
        this.pc = 64;
        continue contLoop;
      } else if (this.pc === 64) {
        this.tmp$19 = runtime.resetDepth(this.tmp$19, this.curDepth$44);
        this.pc = 110;
        continue contLoop;
      } else if (this.pc === 106) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.tmp$19("Map{", ...this.tmp$23, "}"))
      } else if (this.pc === 110) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$20 = Predef1.interleave(", ");
        if (this.tmp$20 instanceof runtime.EffectSig.class) {
          this.pc = 65;
          this.tmp$20.contTrace.last.next = this;
          this.tmp$20.contTrace.last = this;
          return this.tmp$20
        }
        this.pc = 65;
        continue contLoop;
      } else if (this.pc === 65) {
        this.tmp$20 = runtime.resetDepth(this.tmp$20, this.curDepth$44);
        this.pc = 109;
        continue contLoop;
      } else if (this.pc === 107) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$23 = runtime.safeCall(this.tmp$20(...this.tmp$22));
        if (this.tmp$23 instanceof runtime.EffectSig.class) {
          this.pc = 68;
          this.tmp$23.contTrace.last.next = this;
          this.tmp$23.contTrace.last = this;
          return this.tmp$23
        }
        this.pc = 68;
        continue contLoop;
      } else if (this.pc === 109) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$21 = Predef1.map(Predef1.render);
        if (this.tmp$21 instanceof runtime.EffectSig.class) {
          this.pc = 66;
          this.tmp$21.contTrace.last.next = this;
          this.tmp$21.contTrace.last = this;
          return this.tmp$21
        }
        this.pc = 66;
        continue contLoop;
      } else if (this.pc === 66) {
        this.tmp$21 = runtime.resetDepth(this.tmp$21, this.curDepth$44);
        this.pc = 108;
        continue contLoop;
      } else if (this.pc === 108) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$22 = runtime.safeCall(this.tmp$21(...this.arg$0));
        if (this.tmp$22 instanceof runtime.EffectSig.class) {
          this.pc = 67;
          this.tmp$22.contTrace.last.next = this;
          this.tmp$22.contTrace.last = this;
          return this.tmp$22
        }
        this.pc = 67;
        continue contLoop;
      } else if (this.pc === 67) {
        this.tmp$22 = runtime.resetDepth(this.tmp$22, this.curDepth$44);
        this.pc = 107;
        continue contLoop;
      } else if (this.pc === 68) {
        this.tmp$23 = runtime.resetDepth(this.tmp$23, this.curDepth$44);
        this.pc = 106;
        continue contLoop;
      } else if (this.pc === 105) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$14 = Predef1.fold(lambda1);
        if (this.tmp$14 instanceof runtime.EffectSig.class) {
          this.pc = 59;
          this.tmp$14.contTrace.last.next = this;
          this.tmp$14.contTrace.last = this;
          return this.tmp$14
        }
        this.pc = 59;
        continue contLoop;
      } else if (this.pc === 59) {
        this.tmp$14 = runtime.resetDepth(this.tmp$14, this.curDepth$44);
        this.pc = 104;
        continue contLoop;
      } else if (this.pc === 100) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.tmp$14("Set{", ...this.tmp$18, "}"))
      } else if (this.pc === 104) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$15 = Predef1.interleave(", ");
        if (this.tmp$15 instanceof runtime.EffectSig.class) {
          this.pc = 60;
          this.tmp$15.contTrace.last.next = this;
          this.tmp$15.contTrace.last = this;
          return this.tmp$15
        }
        this.pc = 60;
        continue contLoop;
      } else if (this.pc === 60) {
        this.tmp$15 = runtime.resetDepth(this.tmp$15, this.curDepth$44);
        this.pc = 103;
        continue contLoop;
      } else if (this.pc === 101) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$18 = runtime.safeCall(this.tmp$15(...this.tmp$17));
        if (this.tmp$18 instanceof runtime.EffectSig.class) {
          this.pc = 63;
          this.tmp$18.contTrace.last.next = this;
          this.tmp$18.contTrace.last = this;
          return this.tmp$18
        }
        this.pc = 63;
        continue contLoop;
      } else if (this.pc === 103) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$16 = Predef1.map(Predef1.render);
        if (this.tmp$16 instanceof runtime.EffectSig.class) {
          this.pc = 61;
          this.tmp$16.contTrace.last.next = this;
          this.tmp$16.contTrace.last = this;
          return this.tmp$16
        }
        this.pc = 61;
        continue contLoop;
      } else if (this.pc === 61) {
        this.tmp$16 = runtime.resetDepth(this.tmp$16, this.curDepth$44);
        this.pc = 102;
        continue contLoop;
      } else if (this.pc === 102) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$17 = runtime.safeCall(this.tmp$16(...this.arg$0));
        if (this.tmp$17 instanceof runtime.EffectSig.class) {
          this.pc = 62;
          this.tmp$17.contTrace.last.next = this;
          this.tmp$17.contTrace.last = this;
          return this.tmp$17
        }
        this.pc = 62;
        continue contLoop;
      } else if (this.pc === 62) {
        this.tmp$17 = runtime.resetDepth(this.tmp$17, this.curDepth$44);
        this.pc = 101;
        continue contLoop;
      } else if (this.pc === 63) {
        this.tmp$18 = runtime.resetDepth(this.tmp$18, this.curDepth$44);
        this.pc = 100;
        continue contLoop;
      } else if (this.pc === 99) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(globalThis.JSON.stringify(this.arg$0))
      } else if (this.pc === 98) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = Predef1.fold(lambda);
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 54;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 54;
        continue contLoop;
      } else if (this.pc === 54) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$44);
        this.pc = 97;
        continue contLoop;
      } else if (this.pc === 93) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.tmp$9("[", ...this.tmp$13, "]"))
      } else if (this.pc === 97) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$10 = Predef1.interleave(", ");
        if (this.tmp$10 instanceof runtime.EffectSig.class) {
          this.pc = 55;
          this.tmp$10.contTrace.last.next = this;
          this.tmp$10.contTrace.last = this;
          return this.tmp$10
        }
        this.pc = 55;
        continue contLoop;
      } else if (this.pc === 55) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$44);
        this.pc = 96;
        continue contLoop;
      } else if (this.pc === 94) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$13 = runtime.safeCall(this.tmp$10(...this.tmp$12));
        if (this.tmp$13 instanceof runtime.EffectSig.class) {
          this.pc = 58;
          this.tmp$13.contTrace.last.next = this;
          this.tmp$13.contTrace.last = this;
          return this.tmp$13
        }
        this.pc = 58;
        continue contLoop;
      } else if (this.pc === 96) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$11 = Predef1.map(Predef1.render);
        if (this.tmp$11 instanceof runtime.EffectSig.class) {
          this.pc = 56;
          this.tmp$11.contTrace.last.next = this;
          this.tmp$11.contTrace.last = this;
          return this.tmp$11
        }
        this.pc = 56;
        continue contLoop;
      } else if (this.pc === 56) {
        this.tmp$11 = runtime.resetDepth(this.tmp$11, this.curDepth$44);
        this.pc = 95;
        continue contLoop;
      } else if (this.pc === 95) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$12 = runtime.safeCall(this.tmp$11(...this.arg$0));
        if (this.tmp$12 instanceof runtime.EffectSig.class) {
          this.pc = 57;
          this.tmp$12.contTrace.last.next = this;
          this.tmp$12.contTrace.last = this;
          return this.tmp$12
        }
        this.pc = 57;
        continue contLoop;
      } else if (this.pc === 57) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$44);
        this.pc = 94;
        continue contLoop;
      } else if (this.pc === 58) {
        this.tmp$13 = runtime.resetDepth(this.tmp$13, this.curDepth$44);
        this.pc = 93;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$render$Predef$_mls_L0_1070_2080$(" + globalThis.Predef.render(this.pc) + ")"; }
};
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
Cont$func$lambda$$$1 = function Cont$func$lambda$$$(caseScrut$0, first1$1, first0$2, k$3, v$4, tmp$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$3.class(pc);
  return tmp(caseScrut$0, first1$1, first0$2, k$3, v$4, tmp$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9)
};
Cont$func$lambda$$$ctor1 = function Cont$func$lambda$$$ctor(caseScrut$0, first1$1, first0$2, k$3, v$4, tmp$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$3.class(pc);
    return tmp(caseScrut$0, first1$1, first0$2, k$3, v$4, tmp$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9)
  }
};
Cont$func$lambda$$3 = function Cont$func$lambda$$(pc1) {
  return (caseScrut$01, first1$11, first0$21, k$31, v$41, tmp$51, tmp$61, curDepth$71, tmp$81, stackDelayRes$91) => {
    return new Cont$func$lambda$$.class(pc1)(caseScrut$01, first1$11, first0$21, k$31, v$41, tmp$51, tmp$61, curDepth$71, tmp$81, stackDelayRes$91);
  }
};
Cont$func$lambda$$3.class = class Cont$func$lambda$$1 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (caseScrut$0, first1$1, first0$2, k$3, v$4, tmp$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9) => {
      let tmp;
      tmp = super(null);
      this.caseScrut$0 = caseScrut$0;
      this.first1$1 = first1$1;
      this.first0$2 = first0$2;
      this.k$3 = k$3;
      this.v$4 = v$4;
      this.tmp$5 = tmp$5;
      this.tmp$6 = tmp$6;
      this.curDepth$7 = curDepth$7;
      this.tmp$8 = tmp$8;
      this.stackDelayRes$9 = stackDelayRes$9;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 73) {
      this.stackDelayRes$9 = value$;
    } else if (this.pc === 75) {
      this.tmp$8 = value$;
    } else if (this.pc === 74) {
      this.tmp$6 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 73) {
        if (globalThis.Array.isArray(this.caseScrut$0) && this.caseScrut$0.length === 2) {
          this.first0$2 = this.caseScrut$0[0];
          this.first1$1 = this.caseScrut$0[1];
          this.k$3 = this.first0$2;
          this.v$4 = this.first1$1;
          this.tmp$5 = this.k$3 + ": ";
          this.pc = 77;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$8 = new globalThis.Error("match error");
          if (this.tmp$8 instanceof runtime.EffectSig.class) {
            this.pc = 75;
            this.tmp$8.contTrace.last.next = this;
            this.tmp$8.contTrace.last = this;
            return this.tmp$8
          }
          this.pc = 75;
          continue contLoop;
        }
        this.pc = 76;
        continue contLoop;
      } else if (this.pc === 76) {
        break contLoop;
      } else if (this.pc === 75) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$7);
        throw this.tmp$8;
      } else if (this.pc === 77) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = Predef1.render(this.v$4);
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 74;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 74;
        continue contLoop;
      } else if (this.pc === 74) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$7);
        return this.tmp$5 + this.tmp$6
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda4 = (undefined, function (caseScrut) {
  let first1, first0, k, v, tmp, tmp1, curDepth, tmp2, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$1(caseScrut, first1, first0, k, v, tmp, tmp1, curDepth, tmp2, stackDelayRes, 73);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    k = first0;
    v = first1;
    tmp = k + ": ";
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = Predef1.render(v);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$lambda$$$1(caseScrut, first1, first0, k, v, tmp, tmp1, curDepth, tmp2, stackDelayRes, 74);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    return tmp + tmp1
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = new globalThis.Error("match error");
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$lambda$$$1(caseScrut, first1, first0, k, v, tmp, tmp1, curDepth, tmp2, stackDelayRes, 75);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    throw tmp2;
  }
});
lambda5 = (undefined, function (arg1, arg2) {
  return arg1 + arg2
});
Cont$func$lambda$$$ = function Cont$func$lambda$$$(caseScrut$0, first1$1, first0$2, k$3, v$4, tmp$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$4.class(pc);
  return tmp(caseScrut$0, first1$1, first0$2, k$3, v$4, tmp$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9)
};
Cont$func$lambda$$$ctor = function Cont$func$lambda$$$ctor(caseScrut$0, first1$1, first0$2, k$3, v$4, tmp$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$4.class(pc);
    return tmp(caseScrut$0, first1$1, first0$2, k$3, v$4, tmp$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9)
  }
};
Cont$func$lambda$$4 = function Cont$func$lambda$$(pc1) {
  return (caseScrut$01, first1$11, first0$21, k$31, v$41, tmp$51, tmp$61, curDepth$71, tmp$81, stackDelayRes$91) => {
    return new Cont$func$lambda$$.class(pc1)(caseScrut$01, first1$11, first0$21, k$31, v$41, tmp$51, tmp$61, curDepth$71, tmp$81, stackDelayRes$91);
  }
};
Cont$func$lambda$$4.class = class Cont$func$lambda$$2 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (caseScrut$0, first1$1, first0$2, k$3, v$4, tmp$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9) => {
      let tmp;
      tmp = super(null);
      this.caseScrut$0 = caseScrut$0;
      this.first1$1 = first1$1;
      this.first0$2 = first0$2;
      this.k$3 = k$3;
      this.v$4 = v$4;
      this.tmp$5 = tmp$5;
      this.tmp$6 = tmp$6;
      this.curDepth$7 = curDepth$7;
      this.tmp$8 = tmp$8;
      this.stackDelayRes$9 = stackDelayRes$9;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 84) {
      this.stackDelayRes$9 = value$;
    } else if (this.pc === 86) {
      this.tmp$8 = value$;
    } else if (this.pc === 85) {
      this.tmp$6 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 84) {
        if (globalThis.Array.isArray(this.caseScrut$0) && this.caseScrut$0.length === 2) {
          this.first0$2 = this.caseScrut$0[0];
          this.first1$1 = this.caseScrut$0[1];
          this.k$3 = this.first0$2;
          this.v$4 = this.first1$1;
          this.tmp$5 = this.k$3 + ": ";
          this.pc = 88;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$8 = new globalThis.Error("match error");
          if (this.tmp$8 instanceof runtime.EffectSig.class) {
            this.pc = 86;
            this.tmp$8.contTrace.last.next = this;
            this.tmp$8.contTrace.last = this;
            return this.tmp$8
          }
          this.pc = 86;
          continue contLoop;
        }
        this.pc = 87;
        continue contLoop;
      } else if (this.pc === 87) {
        break contLoop;
      } else if (this.pc === 86) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$7);
        throw this.tmp$8;
      } else if (this.pc === 88) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = Predef1.render(this.v$4);
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 85;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 85;
        continue contLoop;
      } else if (this.pc === 85) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$7);
        return this.tmp$5 + this.tmp$6
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda6 = (undefined, function (caseScrut) {
  let first1, first0, k, v, tmp, tmp1, curDepth, tmp2, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$(caseScrut, first1, first0, k, v, tmp, tmp1, curDepth, tmp2, stackDelayRes, 84);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    k = first0;
    v = first1;
    tmp = k + ": ";
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = Predef1.render(v);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$lambda$$$(caseScrut, first1, first0, k, v, tmp, tmp1, curDepth, tmp2, stackDelayRes, 85);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    return tmp + tmp1
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = new globalThis.Error("match error");
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$lambda$$$(caseScrut, first1, first0, k, v, tmp, tmp1, curDepth, tmp2, stackDelayRes, 86);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    throw tmp2;
  }
});
Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$$ = function Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$$(arg$0, stackDelayRes$1, pc) {
  let tmp;
  tmp = new Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$1.class(pc);
  return tmp(arg$0, stackDelayRes$1)
};
Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$$ctor = function Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$$ctor(arg$0, stackDelayRes$1) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$1.class(pc);
    return tmp(arg$0, stackDelayRes$1)
  }
};
Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$1 = function Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$(pc1) {
  return (arg$01, stackDelayRes$11) => {
    return new Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$.class(pc1)(arg$01, stackDelayRes$11);
  }
};
Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$1.class = class Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (arg$0, stackDelayRes$1) => {
      let tmp;
      tmp = super(null);
      this.arg$0 = arg$0;
      this.stackDelayRes$1 = stackDelayRes$1;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 50) {
      this.stackDelayRes$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 50) {
        if (typeof this.arg$0 === 'string') {
          return this.arg$0
        } else {
          this.pc = 52;
          continue contLoop;
        }
        this.pc = 51;
        continue contLoop;
      } else if (this.pc === 51) {
        break contLoop;
      } else if (this.pc === 52) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Predef1.render(this.arg$0)
      }
      break;
    }
  }
  toString() { return "Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$interleave$Predef$_mls_L0_721_998$$ = function Cont$func$interleave$Predef$_mls_L0_721_998$$(sep$0, args$1, res$2, len$3, i$4, scrut$5, idx$6, scrut$7, scrut$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, stackDelayRes$18, pc) {
  let tmp;
  tmp = new Cont$func$interleave$Predef$_mls_L0_721_998$1.class(pc);
  return tmp(sep$0, args$1, res$2, len$3, i$4, scrut$5, idx$6, scrut$7, scrut$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, stackDelayRes$18)
};
Cont$func$interleave$Predef$_mls_L0_721_998$$ctor = function Cont$func$interleave$Predef$_mls_L0_721_998$$ctor(sep$0, args$1, res$2, len$3, i$4, scrut$5, idx$6, scrut$7, scrut$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, stackDelayRes$18) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$interleave$Predef$_mls_L0_721_998$1.class(pc);
    return tmp(sep$0, args$1, res$2, len$3, i$4, scrut$5, idx$6, scrut$7, scrut$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, stackDelayRes$18)
  }
};
Cont$func$interleave$Predef$_mls_L0_721_998$1 = function Cont$func$interleave$Predef$_mls_L0_721_998$(pc1) {
  return (sep$01, args$11, res$21, len$31, i$41, scrut$51, idx$61, scrut$71, scrut$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, curDepth$171, stackDelayRes$181) => {
    return new Cont$func$interleave$Predef$_mls_L0_721_998$.class(pc1)(sep$01, args$11, res$21, len$31, i$41, scrut$51, idx$61, scrut$71, scrut$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, curDepth$171, stackDelayRes$181);
  }
};
Cont$func$interleave$Predef$_mls_L0_721_998$1.class = class Cont$func$interleave$Predef$_mls_L0_721_998$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (sep$0, args$1, res$2, len$3, i$4, scrut$5, idx$6, scrut$7, scrut$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, stackDelayRes$18) => {
      let tmp;
      tmp = super(null);
      this.sep$0 = sep$0;
      this.args$1 = args$1;
      this.res$2 = res$2;
      this.len$3 = len$3;
      this.i$4 = i$4;
      this.scrut$5 = scrut$5;
      this.idx$6 = idx$6;
      this.scrut$7 = scrut$7;
      this.scrut$8 = scrut$8;
      this.tmp$9 = tmp$9;
      this.tmp$10 = tmp$10;
      this.tmp$11 = tmp$11;
      this.tmp$12 = tmp$12;
      this.tmp$13 = tmp$13;
      this.tmp$14 = tmp$14;
      this.tmp$15 = tmp$15;
      this.tmp$16 = tmp$16;
      this.curDepth$17 = curDepth$17;
      this.stackDelayRes$18 = stackDelayRes$18;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 42) {
      this.stackDelayRes$18 = value$;
    } else if (this.pc === 43) {
      this.tmp$11 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 42) {
        this.scrut$8 = this.args$1.length === 0;
        if (this.scrut$8 === true) {
          this.pc = 45;
          continue contLoop;
        } else {
          this.tmp$9 = this.args$1.length * 2;
          this.tmp$10 = this.tmp$9 - 1;
          this.pc = 49;
          continue contLoop;
        }
        this.pc = 44;
        continue contLoop;
      } else if (this.pc === 44) {
        break contLoop;
      } else if (this.pc === 49) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$11 = globalThis.Array(this.tmp$10);
        if (this.tmp$11 instanceof runtime.EffectSig.class) {
          this.pc = 43;
          this.tmp$11.contTrace.last.next = this;
          this.tmp$11.contTrace.last = this;
          return this.tmp$11
        }
        this.pc = 43;
        continue contLoop;
      } else if (this.pc === 43) {
        this.tmp$11 = runtime.resetDepth(this.tmp$11, this.curDepth$17);
        this.res$2 = this.tmp$11;
        this.len$3 = this.args$1.length;
        this.i$4 = 0;
        this.pc = 47;
        continue contLoop;
      } else if (this.pc === 46) {
        return this.res$2
      } else if (this.pc === 47) {
        this.scrut$5 = this.i$4 < this.len$3;
        if (this.scrut$5 === true) {
          this.tmp$12 = this.i$4 * 2;
          this.idx$6 = this.tmp$12;
          this.res$2[this.idx$6] = this.args$1[this.i$4];
          this.tmp$13 = this.i$4 + 1;
          this.i$4 = this.tmp$13;
          this.scrut$7 = this.i$4 < this.len$3;
          if (this.scrut$7 === true) {
            this.tmp$14 = this.idx$6 + 1;
            this.res$2[this.tmp$14] = this.sep$0;
            this.tmp$15 = runtime.Unit;
            this.pc = 48;
            continue contLoop;
          } else {
            this.tmp$15 = runtime.Unit;
            this.pc = 48;
            continue contLoop;
          }
          this.pc = 48;
          continue contLoop;
        } else {
          this.tmp$16 = runtime.Unit;
          this.pc = 46;
          continue contLoop;
        }
        this.pc = 46;
        continue contLoop;
      } else if (this.pc === 48) {
        this.tmp$16 = this.tmp$15;
        this.pc = 47;
        continue contLoop;
      } else if (this.pc === 45) {
        return []
      }
      break;
    }
  }
  toString() { return "Cont$func$interleave$Predef$_mls_L0_721_998$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$printRaw$Predef$_mls_L0_677_715$$ = function Cont$func$printRaw$Predef$_mls_L0_677_715$$(x$0, tmp$1, curDepth$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$printRaw$Predef$_mls_L0_677_715$1.class(pc);
  return tmp(x$0, tmp$1, curDepth$2, stackDelayRes$3)
};
Cont$func$printRaw$Predef$_mls_L0_677_715$$ctor = function Cont$func$printRaw$Predef$_mls_L0_677_715$$ctor(x$0, tmp$1, curDepth$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$printRaw$Predef$_mls_L0_677_715$1.class(pc);
    return tmp(x$0, tmp$1, curDepth$2, stackDelayRes$3)
  }
};
Cont$func$printRaw$Predef$_mls_L0_677_715$1 = function Cont$func$printRaw$Predef$_mls_L0_677_715$(pc1) {
  return (x$01, tmp$11, curDepth$21, stackDelayRes$31) => {
    return new Cont$func$printRaw$Predef$_mls_L0_677_715$.class(pc1)(x$01, tmp$11, curDepth$21, stackDelayRes$31);
  }
};
Cont$func$printRaw$Predef$_mls_L0_677_715$1.class = class Cont$func$printRaw$Predef$_mls_L0_677_715$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, tmp$1, curDepth$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.x$0 = x$0;
      this.tmp$1 = tmp$1;
      this.curDepth$2 = curDepth$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 38) {
      this.stackDelayRes$3 = value$;
    } else if (this.pc === 39) {
      this.tmp$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 38) {
        this.pc = 41;
        continue contLoop;
      } else if (this.pc === 40) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(globalThis.console.log(this.tmp$1))
      } else if (this.pc === 41) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = Predef1.render(this.x$0);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 39;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 39;
        continue contLoop;
      } else if (this.pc === 39) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$2);
        this.pc = 40;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$printRaw$Predef$_mls_L0_677_715$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$print$Predef$_mls_L0_615_671$$ = function Cont$func$print$Predef$_mls_L0_615_671$$(xs$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$print$Predef$_mls_L0_615_671$1.class(pc);
  return tmp(xs$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$print$Predef$_mls_L0_615_671$$ctor = function Cont$func$print$Predef$_mls_L0_615_671$$ctor(xs$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$print$Predef$_mls_L0_615_671$1.class(pc);
    return tmp(xs$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$print$Predef$_mls_L0_615_671$1 = function Cont$func$print$Predef$_mls_L0_615_671$(pc1) {
  return (xs$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$print$Predef$_mls_L0_615_671$.class(pc1)(xs$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$print$Predef$_mls_L0_615_671$1.class = class Cont$func$print$Predef$_mls_L0_615_671$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (xs$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.xs$0 = xs$0;
      this.tmp$1 = tmp$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 32) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 33) {
      this.tmp$1 = value$;
    } else if (this.pc === 34) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 32) {
        this.pc = 37;
        continue contLoop;
      } else if (this.pc === 35) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(globalThis.console.log(...this.tmp$2))
      } else if (this.pc === 37) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = Predef1.map(Predef1.renderAsStr);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 33;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 33;
        continue contLoop;
      } else if (this.pc === 33) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$3);
        this.pc = 36;
        continue contLoop;
      } else if (this.pc === 36) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = runtime.safeCall(this.tmp$1(...this.xs$0));
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 34;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 34;
        continue contLoop;
      } else if (this.pc === 34) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        this.pc = 35;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$print$Predef$_mls_L0_615_671$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$passing$Predef$_mls_L0_565_608$$ = function Cont$func$passing$Predef$_mls_L0_565_608$$(f$0, args$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$passing$Predef$_mls_L0_565_608$1.class(pc);
  return tmp(f$0, args$1, stackDelayRes$2)
};
Cont$func$passing$Predef$_mls_L0_565_608$$ctor = function Cont$func$passing$Predef$_mls_L0_565_608$$ctor(f$0, args$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$passing$Predef$_mls_L0_565_608$1.class(pc);
    return tmp(f$0, args$1, stackDelayRes$2)
  }
};
Cont$func$passing$Predef$_mls_L0_565_608$1 = function Cont$func$passing$Predef$_mls_L0_565_608$(pc1) {
  return (f$01, args$11, stackDelayRes$21) => {
    return new Cont$func$passing$Predef$_mls_L0_565_608$.class(pc1)(f$01, args$11, stackDelayRes$21);
  }
};
Cont$func$passing$Predef$_mls_L0_565_608$1.class = class Cont$func$passing$Predef$_mls_L0_565_608$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, args$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.f$0 = f$0;
      this.args$1 = args$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 30) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 30) {
        this.pc = 31;
        continue contLoop;
      } else if (this.pc === 31) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return this.f$0.bind(null, ...this.args$1)
      }
      break;
    }
  }
  toString() { return "Cont$func$passing$Predef$_mls_L0_565_608$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$pass3$Predef$_mls_L0_522_559$$ = function Cont$func$pass3$Predef$_mls_L0_522_559$$(f$0, xs$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$pass3$Predef$_mls_L0_522_559$1.class(pc);
  return tmp(f$0, xs$1, stackDelayRes$2)
};
Cont$func$pass3$Predef$_mls_L0_522_559$$ctor = function Cont$func$pass3$Predef$_mls_L0_522_559$$ctor(f$0, xs$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$pass3$Predef$_mls_L0_522_559$1.class(pc);
    return tmp(f$0, xs$1, stackDelayRes$2)
  }
};
Cont$func$pass3$Predef$_mls_L0_522_559$1 = function Cont$func$pass3$Predef$_mls_L0_522_559$(pc1) {
  return (f$01, xs$11, stackDelayRes$21) => {
    return new Cont$func$pass3$Predef$_mls_L0_522_559$.class(pc1)(f$01, xs$11, stackDelayRes$21);
  }
};
Cont$func$pass3$Predef$_mls_L0_522_559$1.class = class Cont$func$pass3$Predef$_mls_L0_522_559$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, xs$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.f$0 = f$0;
      this.xs$1 = xs$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 28) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 28) {
        this.pc = 29;
        continue contLoop;
      } else if (this.pc === 29) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.f$0(this.xs$1[0], this.xs$1[1], this.xs$1[2]))
      }
      break;
    }
  }
  toString() { return "Cont$func$pass3$Predef$_mls_L0_522_559$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$pass2$Predef$_mls_L0_486_517$$ = function Cont$func$pass2$Predef$_mls_L0_486_517$$(f$0, xs$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$pass2$Predef$_mls_L0_486_517$1.class(pc);
  return tmp(f$0, xs$1, stackDelayRes$2)
};
Cont$func$pass2$Predef$_mls_L0_486_517$$ctor = function Cont$func$pass2$Predef$_mls_L0_486_517$$ctor(f$0, xs$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$pass2$Predef$_mls_L0_486_517$1.class(pc);
    return tmp(f$0, xs$1, stackDelayRes$2)
  }
};
Cont$func$pass2$Predef$_mls_L0_486_517$1 = function Cont$func$pass2$Predef$_mls_L0_486_517$(pc1) {
  return (f$01, xs$11, stackDelayRes$21) => {
    return new Cont$func$pass2$Predef$_mls_L0_486_517$.class(pc1)(f$01, xs$11, stackDelayRes$21);
  }
};
Cont$func$pass2$Predef$_mls_L0_486_517$1.class = class Cont$func$pass2$Predef$_mls_L0_486_517$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, xs$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.f$0 = f$0;
      this.xs$1 = xs$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 26) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 26) {
        this.pc = 27;
        continue contLoop;
      } else if (this.pc === 27) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.f$0(this.xs$1[0], this.xs$1[1]))
      }
      break;
    }
  }
  toString() { return "Cont$func$pass2$Predef$_mls_L0_486_517$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$pass1$Predef$_mls_L0_456_481$$ = function Cont$func$pass1$Predef$_mls_L0_456_481$$(f$0, xs$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$pass1$Predef$_mls_L0_456_481$1.class(pc);
  return tmp(f$0, xs$1, stackDelayRes$2)
};
Cont$func$pass1$Predef$_mls_L0_456_481$$ctor = function Cont$func$pass1$Predef$_mls_L0_456_481$$ctor(f$0, xs$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$pass1$Predef$_mls_L0_456_481$1.class(pc);
    return tmp(f$0, xs$1, stackDelayRes$2)
  }
};
Cont$func$pass1$Predef$_mls_L0_456_481$1 = function Cont$func$pass1$Predef$_mls_L0_456_481$(pc1) {
  return (f$01, xs$11, stackDelayRes$21) => {
    return new Cont$func$pass1$Predef$_mls_L0_456_481$.class(pc1)(f$01, xs$11, stackDelayRes$21);
  }
};
Cont$func$pass1$Predef$_mls_L0_456_481$1.class = class Cont$func$pass1$Predef$_mls_L0_456_481$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, xs$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.f$0 = f$0;
      this.xs$1 = xs$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 24) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 24) {
        this.pc = 25;
        continue contLoop;
      } else if (this.pc === 25) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.f$0(this.xs$1[0]))
      }
      break;
    }
  }
  toString() { return "Cont$func$pass1$Predef$_mls_L0_456_481$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$call$Predef$_mls_L0_390_450$$ = function Cont$func$call$Predef$_mls_L0_390_450$$(receiver$0, f$1, args$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$call$Predef$_mls_L0_390_450$1.class(pc);
  return tmp(receiver$0, f$1, args$2, stackDelayRes$3)
};
Cont$func$call$Predef$_mls_L0_390_450$$ctor = function Cont$func$call$Predef$_mls_L0_390_450$$ctor(receiver$0, f$1, args$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$call$Predef$_mls_L0_390_450$1.class(pc);
    return tmp(receiver$0, f$1, args$2, stackDelayRes$3)
  }
};
Cont$func$call$Predef$_mls_L0_390_450$1 = function Cont$func$call$Predef$_mls_L0_390_450$(pc1) {
  return (receiver$01, f$11, args$21, stackDelayRes$31) => {
    return new Cont$func$call$Predef$_mls_L0_390_450$.class(pc1)(receiver$01, f$11, args$21, stackDelayRes$31);
  }
};
Cont$func$call$Predef$_mls_L0_390_450$1.class = class Cont$func$call$Predef$_mls_L0_390_450$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (receiver$0, f$1, args$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.receiver$0 = receiver$0;
      this.f$1 = f$1;
      this.args$2 = args$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 22) {
      this.stackDelayRes$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 22) {
        this.pc = 23;
        continue contLoop;
      } else if (this.pc === 23) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return this.f$1.call(this.receiver$0, ...this.args$2)
      }
      break;
    }
  }
  toString() { return "Cont$func$call$Predef$_mls_L0_390_450$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$passTo$Predef$_mls_L0_329_384$$ = function Cont$func$passTo$Predef$_mls_L0_329_384$$(receiver$0, f$1, args$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$passTo$Predef$_mls_L0_329_384$1.class(pc);
  return tmp(receiver$0, f$1, args$2, stackDelayRes$3)
};
Cont$func$passTo$Predef$_mls_L0_329_384$$ctor = function Cont$func$passTo$Predef$_mls_L0_329_384$$ctor(receiver$0, f$1, args$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$passTo$Predef$_mls_L0_329_384$1.class(pc);
    return tmp(receiver$0, f$1, args$2, stackDelayRes$3)
  }
};
Cont$func$passTo$Predef$_mls_L0_329_384$1 = function Cont$func$passTo$Predef$_mls_L0_329_384$(pc1) {
  return (receiver$01, f$11, args$21, stackDelayRes$31) => {
    return new Cont$func$passTo$Predef$_mls_L0_329_384$.class(pc1)(receiver$01, f$11, args$21, stackDelayRes$31);
  }
};
Cont$func$passTo$Predef$_mls_L0_329_384$1.class = class Cont$func$passTo$Predef$_mls_L0_329_384$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (receiver$0, f$1, args$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.receiver$0 = receiver$0;
      this.f$1 = f$1;
      this.args$2 = args$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 20) {
      this.stackDelayRes$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 20) {
        this.pc = 21;
        continue contLoop;
      } else if (this.pc === 21) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.f$1(this.receiver$0, ...this.args$2))
      }
      break;
    }
  }
  toString() { return "Cont$func$passTo$Predef$_mls_L0_329_384$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$compose$Predef$_mls_L0_292_323$$ = function Cont$func$compose$Predef$_mls_L0_292_323$$(f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5, pc) {
  let tmp;
  tmp = new Cont$func$compose$Predef$_mls_L0_292_323$1.class(pc);
  return tmp(f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5)
};
Cont$func$compose$Predef$_mls_L0_292_323$$ctor = function Cont$func$compose$Predef$_mls_L0_292_323$$ctor(f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$compose$Predef$_mls_L0_292_323$1.class(pc);
    return tmp(f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5)
  }
};
Cont$func$compose$Predef$_mls_L0_292_323$1 = function Cont$func$compose$Predef$_mls_L0_292_323$(pc1) {
  return (f$01, g$11, x$21, tmp$31, curDepth$41, stackDelayRes$51) => {
    return new Cont$func$compose$Predef$_mls_L0_292_323$.class(pc1)(f$01, g$11, x$21, tmp$31, curDepth$41, stackDelayRes$51);
  }
};
Cont$func$compose$Predef$_mls_L0_292_323$1.class = class Cont$func$compose$Predef$_mls_L0_292_323$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5) => {
      let tmp;
      tmp = super(null);
      this.f$0 = f$0;
      this.g$1 = g$1;
      this.x$2 = x$2;
      this.tmp$3 = tmp$3;
      this.curDepth$4 = curDepth$4;
      this.stackDelayRes$5 = stackDelayRes$5;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 16) {
      this.stackDelayRes$5 = value$;
    } else if (this.pc === 17) {
      this.tmp$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 16) {
        this.pc = 19;
        continue contLoop;
      } else if (this.pc === 18) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.f$0(this.tmp$3))
      } else if (this.pc === 19) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = runtime.safeCall(this.g$1(this.x$2));
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 17;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 17;
        continue contLoop;
      } else if (this.pc === 17) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$4);
        this.pc = 18;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$compose$Predef$_mls_L0_292_323$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$andThen$Predef$_mls_L0_256_287$$ = function Cont$func$andThen$Predef$_mls_L0_256_287$$(f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5, pc) {
  let tmp;
  tmp = new Cont$func$andThen$Predef$_mls_L0_256_287$1.class(pc);
  return tmp(f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5)
};
Cont$func$andThen$Predef$_mls_L0_256_287$$ctor = function Cont$func$andThen$Predef$_mls_L0_256_287$$ctor(f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$andThen$Predef$_mls_L0_256_287$1.class(pc);
    return tmp(f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5)
  }
};
Cont$func$andThen$Predef$_mls_L0_256_287$1 = function Cont$func$andThen$Predef$_mls_L0_256_287$(pc1) {
  return (f$01, g$11, x$21, tmp$31, curDepth$41, stackDelayRes$51) => {
    return new Cont$func$andThen$Predef$_mls_L0_256_287$.class(pc1)(f$01, g$11, x$21, tmp$31, curDepth$41, stackDelayRes$51);
  }
};
Cont$func$andThen$Predef$_mls_L0_256_287$1.class = class Cont$func$andThen$Predef$_mls_L0_256_287$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5) => {
      let tmp;
      tmp = super(null);
      this.f$0 = f$0;
      this.g$1 = g$1;
      this.x$2 = x$2;
      this.tmp$3 = tmp$3;
      this.curDepth$4 = curDepth$4;
      this.stackDelayRes$5 = stackDelayRes$5;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 12) {
      this.stackDelayRes$5 = value$;
    } else if (this.pc === 13) {
      this.tmp$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 12) {
        this.pc = 15;
        continue contLoop;
      } else if (this.pc === 14) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.g$1(this.tmp$3))
      } else if (this.pc === 15) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = runtime.safeCall(this.f$0(this.x$2));
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 13;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 13;
        continue contLoop;
      } else if (this.pc === 13) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$4);
        this.pc = 14;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$andThen$Predef$_mls_L0_256_287$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$pat$Predef$_mls_L0_226_250$$ = function Cont$func$pat$Predef$_mls_L0_226_250$$(f$0, x$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$pat$Predef$_mls_L0_226_250$1.class(pc);
  return tmp(f$0, x$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$pat$Predef$_mls_L0_226_250$$ctor = function Cont$func$pat$Predef$_mls_L0_226_250$$ctor(f$0, x$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$pat$Predef$_mls_L0_226_250$1.class(pc);
    return tmp(f$0, x$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$pat$Predef$_mls_L0_226_250$1 = function Cont$func$pat$Predef$_mls_L0_226_250$(pc1) {
  return (f$01, x$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$pat$Predef$_mls_L0_226_250$.class(pc1)(f$01, x$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$pat$Predef$_mls_L0_226_250$1.class = class Cont$func$pat$Predef$_mls_L0_226_250$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, x$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.f$0 = f$0;
      this.x$1 = x$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 9) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 10) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 9) {
        this.pc = 11;
        continue contLoop;
      } else if (this.pc === 11) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = runtime.safeCall(this.f$0(this.x$1));
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 10;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 10;
        continue contLoop;
      } else if (this.pc === 10) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        return (this.tmp$2 , this.x$1)
      }
      break;
    }
  }
  toString() { return "Cont$func$pat$Predef$_mls_L0_226_250$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$tap$Predef$_mls_L0_197_221$$ = function Cont$func$tap$Predef$_mls_L0_197_221$$(x$0, f$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$tap$Predef$_mls_L0_197_221$1.class(pc);
  return tmp(x$0, f$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$tap$Predef$_mls_L0_197_221$$ctor = function Cont$func$tap$Predef$_mls_L0_197_221$$ctor(x$0, f$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$tap$Predef$_mls_L0_197_221$1.class(pc);
    return tmp(x$0, f$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$tap$Predef$_mls_L0_197_221$1 = function Cont$func$tap$Predef$_mls_L0_197_221$(pc1) {
  return (x$01, f$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$tap$Predef$_mls_L0_197_221$.class(pc1)(x$01, f$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$tap$Predef$_mls_L0_197_221$1.class = class Cont$func$tap$Predef$_mls_L0_197_221$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, f$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.x$0 = x$0;
      this.f$1 = f$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 6) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 7) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 6) {
        this.pc = 8;
        continue contLoop;
      } else if (this.pc === 8) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = runtime.safeCall(this.f$1(this.x$0));
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 7;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 7;
        continue contLoop;
      } else if (this.pc === 7) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        return (this.tmp$2 , this.x$0)
      }
      break;
    }
  }
  toString() { return "Cont$func$tap$Predef$_mls_L0_197_221$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$pipeFrom$Predef$_mls_L0_165_191$$ = function Cont$func$pipeFrom$Predef$_mls_L0_165_191$$(f$0, x$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$pipeFrom$Predef$_mls_L0_165_191$1.class(pc);
  return tmp(f$0, x$1, stackDelayRes$2)
};
Cont$func$pipeFrom$Predef$_mls_L0_165_191$$ctor = function Cont$func$pipeFrom$Predef$_mls_L0_165_191$$ctor(f$0, x$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$pipeFrom$Predef$_mls_L0_165_191$1.class(pc);
    return tmp(f$0, x$1, stackDelayRes$2)
  }
};
Cont$func$pipeFrom$Predef$_mls_L0_165_191$1 = function Cont$func$pipeFrom$Predef$_mls_L0_165_191$(pc1) {
  return (f$01, x$11, stackDelayRes$21) => {
    return new Cont$func$pipeFrom$Predef$_mls_L0_165_191$.class(pc1)(f$01, x$11, stackDelayRes$21);
  }
};
Cont$func$pipeFrom$Predef$_mls_L0_165_191$1.class = class Cont$func$pipeFrom$Predef$_mls_L0_165_191$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, x$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.f$0 = f$0;
      this.x$1 = x$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 4) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 4) {
        this.pc = 5;
        continue contLoop;
      } else if (this.pc === 5) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.f$0(this.x$1))
      }
      break;
    }
  }
  toString() { return "Cont$func$pipeFrom$Predef$_mls_L0_165_191$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$pipeInto$Predef$_mls_L0_134_160$$ = function Cont$func$pipeInto$Predef$_mls_L0_134_160$$(x$0, f$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$pipeInto$Predef$_mls_L0_134_160$1.class(pc);
  return tmp(x$0, f$1, stackDelayRes$2)
};
Cont$func$pipeInto$Predef$_mls_L0_134_160$$ctor = function Cont$func$pipeInto$Predef$_mls_L0_134_160$$ctor(x$0, f$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$pipeInto$Predef$_mls_L0_134_160$1.class(pc);
    return tmp(x$0, f$1, stackDelayRes$2)
  }
};
Cont$func$pipeInto$Predef$_mls_L0_134_160$1 = function Cont$func$pipeInto$Predef$_mls_L0_134_160$(pc1) {
  return (x$01, f$11, stackDelayRes$21) => {
    return new Cont$func$pipeInto$Predef$_mls_L0_134_160$.class(pc1)(x$01, f$11, stackDelayRes$21);
  }
};
Cont$func$pipeInto$Predef$_mls_L0_134_160$1.class = class Cont$func$pipeInto$Predef$_mls_L0_134_160$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, f$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.x$0 = x$0;
      this.f$1 = f$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 2) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 2) {
        this.pc = 3;
        continue contLoop;
      } else if (this.pc === 3) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.f$1(this.x$0))
      }
      break;
    }
  }
  toString() { return "Cont$func$pipeInto$Predef$_mls_L0_134_160$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$apply$Predef$_mls_L0_94_128$$ = function Cont$func$apply$Predef$_mls_L0_94_128$$(f$0, args$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$apply$Predef$_mls_L0_94_128$1.class(pc);
  return tmp(f$0, args$1, stackDelayRes$2)
};
Cont$func$apply$Predef$_mls_L0_94_128$$ctor = function Cont$func$apply$Predef$_mls_L0_94_128$$ctor(f$0, args$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$apply$Predef$_mls_L0_94_128$1.class(pc);
    return tmp(f$0, args$1, stackDelayRes$2)
  }
};
Cont$func$apply$Predef$_mls_L0_94_128$1 = function Cont$func$apply$Predef$_mls_L0_94_128$(pc1) {
  return (f$01, args$11, stackDelayRes$21) => {
    return new Cont$func$apply$Predef$_mls_L0_94_128$.class(pc1)(f$01, args$11, stackDelayRes$21);
  }
};
Cont$func$apply$Predef$_mls_L0_94_128$1.class = class Cont$func$apply$Predef$_mls_L0_94_128$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, args$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.f$0 = f$0;
      this.args$1 = args$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 0) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 0) {
        this.pc = 1;
        continue contLoop;
      } else if (this.pc === 1) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.f$0(...this.args$1))
      }
      break;
    }
  }
  toString() { return "Cont$func$apply$Predef$_mls_L0_94_128$(" + globalThis.Predef.render(this.pc) + ")"; }
};
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
        let scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, stackDelayRes;
        curDepth = runtime.stackDepth;
        stackDelayRes = runtime.checkDepth();
        if (stackDelayRes instanceof runtime.EffectSig.class) {
          stackDelayRes.contTrace.last.next = Cont$func$log$Predef$_mls_L0_4207_4345$$(TraceLogger, msg, scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, stackDelayRes, 192);
          stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
          return stackDelayRes
        }
        scrut = TraceLogger.enabled;
        if (scrut === true) {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp = runtime.safeCall("| ".repeat(TraceLogger.indentLvl));
          if (tmp instanceof runtime.EffectSig.class) {
            tmp.contTrace.last.next = Cont$func$log$Predef$_mls_L0_4207_4345$$(TraceLogger, msg, scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, stackDelayRes, 193);
            tmp.contTrace.last = tmp.contTrace.last.next;
            return tmp
          }
          tmp = runtime.resetDepth(tmp, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp1 = runtime.safeCall("  ".repeat(TraceLogger.indentLvl));
          if (tmp1 instanceof runtime.EffectSig.class) {
            tmp1.contTrace.last.next = Cont$func$log$Predef$_mls_L0_4207_4345$$(TraceLogger, msg, scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, stackDelayRes, 194);
            tmp1.contTrace.last = tmp1.contTrace.last.next;
            return tmp1
          }
          tmp1 = runtime.resetDepth(tmp1, curDepth);
          tmp2 = "\n" + tmp1;
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp3 = msg.replaceAll("\n", tmp2);
          if (tmp3 instanceof runtime.EffectSig.class) {
            tmp3.contTrace.last.next = Cont$func$log$Predef$_mls_L0_4207_4345$$(TraceLogger, msg, scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, stackDelayRes, 195);
            tmp3.contTrace.last = tmp3.contTrace.last.next;
            return tmp3
          }
          tmp3 = runtime.resetDepth(tmp3, curDepth);
          tmp4 = tmp + tmp3;
          runtime.stackDepth = runtime.stackDepth + 1;
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
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$apply$Predef$_mls_L0_94_128$$(f, args, stackDelayRes, 0);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(f(...args))
  } 
  static pipeInto(x2, f1) {
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$pipeInto$Predef$_mls_L0_134_160$$(x2, f1, stackDelayRes, 2);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(f1(x2))
  } 
  static pipeFrom(f2, x3) {
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$pipeFrom$Predef$_mls_L0_165_191$$(f2, x3, stackDelayRes, 4);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(f2(x3))
  } 
  static tap(x4, f3) {
    let tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$tap$Predef$_mls_L0_197_221$$(x4, f3, tmp, curDepth, stackDelayRes, 6);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = runtime.safeCall(f3(x4));
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$tap$Predef$_mls_L0_197_221$$(x4, f3, tmp, curDepth, stackDelayRes, 7);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    return (tmp , x4)
  } 
  static pat(f4, x5) {
    let tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$pat$Predef$_mls_L0_226_250$$(f4, x5, tmp, curDepth, stackDelayRes, 9);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = runtime.safeCall(f4(x5));
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$pat$Predef$_mls_L0_226_250$$(f4, x5, tmp, curDepth, stackDelayRes, 10);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    return (tmp , x5)
  } 
  static andThen(f5, g) {
    return (x6) => {
      let tmp, curDepth, stackDelayRes;
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = Cont$func$andThen$Predef$_mls_L0_256_287$$(f5, g, x6, tmp, curDepth, stackDelayRes, 12);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = runtime.safeCall(f5(x6));
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$andThen$Predef$_mls_L0_256_287$$(f5, g, x6, tmp, curDepth, stackDelayRes, 13);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(g(tmp))
    }
  } 
  static compose(f6, g1) {
    return (x6) => {
      let tmp, curDepth, stackDelayRes;
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = Cont$func$compose$Predef$_mls_L0_292_323$$(f6, g1, x6, tmp, curDepth, stackDelayRes, 16);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = runtime.safeCall(g1(x6));
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$compose$Predef$_mls_L0_292_323$$(f6, g1, x6, tmp, curDepth, stackDelayRes, 17);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f6(tmp))
    }
  } 
  static passTo(receiver, f7) {
    return (...args1) => {
      let stackDelayRes;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = Cont$func$passTo$Predef$_mls_L0_329_384$$(receiver, f7, args1, stackDelayRes, 20);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f7(receiver, ...args1))
    }
  } 
  static call(receiver1, f8) {
    return (...args1) => {
      let stackDelayRes;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = Cont$func$call$Predef$_mls_L0_390_450$$(receiver1, f8, args1, stackDelayRes, 22);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return f8.call(receiver1, ...args1)
    }
  } 
  static pass1(f9) {
    return (...xs) => {
      let stackDelayRes;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = Cont$func$pass1$Predef$_mls_L0_456_481$$(f9, xs, stackDelayRes, 24);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f9(xs[0]))
    }
  } 
  static pass2(f10) {
    return (...xs) => {
      let stackDelayRes;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = Cont$func$pass2$Predef$_mls_L0_486_517$$(f10, xs, stackDelayRes, 26);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f10(xs[0], xs[1]))
    }
  } 
  static pass3(f11) {
    return (...xs) => {
      let stackDelayRes;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = Cont$func$pass3$Predef$_mls_L0_522_559$$(f11, xs, stackDelayRes, 28);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(f11(xs[0], xs[1], xs[2]))
    }
  } 
  static passing(f12, ...args1) {
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$passing$Predef$_mls_L0_565_608$$(f12, args1, stackDelayRes, 30);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return f12.bind(null, ...args1)
  } 
  static print(...xs) {
    let tmp, tmp1, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$print$Predef$_mls_L0_615_671$$(xs, tmp, tmp1, curDepth, stackDelayRes, 32);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = Predef.map(Predef.renderAsStr);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$print$Predef$_mls_L0_615_671$$(xs, tmp, tmp1, curDepth, stackDelayRes, 33);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = runtime.safeCall(tmp(...xs));
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$print$Predef$_mls_L0_615_671$$(xs, tmp, tmp1, curDepth, stackDelayRes, 34);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(globalThis.console.log(...tmp1))
  } 
  static printRaw(x6) {
    let tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$printRaw$Predef$_mls_L0_677_715$$(x6, tmp, curDepth, stackDelayRes, 38);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = Predef.render(x6);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$printRaw$Predef$_mls_L0_677_715$$(x6, tmp, curDepth, stackDelayRes, 39);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(globalThis.console.log(tmp))
  } 
  static interleave(sep) {
    return (...args2) => {
      let res, len, i, scrut, idx, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes;
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = Cont$func$interleave$Predef$_mls_L0_721_998$$(sep, args2, res, len, i, scrut, idx, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 42);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      scrut2 = args2.length === 0;
      if (scrut2 === true) {
        return []
      } else {
        tmp = args2.length * 2;
        tmp1 = tmp - 1;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp2 = globalThis.Array(tmp1);
        if (tmp2 instanceof runtime.EffectSig.class) {
          tmp2.contTrace.last.next = Cont$func$interleave$Predef$_mls_L0_721_998$$(sep, args2, res, len, i, scrut, idx, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 43);
          tmp2.contTrace.last = tmp2.contTrace.last.next;
          return tmp2
        }
        tmp2 = runtime.resetDepth(tmp2, curDepth);
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
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$renderAsStr$Predef$_mls_L0_1004_1064$$(arg, stackDelayRes, 50);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    if (typeof arg === 'string') {
      return arg
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      return Predef.render(arg)
    }
  } 
  static render(arg1) {
    let ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 53);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    if (arg1 === undefined) {
      return "undefined"
    } else if (arg1 === null) {
      return "null"
    } else if (arg1 instanceof globalThis.Array) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = Predef.fold(lambda);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 54);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = Predef.interleave(", ");
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 55);
        tmp1.contTrace.last = tmp1.contTrace.last.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = Predef.map(Predef.render);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 56);
        tmp2.contTrace.last = tmp2.contTrace.last.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = runtime.safeCall(tmp2(...arg1));
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 57);
        tmp3.contTrace.last = tmp3.contTrace.last.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = runtime.safeCall(tmp1(...tmp3));
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 58);
        tmp4.contTrace.last = tmp4.contTrace.last.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(tmp("[", ...tmp4, "]"))
    } else if (typeof arg1 === 'string') {
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(globalThis.JSON.stringify(arg1))
    } else if (arg1 instanceof globalThis.Set) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp5 = Predef.fold(lambda1);
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 59);
        tmp5.contTrace.last = tmp5.contTrace.last.next;
        return tmp5
      }
      tmp5 = runtime.resetDepth(tmp5, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp6 = Predef.interleave(", ");
      if (tmp6 instanceof runtime.EffectSig.class) {
        tmp6.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 60);
        tmp6.contTrace.last = tmp6.contTrace.last.next;
        return tmp6
      }
      tmp6 = runtime.resetDepth(tmp6, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp7 = Predef.map(Predef.render);
      if (tmp7 instanceof runtime.EffectSig.class) {
        tmp7.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 61);
        tmp7.contTrace.last = tmp7.contTrace.last.next;
        return tmp7
      }
      tmp7 = runtime.resetDepth(tmp7, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp8 = runtime.safeCall(tmp7(...arg1));
      if (tmp8 instanceof runtime.EffectSig.class) {
        tmp8.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 62);
        tmp8.contTrace.last = tmp8.contTrace.last.next;
        return tmp8
      }
      tmp8 = runtime.resetDepth(tmp8, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp9 = runtime.safeCall(tmp6(...tmp8));
      if (tmp9 instanceof runtime.EffectSig.class) {
        tmp9.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 63);
        tmp9.contTrace.last = tmp9.contTrace.last.next;
        return tmp9
      }
      tmp9 = runtime.resetDepth(tmp9, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(tmp5("Set{", ...tmp9, "}"))
    } else if (arg1 instanceof globalThis.Map) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp10 = Predef.fold(lambda2);
      if (tmp10 instanceof runtime.EffectSig.class) {
        tmp10.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 64);
        tmp10.contTrace.last = tmp10.contTrace.last.next;
        return tmp10
      }
      tmp10 = runtime.resetDepth(tmp10, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp11 = Predef.interleave(", ");
      if (tmp11 instanceof runtime.EffectSig.class) {
        tmp11.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 65);
        tmp11.contTrace.last = tmp11.contTrace.last.next;
        return tmp11
      }
      tmp11 = runtime.resetDepth(tmp11, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp12 = Predef.map(Predef.render);
      if (tmp12 instanceof runtime.EffectSig.class) {
        tmp12.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 66);
        tmp12.contTrace.last = tmp12.contTrace.last.next;
        return tmp12
      }
      tmp12 = runtime.resetDepth(tmp12, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp13 = runtime.safeCall(tmp12(...arg1));
      if (tmp13 instanceof runtime.EffectSig.class) {
        tmp13.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 67);
        tmp13.contTrace.last = tmp13.contTrace.last.next;
        return tmp13
      }
      tmp13 = runtime.resetDepth(tmp13, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp14 = runtime.safeCall(tmp11(...tmp13));
      if (tmp14 instanceof runtime.EffectSig.class) {
        tmp14.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 68);
        tmp14.contTrace.last = tmp14.contTrace.last.next;
        return tmp14
      }
      tmp14 = runtime.resetDepth(tmp14, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(tmp10("Map{", ...tmp14, "}"))
    } else if (arg1 instanceof globalThis.Function) {
      runtime.stackDepth = runtime.stackDepth + 1;
      p = globalThis.Object.getOwnPropertyDescriptor(arg1, "prototype");
      if (p instanceof runtime.EffectSig.class) {
        p.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 69);
        p.contTrace.last = p.contTrace.last.next;
        return p
      }
      p = runtime.resetDepth(p, curDepth);
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
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp19 = runtime.safeCall(globalThis.Object.entries(arg1));
          if (tmp19 instanceof runtime.EffectSig.class) {
            tmp19.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 70);
            tmp19.contTrace.last = tmp19.contTrace.last.next;
            return tmp19
          }
          tmp19 = runtime.resetDepth(tmp19, curDepth);
          es = tmp19;
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp20 = Predef.fold(lambda3);
          if (tmp20 instanceof runtime.EffectSig.class) {
            tmp20.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 71);
            tmp20.contTrace.last = tmp20.contTrace.last.next;
            return tmp20
          }
          tmp20 = runtime.resetDepth(tmp20, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp21 = Predef.interleave(", ");
          if (tmp21 instanceof runtime.EffectSig.class) {
            tmp21.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 72);
            tmp21.contTrace.last = tmp21.contTrace.last.next;
            return tmp21
          }
          tmp21 = runtime.resetDepth(tmp21, curDepth);
          tmp22 = lambda4;
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp23 = Predef.map(tmp22);
          if (tmp23 instanceof runtime.EffectSig.class) {
            tmp23.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 78);
            tmp23.contTrace.last = tmp23.contTrace.last.next;
            return tmp23
          }
          tmp23 = runtime.resetDepth(tmp23, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp24 = runtime.safeCall(tmp23(...es));
          if (tmp24 instanceof runtime.EffectSig.class) {
            tmp24.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 79);
            tmp24.contTrace.last = tmp24.contTrace.last.next;
            return tmp24
          }
          tmp24 = runtime.resetDepth(tmp24, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp25 = runtime.safeCall(tmp21(...tmp24));
          if (tmp25 instanceof runtime.EffectSig.class) {
            tmp25.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 80);
            tmp25.contTrace.last = tmp25.contTrace.last.next;
            return tmp25
          }
          tmp25 = runtime.resetDepth(tmp25, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          return runtime.safeCall(tmp20("{", ...tmp25, "}"))
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          return globalThis.String(arg1)
        }
      }
    } else if (arg1 instanceof globalThis.Object) {
      scrut = arg1.constructor.name;
      if (scrut === "Object") {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp26 = runtime.safeCall(globalThis.Object.entries(arg1));
        if (tmp26 instanceof runtime.EffectSig.class) {
          tmp26.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 81);
          tmp26.contTrace.last = tmp26.contTrace.last.next;
          return tmp26
        }
        tmp26 = runtime.resetDepth(tmp26, curDepth);
        es = tmp26;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp27 = Predef.fold(lambda5);
        if (tmp27 instanceof runtime.EffectSig.class) {
          tmp27.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 82);
          tmp27.contTrace.last = tmp27.contTrace.last.next;
          return tmp27
        }
        tmp27 = runtime.resetDepth(tmp27, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp28 = Predef.interleave(", ");
        if (tmp28 instanceof runtime.EffectSig.class) {
          tmp28.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 83);
          tmp28.contTrace.last = tmp28.contTrace.last.next;
          return tmp28
        }
        tmp28 = runtime.resetDepth(tmp28, curDepth);
        tmp29 = lambda6;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp30 = Predef.map(tmp29);
        if (tmp30 instanceof runtime.EffectSig.class) {
          tmp30.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 89);
          tmp30.contTrace.last = tmp30.contTrace.last.next;
          return tmp30
        }
        tmp30 = runtime.resetDepth(tmp30, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp31 = runtime.safeCall(tmp30(...es));
        if (tmp31 instanceof runtime.EffectSig.class) {
          tmp31.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 90);
          tmp31.contTrace.last = tmp31.contTrace.last.next;
          return tmp31
        }
        tmp31 = runtime.resetDepth(tmp31, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp32 = runtime.safeCall(tmp28(...tmp31));
        if (tmp32 instanceof runtime.EffectSig.class) {
          tmp32.contTrace.last.next = Cont$func$render$Predef$_mls_L0_1070_2080$$(arg1, ts, scrut, es, p, scrut1, scrut2, scrut3, nme, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, curDepth, stackDelayRes, 91);
          tmp32.contTrace.last = tmp32.contTrace.last.next;
          return tmp32
        }
        tmp32 = runtime.resetDepth(tmp32, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(tmp27("{", ...tmp32, "}"))
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        return globalThis.String(arg1)
      }
    } else {
      ts = arg1["toString"];
      if (ts === undefined) {
        tmp33 = typeof arg1;
        tmp34 = "[" + tmp33;
        return tmp34 + "]"
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(ts.call(arg1))
      }
    }
  } 
  static notImplemented(msg) {
    let tmp, tmp1, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$notImplemented$Predef$_mls_L0_2115_2180$$(msg, tmp, tmp1, curDepth, stackDelayRes, 133);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    tmp = "Not implemented: " + msg;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = globalThis.Error(tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$notImplemented$Predef$_mls_L0_2115_2180$$(msg, tmp, tmp1, curDepth, stackDelayRes, 134);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    throw tmp1;
  } 
  static get notImplementedError() {
    let tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$$(tmp, curDepth, stackDelayRes, 136);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = globalThis.Error("Not implemented");
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$notImplementedError$Predef$_mls_L0_2185_2243$$(tmp, curDepth, stackDelayRes, 137);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    throw tmp;
  } 
  static tuple(...xs1) {
    return xs1
  } 
  static tupleSlice(xs2, i, j) {
    let tmp, stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$tupleSlice$Predef$_mls_L0_2273_2475$$(xs2, i, j, tmp, stackDelayRes, 139);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    tmp = xs2.length - j;
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(globalThis.Array.prototype.slice.call(xs2, i, tmp))
  } 
  static tupleGet(xs3, i1) {
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$tupleGet$Predef$_mls_L0_2481_2617$$(xs3, i1, stackDelayRes, 141);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return globalThis.Array.prototype.at.call(xs3, i1)
  } 
  static map(f13) {
    return (...xs4) => {
      let tmp, curDepth, stackDelayRes;
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = Cont$func$map$Predef$_mls_L0_2623_2655$$(f13, xs4, tmp, curDepth, stackDelayRes, 143);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = Predef.pass1(f13);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$map$Predef$_mls_L0_2623_2655$$(f13, xs4, tmp, curDepth, stackDelayRes, 144);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(xs4.map(tmp))
    }
  } 
  static fold(f14) {
    return (init, ...rest) => {
      let i2, len, scrut, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes;
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = Cont$func$fold$Predef$_mls_L0_2661_2803$$(f14, init, rest, i2, len, scrut, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 147);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      i2 = 0;
      len = rest.length;
      tmp4: while (true) {
        scrut = i2 < len;
        if (scrut === true) {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp = runtime.safeCall(rest.at(i2));
          if (tmp instanceof runtime.EffectSig.class) {
            tmp.contTrace.last.next = Cont$func$fold$Predef$_mls_L0_2661_2803$$(f14, init, rest, i2, len, scrut, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 148);
            tmp.contTrace.last = tmp.contTrace.last.next;
            return tmp
          }
          tmp = runtime.resetDepth(tmp, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp1 = runtime.safeCall(f14(init, tmp));
          if (tmp1 instanceof runtime.EffectSig.class) {
            tmp1.contTrace.last.next = Cont$func$fold$Predef$_mls_L0_2661_2803$$(f14, init, rest, i2, len, scrut, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 149);
            tmp1.contTrace.last = tmp1.contTrace.last.next;
            return tmp1
          }
          tmp1 = runtime.resetDepth(tmp1, curDepth);
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
      let len, i2, init, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes;
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = Cont$func$foldr$Predef$_mls_L0_2886_3101$$(f15, first, rest, len, i2, init, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 154);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      len = rest.length;
      scrut1 = len == 0;
      if (scrut1 === true) {
        return first
      } else {
        tmp = len - 1;
        i2 = tmp;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp1 = runtime.safeCall(rest.at(i2));
        if (tmp1 instanceof runtime.EffectSig.class) {
          tmp1.contTrace.last.next = Cont$func$foldr$Predef$_mls_L0_2886_3101$$(f15, first, rest, len, i2, init, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 155);
          tmp1.contTrace.last = tmp1.contTrace.last.next;
          return tmp1
        }
        tmp1 = runtime.resetDepth(tmp1, curDepth);
        init = tmp1;
        tmp6: while (true) {
          scrut = i2 > 0;
          if (scrut === true) {
            tmp2 = i2 - 1;
            i2 = tmp2;
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = runtime.safeCall(rest.at(i2));
            if (tmp3 instanceof runtime.EffectSig.class) {
              tmp3.contTrace.last.next = Cont$func$foldr$Predef$_mls_L0_2886_3101$$(f15, first, rest, len, i2, init, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 156);
              tmp3.contTrace.last = tmp3.contTrace.last.next;
              return tmp3
            }
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = runtime.safeCall(f15(tmp3, init));
            if (tmp4 instanceof runtime.EffectSig.class) {
              tmp4.contTrace.last.next = Cont$func$foldr$Predef$_mls_L0_2886_3101$$(f15, first, rest, len, i2, init, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 157);
              tmp4.contTrace.last = tmp4.contTrace.last.next;
              return tmp4
            }
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            init = tmp4;
            tmp5 = runtime.Unit;
            continue tmp6;
          } else {
            tmp5 = runtime.Unit;
          }
          break;
        }
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(f15(first, init))
      }
    }
  } 
  static mkStr(...xs4) {
    let tmp, tmp1, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$mkStr$Predef$_mls_L0_3107_3176$$(xs4, tmp, tmp1, curDepth, stackDelayRes, 164);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    tmp = lambda7;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = Predef.fold(tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$mkStr$Predef$_mls_L0_3107_3176$$(xs4, tmp, tmp1, curDepth, stackDelayRes, 168);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(tmp1(...xs4))
  } 
  static stringStartsWith(string, prefix) {
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$stringStartsWith$Predef$_mls_L0_3183_3243$$(string, prefix, stackDelayRes, 171);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(string.startsWith(prefix))
  } 
  static stringGet(string1, i2) {
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$stringGet$Predef$_mls_L0_3249_3284$$(string1, i2, stackDelayRes, 173);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(string1.at(i2))
  } 
  static stringDrop(string2, n) {
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$stringDrop$Predef$_mls_L0_3290_3329$$(string2, n, stackDelayRes, 175);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(string2.slice(n))
  } 
  static get unreachable() {
    let tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$unreachable$Predef$_mls_L0_3336_3376$$(tmp, curDepth, stackDelayRes, 177);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = globalThis.Error("unreachable");
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$unreachable$Predef$_mls_L0_3336_3376$$(tmp, curDepth, stackDelayRes, 178);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    throw tmp;
  } 
  static checkArgs(functionName, expected, isUB, got) {
    let scrut, name, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, tmp9, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$checkArgs$Predef$_mls_L0_3382_3927$$(functionName, expected, isUB, got, scrut, name, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, tmp9, stackDelayRes, 180);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
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
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp5 = Predef.fold(lambda8);
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.contTrace.last.next = Cont$func$checkArgs$Predef$_mls_L0_3382_3927$$(functionName, expected, isUB, got, scrut, name, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, tmp9, stackDelayRes, 181);
        tmp5.contTrace.last = tmp5.contTrace.last.next;
        return tmp5
      }
      tmp5 = runtime.resetDepth(tmp5, curDepth);
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
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp8 = runtime.safeCall(tmp5("Function", name, " expected ", tmp6, expected, " argument", tmp7, " but got ", got));
      if (tmp8 instanceof runtime.EffectSig.class) {
        tmp8.contTrace.last.next = Cont$func$checkArgs$Predef$_mls_L0_3382_3927$$(functionName, expected, isUB, got, scrut, name, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, tmp9, stackDelayRes, 182);
        tmp8.contTrace.last = tmp8.contTrace.last.next;
        return tmp8
      }
      tmp8 = runtime.resetDepth(tmp8, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp9 = globalThis.Error(tmp8);
      if (tmp9 instanceof runtime.EffectSig.class) {
        tmp9.contTrace.last.next = Cont$func$checkArgs$Predef$_mls_L0_3382_3927$$(functionName, expected, isUB, got, scrut, name, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, tmp9, stackDelayRes, 183);
        tmp9.contTrace.last = tmp9.contTrace.last.next;
        return tmp9
      }
      tmp9 = runtime.resetDepth(tmp9, curDepth);
      throw tmp9;
    } else {
      return runtime.Unit
    }
  } 
  static enterHandleBlock(handler, body) {
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$enterHandleBlock$Predef$_mls_L0_4467_4735$$(handler, body, stackDelayRes, 190);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return Runtime.enterHandleBlock(handler, body)
  }
  static toString() { return "Predef"; }
};
let Predef = Predef1; export default Predef;
