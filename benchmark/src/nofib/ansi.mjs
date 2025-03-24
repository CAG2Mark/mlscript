import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let ansi1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, Cont$func$goto$ansi$_mls_L0_262_396$1, Cont$func$at$ansi$_mls_L0_402_452$1, Cont$func$highlight$ansi$_mls_L0_458_536$1, Cont$func$end$ansi$_mls_L0_542_573$1, Cont$func$readChar$ansi$_mls_L0_579_666$1, Cont$func$peekChar$ansi$_mls_L0_672_764$1, Cont$func$lambda$$10, Cont$func$pressAnyKey$ansi$_mls_L0_770_829$1, Cont$func$unreadChar$ansi$_mls_L0_835_874$1, Cont$func$writeChar$ansi$_mls_L0_880_918$1, Cont$func$writeString$ansi$_mls_L0_924_964$1, Cont$func$writes$ansi$_mls_L0_970_1018$1, Cont$func$ringBell$ansi$_mls_L0_1024_1069$1, Cont$func$clearScreen$ansi$_mls_L0_1075_1117$1, Cont$func$lambda$$11, Cont$func$writeAt$ansi$_mls_L0_1123_1205$1, Cont$func$lambda$$12, Cont$func$moveTo$ansi$_mls_L0_1211_1284$1, Cont$func$returnn$ansi$_mls_L0_1290_1331$1, Cont$func$deletee$ansi$_mls_L0_1430_1603$1, Cont$func$lambda$$13, Cont$func$lambda$$14, Cont$func$readAt$ansi$_mls_L0_2058_2153$1, Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$1, Cont$func$lambda$$15, Cont$func$lambda$$16, Cont$func$lambda$$17, Cont$func$lambda$$18, Cont$func$program$ansi$_mls_L0_2300_3219$1, Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$1, Cont$func$lambda$$19, Cont$func$lambda$$$ctor, Cont$func$lambda$$$, Cont$func$goto$ansi$_mls_L0_262_396$$ctor, Cont$func$goto$ansi$_mls_L0_262_396$$, Cont$func$at$ansi$_mls_L0_402_452$$ctor, Cont$func$at$ansi$_mls_L0_402_452$$, Cont$func$highlight$ansi$_mls_L0_458_536$$ctor, Cont$func$highlight$ansi$_mls_L0_458_536$$, Cont$func$end$ansi$_mls_L0_542_573$$ctor, Cont$func$end$ansi$_mls_L0_542_573$$, Cont$func$readChar$ansi$_mls_L0_579_666$$ctor, Cont$func$readChar$ansi$_mls_L0_579_666$$, Cont$func$peekChar$ansi$_mls_L0_672_764$$ctor, Cont$func$peekChar$ansi$_mls_L0_672_764$$, lambda$, Cont$func$lambda$$$ctor1, Cont$func$lambda$$$1, Cont$func$pressAnyKey$ansi$_mls_L0_770_829$$ctor, Cont$func$pressAnyKey$ansi$_mls_L0_770_829$$, Cont$func$unreadChar$ansi$_mls_L0_835_874$$ctor, Cont$func$unreadChar$ansi$_mls_L0_835_874$$, Cont$func$writeChar$ansi$_mls_L0_880_918$$ctor, Cont$func$writeChar$ansi$_mls_L0_880_918$$, Cont$func$writeString$ansi$_mls_L0_924_964$$ctor, Cont$func$writeString$ansi$_mls_L0_924_964$$, Cont$func$writes$ansi$_mls_L0_970_1018$$ctor, Cont$func$writes$ansi$_mls_L0_970_1018$$, Cont$func$ringBell$ansi$_mls_L0_1024_1069$$ctor, Cont$func$ringBell$ansi$_mls_L0_1024_1069$$, Cont$func$clearScreen$ansi$_mls_L0_1075_1117$$ctor, Cont$func$clearScreen$ansi$_mls_L0_1075_1117$$, lambda$1, Cont$func$lambda$$$ctor2, Cont$func$lambda$$$2, Cont$func$writeAt$ansi$_mls_L0_1123_1205$$ctor, Cont$func$writeAt$ansi$_mls_L0_1123_1205$$, lambda$2, Cont$func$lambda$$$ctor3, Cont$func$lambda$$$3, Cont$func$moveTo$ansi$_mls_L0_1211_1284$$ctor, Cont$func$moveTo$ansi$_mls_L0_1211_1284$$, Cont$func$returnn$ansi$_mls_L0_1290_1331$$ctor, Cont$func$returnn$ansi$_mls_L0_1290_1331$$, Cont$func$deletee$ansi$_mls_L0_1430_1603$$ctor, Cont$func$deletee$ansi$_mls_L0_1430_1603$$, lambda$3, lambda$4, Cont$func$lambda$$$ctor4, Cont$func$lambda$$$4, Cont$func$lambda$$$ctor5, Cont$func$lambda$$$5, Cont$func$readAt$ansi$_mls_L0_2058_2153$$ctor, Cont$func$readAt$ansi$_mls_L0_2058_2153$$, Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$$ctor, Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$$, Cont$func$lambda$$$ctor6, Cont$func$lambda$$$6, Cont$func$lambda$$$ctor7, Cont$func$lambda$$$7, Cont$func$lambda$$$ctor8, Cont$func$lambda$$$8, Cont$func$lambda$$$ctor9, Cont$func$lambda$$$9, Cont$func$program$ansi$_mls_L0_2300_3219$$ctor, Cont$func$program$ansi$_mls_L0_2300_3219$$, Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$$ctor, Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$$;
Cont$func$lambda$$$ = function Cont$func$lambda$$$(tmp$0, curDepth$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$19.class(pc);
  return tmp(tmp$0, curDepth$1, stackDelayRes$2)
};
Cont$func$lambda$$$ctor = function Cont$func$lambda$$$ctor(tmp$0, curDepth$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$19.class(pc);
    return tmp(tmp$0, curDepth$1, stackDelayRes$2)
  }
};
Cont$func$lambda$$19 = function Cont$func$lambda$$(pc1) {
  return (tmp$01, curDepth$11, stackDelayRes$21) => {
    return new Cont$func$lambda$$.class(pc1)(tmp$01, curDepth$11, stackDelayRes$21);
  }
};
Cont$func$lambda$$19.class = class Cont$func$lambda$$ extends runtime.FunctionContFrame.class {
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
    if (this.pc === 216) {
      this.stackDelayRes$2 = value$;
    } else if (this.pc === 217) {
      this.tmp$0 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 216) {
        this.pc = 219;
        continue contLoop;
      } else if (this.pc === 218) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.nofibListToString(this.tmp$0)
      } else if (this.pc === 219) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$0 = ansi1.testAnsi_nofib(1);
        if (this.tmp$0 instanceof runtime.EffectSig.class) {
          this.pc = 217;
          this.tmp$0.contTrace.last.next = this;
          this.tmp$0.contTrace.last = this;
          return this.tmp$0
        }
        this.pc = 217;
        continue contLoop;
      } else if (this.pc === 217) {
        this.tmp$0 = runtime.resetDepth(this.tmp$0, this.curDepth$1);
        this.pc = 218;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$$ = function Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$$(n$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5, pc) {
  let tmp;
  tmp = new Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$1.class(pc);
  return tmp(n$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5)
};
Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$$ctor = function Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$$ctor(n$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$1.class(pc);
    return tmp(n$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5)
  }
};
Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$1 = function Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$(pc1) {
  return (n$01, tmp$11, tmp$21, tmp$31, curDepth$41, stackDelayRes$51) => {
    return new Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$.class(pc1)(n$01, tmp$11, tmp$21, tmp$31, curDepth$41, stackDelayRes$51);
  }
};
Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$1.class = class Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (n$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5) => {
      let tmp;
      tmp = super(null);
      this.n$0 = n$0;
      this.tmp$1 = tmp$1;
      this.tmp$2 = tmp$2;
      this.tmp$3 = tmp$3;
      this.curDepth$4 = curDepth$4;
      this.stackDelayRes$5 = stackDelayRes$5;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 207) {
      this.stackDelayRes$5 = value$;
    } else if (this.pc === 208) {
      this.tmp$1 = value$;
    } else if (this.pc === 209) {
      this.tmp$2 = value$;
    } else if (this.pc === 210) {
      this.tmp$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 207) {
        this.pc = 214;
        continue contLoop;
      } else if (this.pc === 213) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = NofibPrelude.foldr(NofibPrelude.compose, lambda9, this.tmp$1);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 209;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 209;
        continue contLoop;
      } else if (this.pc === 214) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = NofibPrelude.replicate(this.n$0, ansi1.program);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 208;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 208;
        continue contLoop;
      } else if (this.pc === 208) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$4);
        this.pc = 213;
        continue contLoop;
      } else if (this.pc === 209) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$4);
        this.pc = 212;
        continue contLoop;
      } else if (this.pc === 211) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.tmp$2(this.tmp$3))
      } else if (this.pc === 212) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = NofibPrelude.nofibStringToList("testtesttest");
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 210;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 210;
        continue contLoop;
      } else if (this.pc === 210) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$4);
        this.pc = 211;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda9 = (undefined, function (x) {
  return x
});
Cont$func$program$ansi$_mls_L0_2300_3219$$ = function Cont$func$program$ansi$_mls_L0_2300_3219$$(input$0, tmp$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, curDepth$22, stackDelayRes$23, pc) {
  let tmp;
  tmp = new Cont$func$program$ansi$_mls_L0_2300_3219$1.class(pc);
  return tmp(input$0, tmp$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, curDepth$22, stackDelayRes$23)
};
Cont$func$program$ansi$_mls_L0_2300_3219$$ctor = function Cont$func$program$ansi$_mls_L0_2300_3219$$ctor(input$0, tmp$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, curDepth$22, stackDelayRes$23) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$program$ansi$_mls_L0_2300_3219$1.class(pc);
    return tmp(input$0, tmp$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, curDepth$22, stackDelayRes$23)
  }
};
Cont$func$program$ansi$_mls_L0_2300_3219$1 = function Cont$func$program$ansi$_mls_L0_2300_3219$(pc1) {
  return (input$01, tmp$110, tmp$22, tmp$31, tmp$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, tmp$171, tmp$181, tmp$191, tmp$201, tmp$211, curDepth$221, stackDelayRes$231) => {
    return new Cont$func$program$ansi$_mls_L0_2300_3219$.class(pc1)(input$01, tmp$110, tmp$22, tmp$31, tmp$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, tmp$171, tmp$181, tmp$191, tmp$201, tmp$211, curDepth$221, stackDelayRes$231);
  }
};
Cont$func$program$ansi$_mls_L0_2300_3219$1.class = class Cont$func$program$ansi$_mls_L0_2300_3219$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (input$0, tmp$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, curDepth$22, stackDelayRes$23) => {
      let tmp;
      tmp = super(null);
      this.input$0 = input$0;
      this.tmp$1 = tmp$1;
      this.tmp$2 = tmp$2;
      this.tmp$3 = tmp$3;
      this.tmp$4 = tmp$4;
      this.tmp$5 = tmp$5;
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
      this.tmp$16 = tmp$16;
      this.tmp$17 = tmp$17;
      this.tmp$18 = tmp$18;
      this.tmp$19 = tmp$19;
      this.tmp$20 = tmp$20;
      this.tmp$21 = tmp$21;
      this.curDepth$22 = curDepth$22;
      this.stackDelayRes$23 = stackDelayRes$23;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 139) {
      this.stackDelayRes$23 = value$;
    } else if (this.pc === 140) {
      this.tmp$1 = value$;
    } else if (this.pc === 141) {
      this.tmp$2 = value$;
    } else if (this.pc === 142) {
      this.tmp$3 = value$;
    } else if (this.pc === 143) {
      this.tmp$4 = value$;
    } else if (this.pc === 144) {
      this.tmp$5 = value$;
    } else if (this.pc === 145) {
      this.tmp$6 = value$;
    } else if (this.pc === 146) {
      this.tmp$7 = value$;
    } else if (this.pc === 147) {
      this.tmp$8 = value$;
    } else if (this.pc === 148) {
      this.tmp$9 = value$;
    } else if (this.pc === 149) {
      this.tmp$10 = value$;
    } else if (this.pc === 150) {
      this.tmp$11 = value$;
    } else if (this.pc === 151) {
      this.tmp$12 = value$;
    } else if (this.pc === 152) {
      this.tmp$13 = value$;
    } else if (this.pc === 153) {
      this.tmp$14 = value$;
    } else if (this.pc === 154) {
      this.tmp$15 = value$;
    } else if (this.pc === 155) {
      this.tmp$16 = value$;
    } else if (this.pc === 156) {
      this.tmp$17 = value$;
    } else if (this.pc === 157) {
      this.tmp$18 = value$;
    } else if (this.pc === 158) {
      this.tmp$19 = value$;
    } else if (this.pc === 159) {
      this.tmp$20 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 139) {
        this.pc = 206;
        continue contLoop;
      } else if (this.pc === 186) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.writes(this.tmp$20, this.tmp$21, this.input$0)
      } else if (this.pc === 187) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$20 = NofibPrelude.Cons(ansi1.cls, this.tmp$19);
        if (this.tmp$20 instanceof runtime.EffectSig.class) {
          this.pc = 159;
          this.tmp$20.contTrace.last.next = this;
          this.tmp$20.contTrace.last = this;
          return this.tmp$20
        }
        this.pc = 159;
        continue contLoop;
      } else if (this.pc === 188) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$19 = NofibPrelude.Cons(this.tmp$3, this.tmp$18);
        if (this.tmp$19 instanceof runtime.EffectSig.class) {
          this.pc = 158;
          this.tmp$19.contTrace.last.next = this;
          this.tmp$19.contTrace.last = this;
          return this.tmp$19
        }
        this.pc = 158;
        continue contLoop;
      } else if (this.pc === 204) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = ansi1.at([
          17,
          5
        ], this.tmp$2);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 142;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 142;
        continue contLoop;
      } else if (this.pc === 205) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = ansi1.highlight(this.tmp$1);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 141;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 141;
        continue contLoop;
      } else if (this.pc === 206) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = NofibPrelude.nofibStringToList("Demonstration program");
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 140;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 140;
        continue contLoop;
      } else if (this.pc === 140) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$22);
        this.pc = 205;
        continue contLoop;
      } else if (this.pc === 141) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$22);
        this.pc = 204;
        continue contLoop;
      } else if (this.pc === 142) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$22);
        this.pc = 203;
        continue contLoop;
      } else if (this.pc === 189) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$18 = NofibPrelude.Cons(this.tmp$5, this.tmp$17);
        if (this.tmp$18 instanceof runtime.EffectSig.class) {
          this.pc = 157;
          this.tmp$18.contTrace.last.next = this;
          this.tmp$18.contTrace.last = this;
          return this.tmp$18
        }
        this.pc = 157;
        continue contLoop;
      } else if (this.pc === 202) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = ansi1.at([
          48,
          5
        ], this.tmp$4);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 144;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 144;
        continue contLoop;
      } else if (this.pc === 203) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$4 = NofibPrelude.nofibStringToList("Version 1.0");
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 143;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 143;
        continue contLoop;
      } else if (this.pc === 143) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$22);
        this.pc = 202;
        continue contLoop;
      } else if (this.pc === 144) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$22);
        this.pc = 201;
        continue contLoop;
      } else if (this.pc === 190) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$17 = NofibPrelude.Cons(this.tmp$7, this.tmp$16);
        if (this.tmp$17 instanceof runtime.EffectSig.class) {
          this.pc = 156;
          this.tmp$17.contTrace.last.next = this;
          this.tmp$17.contTrace.last = this;
          return this.tmp$17
        }
        this.pc = 156;
        continue contLoop;
      } else if (this.pc === 200) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = ansi1.at([
          17,
          7
        ], this.tmp$6);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 146;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 146;
        continue contLoop;
      } else if (this.pc === 201) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = NofibPrelude.nofibStringToList("This program illustrates a simple approach");
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 145;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 145;
        continue contLoop;
      } else if (this.pc === 145) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$22);
        this.pc = 200;
        continue contLoop;
      } else if (this.pc === 146) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$22);
        this.pc = 199;
        continue contLoop;
      } else if (this.pc === 191) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$16 = NofibPrelude.Cons(this.tmp$9, this.tmp$15);
        if (this.tmp$16 instanceof runtime.EffectSig.class) {
          this.pc = 155;
          this.tmp$16.contTrace.last.next = this;
          this.tmp$16.contTrace.last = this;
          return this.tmp$16
        }
        this.pc = 155;
        continue contLoop;
      } else if (this.pc === 198) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = ansi1.at([
          17,
          8
        ], this.tmp$8);
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 148;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 148;
        continue contLoop;
      } else if (this.pc === 199) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = NofibPrelude.nofibStringToList("to screen-based interactive programs using");
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 147;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 147;
        continue contLoop;
      } else if (this.pc === 147) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$22);
        this.pc = 198;
        continue contLoop;
      } else if (this.pc === 148) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$22);
        this.pc = 197;
        continue contLoop;
      } else if (this.pc === 192) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$15 = NofibPrelude.Cons(this.tmp$11, this.tmp$14);
        if (this.tmp$15 instanceof runtime.EffectSig.class) {
          this.pc = 154;
          this.tmp$15.contTrace.last.next = this;
          this.tmp$15.contTrace.last = this;
          return this.tmp$15
        }
        this.pc = 154;
        continue contLoop;
      } else if (this.pc === 196) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$11 = ansi1.at([
          17,
          9
        ], this.tmp$10);
        if (this.tmp$11 instanceof runtime.EffectSig.class) {
          this.pc = 150;
          this.tmp$11.contTrace.last.next = this;
          this.tmp$11.contTrace.last = this;
          return this.tmp$11
        }
        this.pc = 150;
        continue contLoop;
      } else if (this.pc === 197) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$10 = NofibPrelude.nofibStringToList("the Hugs functional programming system.");
        if (this.tmp$10 instanceof runtime.EffectSig.class) {
          this.pc = 149;
          this.tmp$10.contTrace.last.next = this;
          this.tmp$10.contTrace.last = this;
          return this.tmp$10
        }
        this.pc = 149;
        continue contLoop;
      } else if (this.pc === 149) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$22);
        this.pc = 196;
        continue contLoop;
      } else if (this.pc === 150) {
        this.tmp$11 = runtime.resetDepth(this.tmp$11, this.curDepth$22);
        this.pc = 195;
        continue contLoop;
      } else if (this.pc === 193) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$14 = NofibPrelude.Cons(this.tmp$13, NofibPrelude.Nil);
        if (this.tmp$14 instanceof runtime.EffectSig.class) {
          this.pc = 153;
          this.tmp$14.contTrace.last.next = this;
          this.tmp$14.contTrace.last = this;
          return this.tmp$14
        }
        this.pc = 153;
        continue contLoop;
      } else if (this.pc === 194) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$13 = ansi1.at([
          17,
          11
        ], this.tmp$12);
        if (this.tmp$13 instanceof runtime.EffectSig.class) {
          this.pc = 152;
          this.tmp$13.contTrace.last.next = this;
          this.tmp$13.contTrace.last = this;
          return this.tmp$13
        }
        this.pc = 152;
        continue contLoop;
      } else if (this.pc === 195) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$12 = NofibPrelude.nofibStringToList("Please press any key to continue ...");
        if (this.tmp$12 instanceof runtime.EffectSig.class) {
          this.pc = 151;
          this.tmp$12.contTrace.last.next = this;
          this.tmp$12.contTrace.last = this;
          return this.tmp$12
        }
        this.pc = 151;
        continue contLoop;
      } else if (this.pc === 151) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$22);
        this.pc = 194;
        continue contLoop;
      } else if (this.pc === 152) {
        this.tmp$13 = runtime.resetDepth(this.tmp$13, this.curDepth$22);
        this.pc = 193;
        continue contLoop;
      } else if (this.pc === 153) {
        this.tmp$14 = runtime.resetDepth(this.tmp$14, this.curDepth$22);
        this.pc = 192;
        continue contLoop;
      } else if (this.pc === 154) {
        this.tmp$15 = runtime.resetDepth(this.tmp$15, this.curDepth$22);
        this.pc = 191;
        continue contLoop;
      } else if (this.pc === 155) {
        this.tmp$16 = runtime.resetDepth(this.tmp$16, this.curDepth$22);
        this.pc = 190;
        continue contLoop;
      } else if (this.pc === 156) {
        this.tmp$17 = runtime.resetDepth(this.tmp$17, this.curDepth$22);
        this.pc = 189;
        continue contLoop;
      } else if (this.pc === 157) {
        this.tmp$18 = runtime.resetDepth(this.tmp$18, this.curDepth$22);
        this.pc = 188;
        continue contLoop;
      } else if (this.pc === 158) {
        this.tmp$19 = runtime.resetDepth(this.tmp$19, this.curDepth$22);
        this.pc = 187;
        continue contLoop;
      } else if (this.pc === 159) {
        this.tmp$20 = runtime.resetDepth(this.tmp$20, this.curDepth$22);
        this.tmp$21 = lambda5;
        this.pc = 186;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$program$ansi$_mls_L0_2300_3219$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$9 = function Cont$func$lambda$$$(x$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$18.class(pc);
  return tmp(x$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5)
};
Cont$func$lambda$$$ctor9 = function Cont$func$lambda$$$ctor(x$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$18.class(pc);
    return tmp(x$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5)
  }
};
Cont$func$lambda$$18 = function Cont$func$lambda$$(pc1) {
  return (x$01, tmp$11, tmp$21, tmp$31, curDepth$41, stackDelayRes$51) => {
    return new Cont$func$lambda$$.class(pc1)(x$01, tmp$11, tmp$21, tmp$31, curDepth$41, stackDelayRes$51);
  }
};
Cont$func$lambda$$18.class = class Cont$func$lambda$$1 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5) => {
      let tmp;
      tmp = super(null);
      this.x$0 = x$0;
      this.tmp$1 = tmp$1;
      this.tmp$2 = tmp$2;
      this.tmp$3 = tmp$3;
      this.curDepth$4 = curDepth$4;
      this.stackDelayRes$5 = stackDelayRes$5;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 160) {
      this.stackDelayRes$5 = value$;
    } else if (this.pc === 161) {
      this.tmp$1 = value$;
    } else if (this.pc === 182) {
      this.tmp$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 160) {
        this.pc = 185;
        continue contLoop;
      } else if (this.pc === 183) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.pressAnyKey(this.tmp$3, this.x$0)
      } else if (this.pc === 184) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = ansi1.promptReadAt([
          17,
          15
        ], 18, this.tmp$1, this.tmp$2);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 182;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 182;
        continue contLoop;
      } else if (this.pc === 185) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = NofibPrelude.nofibStringToList("Please enter your name: ");
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 161;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 161;
        continue contLoop;
      } else if (this.pc === 161) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$4);
        this.tmp$2 = lambda6;
        this.pc = 184;
        continue contLoop;
      } else if (this.pc === 182) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$4);
        this.pc = 183;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$8 = function Cont$func$lambda$$$(name$0, reply$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$17.class(pc);
  return tmp(name$0, reply$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11)
};
Cont$func$lambda$$$ctor8 = function Cont$func$lambda$$$ctor(name$0, reply$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$17.class(pc);
    return tmp(name$0, reply$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11)
  }
};
Cont$func$lambda$$17 = function Cont$func$lambda$$(pc1) {
  return (name$01, reply$11, tmp$21, tmp$31, tmp$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, curDepth$101, stackDelayRes$111) => {
    return new Cont$func$lambda$$.class(pc1)(name$01, reply$11, tmp$21, tmp$31, tmp$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, curDepth$101, stackDelayRes$111);
  }
};
Cont$func$lambda$$17.class = class Cont$func$lambda$$2 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (name$0, reply$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, stackDelayRes$11) => {
      let tmp;
      tmp = super(null);
      this.name$0 = name$0;
      this.reply$1 = reply$1;
      this.tmp$2 = tmp$2;
      this.tmp$3 = tmp$3;
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
    if (this.pc === 162) {
      this.stackDelayRes$11 = value$;
    } else if (this.pc === 163) {
      this.tmp$2 = value$;
    } else if (this.pc === 164) {
      this.tmp$3 = value$;
    } else if (this.pc === 165) {
      this.tmp$4 = value$;
    } else if (this.pc === 166) {
      this.tmp$5 = value$;
    } else if (this.pc === 167) {
      this.tmp$6 = value$;
    } else if (this.pc === 174) {
      this.tmp$9 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 162) {
        this.pc = 181;
        continue contLoop;
      } else if (this.pc === 178) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = NofibPrelude.append(this.tmp$2, this.tmp$4);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 166;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 166;
        continue contLoop;
      } else if (this.pc === 181) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = NofibPrelude.nofibStringToList("Hello ");
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 163;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 163;
        continue contLoop;
      } else if (this.pc === 163) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$10);
        this.pc = 180;
        continue contLoop;
      } else if (this.pc === 179) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$4 = NofibPrelude.append(this.name$0, this.tmp$3);
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 165;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 165;
        continue contLoop;
      } else if (this.pc === 180) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = NofibPrelude.nofibStringToList("!");
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 164;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 164;
        continue contLoop;
      } else if (this.pc === 164) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$10);
        this.pc = 179;
        continue contLoop;
      } else if (this.pc === 165) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$10);
        this.pc = 178;
        continue contLoop;
      } else if (this.pc === 166) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$10);
        this.reply$1 = this.tmp$5;
        this.pc = 177;
        continue contLoop;
      } else if (this.pc === 175) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.writeAt([
          this.tmp$8,
          18
        ], this.reply$1, this.tmp$9)
      } else if (this.pc === 177) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = NofibPrelude.listLen(this.reply$1);
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 167;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 167;
        continue contLoop;
      } else if (this.pc === 167) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$10);
        this.tmp$7 = this.tmp$6 / 2;
        this.tmp$8 = 40 - this.tmp$7;
        this.pc = 176;
        continue contLoop;
      } else if (this.pc === 176) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = ansi1.moveTo([
          1,
          23
        ], lambda7);
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 174;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 174;
        continue contLoop;
      } else if (this.pc === 174) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$10);
        this.pc = 175;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$7 = function Cont$func$lambda$$$(y$0, tmp$1, curDepth$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$16.class(pc);
  return tmp(y$0, tmp$1, curDepth$2, stackDelayRes$3)
};
Cont$func$lambda$$$ctor7 = function Cont$func$lambda$$$ctor(y$0, tmp$1, curDepth$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$16.class(pc);
    return tmp(y$0, tmp$1, curDepth$2, stackDelayRes$3)
  }
};
Cont$func$lambda$$16 = function Cont$func$lambda$$(pc1) {
  return (y$01, tmp$11, curDepth$21, stackDelayRes$31) => {
    return new Cont$func$lambda$$.class(pc1)(y$01, tmp$11, curDepth$21, stackDelayRes$31);
  }
};
Cont$func$lambda$$16.class = class Cont$func$lambda$$3 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (y$0, tmp$1, curDepth$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.y$0 = y$0;
      this.tmp$1 = tmp$1;
      this.curDepth$2 = curDepth$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 168) {
      this.stackDelayRes$3 = value$;
    } else if (this.pc === 169) {
      this.tmp$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 168) {
        this.pc = 173;
        continue contLoop;
      } else if (this.pc === 172) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.writeString(this.tmp$1, lambda8, this.y$0)
      } else if (this.pc === 173) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = NofibPrelude.nofibStringToList("I'm waiting...");
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 169;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 169;
        continue contLoop;
      } else if (this.pc === 169) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$2);
        this.pc = 172;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$6 = function Cont$func$lambda$$$(x$0, stackDelayRes$1, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$15.class(pc);
  return tmp(x$0, stackDelayRes$1)
};
Cont$func$lambda$$$ctor6 = function Cont$func$lambda$$$ctor(x$0, stackDelayRes$1) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$15.class(pc);
    return tmp(x$0, stackDelayRes$1)
  }
};
Cont$func$lambda$$15 = function Cont$func$lambda$$(pc1) {
  return (x$01, stackDelayRes$11) => {
    return new Cont$func$lambda$$.class(pc1)(x$01, stackDelayRes$11);
  }
};
Cont$func$lambda$$15.class = class Cont$func$lambda$$4 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, stackDelayRes$1) => {
      let tmp;
      tmp = super(null);
      this.x$0 = x$0;
      this.stackDelayRes$1 = stackDelayRes$1;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 170) {
      this.stackDelayRes$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 170) {
        this.pc = 171;
        continue contLoop;
      } else if (this.pc === 171) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.pressAnyKey(ansi1.end, this.x$0)
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda8 = (undefined, function (x) {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$6(x, stackDelayRes, 170);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return ansi1.pressAnyKey(ansi1.end, x)
});
lambda7 = (undefined, function (y) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$7(y, tmp, curDepth, stackDelayRes, 168);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = NofibPrelude.nofibStringToList("I'm waiting...");
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$7(y, tmp, curDepth, stackDelayRes, 169);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return ansi1.writeString(tmp, lambda8, y)
});
lambda6 = (undefined, function (name) {
  let reply, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$8(name, reply, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 162);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = NofibPrelude.nofibStringToList("Hello ");
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$8(name, reply, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 163);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = NofibPrelude.nofibStringToList("!");
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$lambda$$$8(name, reply, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 164);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp2 = NofibPrelude.append(name, tmp1);
  if (tmp2 instanceof runtime.EffectSig.class) {
    tmp2.contTrace.last.next = Cont$func$lambda$$$8(name, reply, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 165);
    tmp2.contTrace.last = tmp2.contTrace.last.next;
    return tmp2
  }
  tmp2 = runtime.resetDepth(tmp2, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp3 = NofibPrelude.append(tmp, tmp2);
  if (tmp3 instanceof runtime.EffectSig.class) {
    tmp3.contTrace.last.next = Cont$func$lambda$$$8(name, reply, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 166);
    tmp3.contTrace.last = tmp3.contTrace.last.next;
    return tmp3
  }
  tmp3 = runtime.resetDepth(tmp3, curDepth);
  reply = tmp3;
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp4 = NofibPrelude.listLen(reply);
  if (tmp4 instanceof runtime.EffectSig.class) {
    tmp4.contTrace.last.next = Cont$func$lambda$$$8(name, reply, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 167);
    tmp4.contTrace.last = tmp4.contTrace.last.next;
    return tmp4
  }
  tmp4 = runtime.resetDepth(tmp4, curDepth);
  tmp5 = tmp4 / 2;
  tmp6 = 40 - tmp5;
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp7 = ansi1.moveTo([
    1,
    23
  ], lambda7);
  if (tmp7 instanceof runtime.EffectSig.class) {
    tmp7.contTrace.last.next = Cont$func$lambda$$$8(name, reply, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, curDepth, stackDelayRes, 174);
    tmp7.contTrace.last = tmp7.contTrace.last.next;
    return tmp7
  }
  tmp7 = runtime.resetDepth(tmp7, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return ansi1.writeAt([
    tmp6,
    18
  ], reply, tmp7)
});
lambda5 = (undefined, function (x) {
  let tmp, tmp1, tmp2, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$9(x, tmp, tmp1, tmp2, curDepth, stackDelayRes, 160);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = NofibPrelude.nofibStringToList("Please enter your name: ");
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$9(x, tmp, tmp1, tmp2, curDepth, stackDelayRes, 161);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  tmp1 = lambda6;
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp2 = ansi1.promptReadAt([
    17,
    15
  ], 18, tmp, tmp1);
  if (tmp2 instanceof runtime.EffectSig.class) {
    tmp2.contTrace.last.next = Cont$func$lambda$$$9(x, tmp, tmp1, tmp2, curDepth, stackDelayRes, 182);
    tmp2.contTrace.last = tmp2.contTrace.last.next;
    return tmp2
  }
  tmp2 = runtime.resetDepth(tmp2, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return ansi1.pressAnyKey(tmp2, x)
});
Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$$ = function Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$$(x_y$0, l$1, prompt$2, consume$3, first1$4, first0$5, x$6, y$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13, pc) {
  let tmp;
  tmp = new Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$1.class(pc);
  return tmp(x_y$0, l$1, prompt$2, consume$3, first1$4, first0$5, x$6, y$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13)
};
Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$$ctor = function Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$$ctor(x_y$0, l$1, prompt$2, consume$3, first1$4, first0$5, x$6, y$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$1.class(pc);
    return tmp(x_y$0, l$1, prompt$2, consume$3, first1$4, first0$5, x$6, y$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13)
  }
};
Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$1 = function Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$(pc1) {
  return (x_y$01, l$11, prompt$21, consume$31, first1$41, first0$51, x$61, y$71, tmp$81, tmp$91, tmp$101, curDepth$111, tmp$121, stackDelayRes$131) => {
    return new Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$.class(pc1)(x_y$01, l$11, prompt$21, consume$31, first1$41, first0$51, x$61, y$71, tmp$81, tmp$91, tmp$101, curDepth$111, tmp$121, stackDelayRes$131);
  }
};
Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$1.class = class Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x_y$0, l$1, prompt$2, consume$3, first1$4, first0$5, x$6, y$7, tmp$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13) => {
      let tmp;
      tmp = super(null);
      this.x_y$0 = x_y$0;
      this.l$1 = l$1;
      this.prompt$2 = prompt$2;
      this.consume$3 = consume$3;
      this.first1$4 = first1$4;
      this.first0$5 = first0$5;
      this.x$6 = x$6;
      this.y$7 = y$7;
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
    if (this.pc === 131) {
      this.stackDelayRes$13 = value$;
    } else if (this.pc === 134) {
      this.tmp$12 = value$;
    } else if (this.pc === 132) {
      this.tmp$8 = value$;
    } else if (this.pc === 133) {
      this.tmp$10 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 131) {
        if (globalThis.Array.isArray(this.x_y$0) && this.x_y$0.length === 2) {
          this.first0$5 = this.x_y$0[0];
          this.first1$4 = this.x_y$0[1];
          this.x$6 = this.first0$5;
          this.y$7 = this.first1$4;
          this.pc = 138;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$12 = new globalThis.Error("match error");
          if (this.tmp$12 instanceof runtime.EffectSig.class) {
            this.pc = 134;
            this.tmp$12.contTrace.last.next = this;
            this.tmp$12.contTrace.last = this;
            return this.tmp$12
          }
          this.pc = 134;
          continue contLoop;
        }
        this.pc = 135;
        continue contLoop;
      } else if (this.pc === 135) {
        break contLoop;
      } else if (this.pc === 134) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$11);
        throw this.tmp$12;
      } else if (this.pc === 136) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.writeAt([
          this.x$6,
          this.y$7
        ], this.prompt$2, this.tmp$10)
      } else if (this.pc === 137) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$10 = ansi1.readAt([
          this.tmp$9,
          this.y$7
        ], this.l$1, this.consume$3);
        if (this.tmp$10 instanceof runtime.EffectSig.class) {
          this.pc = 133;
          this.tmp$10.contTrace.last.next = this;
          this.tmp$10.contTrace.last = this;
          return this.tmp$10
        }
        this.pc = 133;
        continue contLoop;
      } else if (this.pc === 138) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = NofibPrelude.listLen(this.prompt$2);
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 132;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 132;
        continue contLoop;
      } else if (this.pc === 132) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$11);
        this.tmp$9 = this.x$6 + this.tmp$8;
        this.pc = 137;
        continue contLoop;
      } else if (this.pc === 133) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$11);
        this.pc = 136;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$readAt$ansi$_mls_L0_2058_2153$$ = function Cont$func$readAt$ansi$_mls_L0_2058_2153$$(x_y$0, l$1, consume$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7, pc) {
  let tmp;
  tmp = new Cont$func$readAt$ansi$_mls_L0_2058_2153$1.class(pc);
  return tmp(x_y$0, l$1, consume$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7)
};
Cont$func$readAt$ansi$_mls_L0_2058_2153$$ctor = function Cont$func$readAt$ansi$_mls_L0_2058_2153$$ctor(x_y$0, l$1, consume$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$readAt$ansi$_mls_L0_2058_2153$1.class(pc);
    return tmp(x_y$0, l$1, consume$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7)
  }
};
Cont$func$readAt$ansi$_mls_L0_2058_2153$1 = function Cont$func$readAt$ansi$_mls_L0_2058_2153$(pc1) {
  return (x_y$01, l$11, consume$21, tmp$31, tmp$41, tmp$51, curDepth$61, stackDelayRes$71) => {
    return new Cont$func$readAt$ansi$_mls_L0_2058_2153$.class(pc1)(x_y$01, l$11, consume$21, tmp$31, tmp$41, tmp$51, curDepth$61, stackDelayRes$71);
  }
};
Cont$func$readAt$ansi$_mls_L0_2058_2153$1.class = class Cont$func$readAt$ansi$_mls_L0_2058_2153$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x_y$0, l$1, consume$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7) => {
      let tmp;
      tmp = super(null);
      this.x_y$0 = x_y$0;
      this.l$1 = l$1;
      this.consume$2 = consume$2;
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
    if (this.pc === 123) {
      this.stackDelayRes$7 = value$;
    } else if (this.pc === 124) {
      this.tmp$3 = value$;
    } else if (this.pc === 125) {
      this.tmp$4 = value$;
    } else if (this.pc === 126) {
      this.tmp$5 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 123) {
        this.pc = 130;
        continue contLoop;
      } else if (this.pc === 127) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.writeAt(this.x_y$0, this.tmp$3, this.tmp$5)
      } else if (this.pc === 130) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = NofibPrelude.replicate(this.l$1, "_");
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 124;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 124;
        continue contLoop;
      } else if (this.pc === 124) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$6);
        this.pc = 129;
        continue contLoop;
      } else if (this.pc === 128) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = ansi1.moveTo(this.x_y$0, this.tmp$4);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 126;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 126;
        continue contLoop;
      } else if (this.pc === 129) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$4 = ansi1.loop(0, "", this.l$1, this.consume$2);
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 125;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 125;
        continue contLoop;
      } else if (this.pc === 125) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$6);
        this.pc = 128;
        continue contLoop;
      } else if (this.pc === 126) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$6);
        this.pc = 127;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$readAt$ansi$_mls_L0_2058_2153$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$5 = function Cont$func$lambda$$$(n$0, s$1, l$2, consume$3, x$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$14.class(pc);
  return tmp(n$0, s$1, l$2, consume$3, x$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8)
};
Cont$func$lambda$$$ctor5 = function Cont$func$lambda$$$ctor(n$0, s$1, l$2, consume$3, x$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$14.class(pc);
    return tmp(n$0, s$1, l$2, consume$3, x$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8)
  }
};
Cont$func$lambda$$14 = function Cont$func$lambda$$(pc1) {
  return (n$01, s$11, l$21, consume$31, x$41, tmp$51, tmp$61, curDepth$71, stackDelayRes$81) => {
    return new Cont$func$lambda$$.class(pc1)(n$01, s$11, l$21, consume$31, x$41, tmp$51, tmp$61, curDepth$71, stackDelayRes$81);
  }
};
Cont$func$lambda$$14.class = class Cont$func$lambda$$5 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (n$0, s$1, l$2, consume$3, x$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8) => {
      let tmp;
      tmp = super(null);
      this.n$0 = n$0;
      this.s$1 = s$1;
      this.l$2 = l$2;
      this.consume$3 = consume$3;
      this.x$4 = x$4;
      this.tmp$5 = tmp$5;
      this.tmp$6 = tmp$6;
      this.curDepth$7 = curDepth$7;
      this.stackDelayRes$8 = stackDelayRes$8;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 106) {
      this.stackDelayRes$8 = value$;
    } else if (this.pc === 107) {
      this.tmp$5 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 106) {
        this.pc = 122;
        continue contLoop;
      } else if (this.pc === 121) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.readChar(this.tmp$5, this.tmp$6, this.x$4)
      } else if (this.pc === 122) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = ansi1.returnn(this.s$1, this.consume$3);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 107;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 107;
        continue contLoop;
      } else if (this.pc === 107) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$7);
        this.tmp$6 = runtime.safeCall(lambda4(this.n$0, this.s$1, this.l$2, this.consume$3));
        this.pc = 121;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$4 = function Cont$func$lambda$$$(n$0, s$1, l$2, consume$3, c$4, d$5, scrut$6, scrut$7, scrut$8, scrut$9, tmp$10, tmp$11, tmp$12, tmp$13, curDepth$14, stackDelayRes$15, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$13.class(pc);
  return tmp(n$0, s$1, l$2, consume$3, c$4, d$5, scrut$6, scrut$7, scrut$8, scrut$9, tmp$10, tmp$11, tmp$12, tmp$13, curDepth$14, stackDelayRes$15)
};
Cont$func$lambda$$$ctor4 = function Cont$func$lambda$$$ctor(n$0, s$1, l$2, consume$3, c$4, d$5, scrut$6, scrut$7, scrut$8, scrut$9, tmp$10, tmp$11, tmp$12, tmp$13, curDepth$14, stackDelayRes$15) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$13.class(pc);
    return tmp(n$0, s$1, l$2, consume$3, c$4, d$5, scrut$6, scrut$7, scrut$8, scrut$9, tmp$10, tmp$11, tmp$12, tmp$13, curDepth$14, stackDelayRes$15)
  }
};
Cont$func$lambda$$13 = function Cont$func$lambda$$(pc1) {
  return (n$01, s$11, l$21, consume$31, c$41, d$51, scrut$61, scrut$71, scrut$81, scrut$91, tmp$101, tmp$111, tmp$121, tmp$131, curDepth$141, stackDelayRes$151) => {
    return new Cont$func$lambda$$.class(pc1)(n$01, s$11, l$21, consume$31, c$41, d$51, scrut$61, scrut$71, scrut$81, scrut$91, tmp$101, tmp$111, tmp$121, tmp$131, curDepth$141, stackDelayRes$151);
  }
};
Cont$func$lambda$$13.class = class Cont$func$lambda$$6 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (n$0, s$1, l$2, consume$3, c$4, d$5, scrut$6, scrut$7, scrut$8, scrut$9, tmp$10, tmp$11, tmp$12, tmp$13, curDepth$14, stackDelayRes$15) => {
      let tmp;
      tmp = super(null);
      this.n$0 = n$0;
      this.s$1 = s$1;
      this.l$2 = l$2;
      this.consume$3 = consume$3;
      this.c$4 = c$4;
      this.d$5 = d$5;
      this.scrut$6 = scrut$6;
      this.scrut$7 = scrut$7;
      this.scrut$8 = scrut$8;
      this.scrut$9 = scrut$9;
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
    if (this.pc === 108) {
      this.stackDelayRes$15 = value$;
    } else if (this.pc === 111) {
      this.tmp$13 = value$;
    } else if (this.pc === 109) {
      this.tmp$11 = value$;
    } else if (this.pc === 110) {
      this.tmp$12 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 108) {
        this.scrut$9 = this.c$4 == "B";
        if (this.scrut$9 === true) {
          this.pc = 113;
          continue contLoop;
        } else {
          this.scrut$8 = this.c$4 == "D";
          if (this.scrut$8 === true) {
            this.pc = 114;
            continue contLoop;
          } else {
            this.scrut$7 = this.c$4 == "`";
            if (this.scrut$7 === true) {
              this.pc = 115;
              continue contLoop;
            } else {
              this.scrut$6 = this.n$0 < this.l$2;
              if (this.scrut$6 === true) {
                this.tmp$10 = this.n$0 + 1;
                this.pc = 118;
                continue contLoop;
              } else {
                this.pc = 120;
                continue contLoop;
              }
              this.pc = 112;
              continue contLoop;
            }
            this.pc = 112;
            continue contLoop;
          }
          this.pc = 112;
          continue contLoop;
        }
        this.pc = 112;
        continue contLoop;
      } else if (this.pc === 112) {
        break contLoop;
      } else if (this.pc === 119) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.ringBell(this.tmp$13, this.d$5)
      } else if (this.pc === 120) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$13 = ansi1.loop(this.n$0, this.s$1, this.l$2, this.consume$3);
        if (this.tmp$13 instanceof runtime.EffectSig.class) {
          this.pc = 111;
          this.tmp$13.contTrace.last.next = this;
          this.tmp$13.contTrace.last = this;
          return this.tmp$13
        }
        this.pc = 111;
        continue contLoop;
      } else if (this.pc === 111) {
        this.tmp$13 = runtime.resetDepth(this.tmp$13, this.curDepth$14);
        this.pc = 119;
        continue contLoop;
      } else if (this.pc === 116) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.writeChar(this.c$4, this.tmp$12, this.d$5)
      } else if (this.pc === 117) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$12 = ansi1.loop(this.tmp$10, this.tmp$11, this.l$2, this.consume$3);
        if (this.tmp$12 instanceof runtime.EffectSig.class) {
          this.pc = 110;
          this.tmp$12.contTrace.last.next = this;
          this.tmp$12.contTrace.last = this;
          return this.tmp$12
        }
        this.pc = 110;
        continue contLoop;
      } else if (this.pc === 118) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$11 = NofibPrelude.Cons(this.c$4, this.s$1);
        if (this.tmp$11 instanceof runtime.EffectSig.class) {
          this.pc = 109;
          this.tmp$11.contTrace.last.next = this;
          this.tmp$11.contTrace.last = this;
          return this.tmp$11
        }
        this.pc = 109;
        continue contLoop;
      } else if (this.pc === 109) {
        this.tmp$11 = runtime.resetDepth(this.tmp$11, this.curDepth$14);
        this.pc = 117;
        continue contLoop;
      } else if (this.pc === 110) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$14);
        this.pc = 116;
        continue contLoop;
      } else if (this.pc === 115) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.returnn(this.s$1, this.consume$3)
      } else if (this.pc === 114) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.deletee(this.n$0, this.s$1, this.l$2, this.consume$3)
      } else if (this.pc === 113) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.deletee(this.n$0, this.s$1, this.l$2, this.consume$3)
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda$4 = function lambda$(n, s, l, consume, c, d) {
  let scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$4(n, s, l, consume, c, d, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 108);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  scrut3 = c == "B";
  if (scrut3 === true) {
    runtime.stackDepth = runtime.stackDepth + 1;
    return ansi1.deletee(n, s, l, consume)
  } else {
    scrut2 = c == "D";
    if (scrut2 === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      return ansi1.deletee(n, s, l, consume)
    } else {
      scrut1 = c == "`";
      if (scrut1 === true) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.returnn(s, consume)
      } else {
        scrut = n < l;
        if (scrut === true) {
          tmp = n + 1;
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp1 = NofibPrelude.Cons(c, s);
          if (tmp1 instanceof runtime.EffectSig.class) {
            tmp1.contTrace.last.next = Cont$func$lambda$$$4(n, s, l, consume, c, d, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 109);
            tmp1.contTrace.last = tmp1.contTrace.last.next;
            return tmp1
          }
          tmp1 = runtime.resetDepth(tmp1, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp2 = ansi1.loop(tmp, tmp1, l, consume);
          if (tmp2 instanceof runtime.EffectSig.class) {
            tmp2.contTrace.last.next = Cont$func$lambda$$$4(n, s, l, consume, c, d, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 110);
            tmp2.contTrace.last = tmp2.contTrace.last.next;
            return tmp2
          }
          tmp2 = runtime.resetDepth(tmp2, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          return ansi1.writeChar(c, tmp2, d)
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp3 = ansi1.loop(n, s, l, consume);
          if (tmp3 instanceof runtime.EffectSig.class) {
            tmp3.contTrace.last.next = Cont$func$lambda$$$4(n, s, l, consume, c, d, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 111);
            tmp3.contTrace.last = tmp3.contTrace.last.next;
            return tmp3
          }
          tmp3 = runtime.resetDepth(tmp3, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          return ansi1.ringBell(tmp3, d)
        }
      }
    }
  }
};
lambda4 = (undefined, function (n, s, l, consume) {
  return (c, d) => {
    return lambda$4(n, s, l, consume, c, d)
  }
});
lambda$3 = function lambda$(n, s, l, consume, x) {
  let tmp, tmp1, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$5(n, s, l, consume, x, tmp, tmp1, curDepth, stackDelayRes, 106);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = ansi1.returnn(s, consume);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$5(n, s, l, consume, x, tmp, tmp1, curDepth, stackDelayRes, 107);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  tmp1 = runtime.safeCall(lambda4(n, s, l, consume));
  runtime.stackDepth = runtime.stackDepth + 1;
  return ansi1.readChar(tmp, tmp1, x)
};
lambda3 = (undefined, function (n, s, l, consume) {
  return (x) => {
    return lambda$3(n, s, l, consume, x)
  }
});
Cont$func$deletee$ansi$_mls_L0_1430_1603$$ = function Cont$func$deletee$ansi$_mls_L0_1430_1603$$(n$0, s$1, l$2, consume$3, scrut$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12, pc) {
  let tmp;
  tmp = new Cont$func$deletee$ansi$_mls_L0_1430_1603$1.class(pc);
  return tmp(n$0, s$1, l$2, consume$3, scrut$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12)
};
Cont$func$deletee$ansi$_mls_L0_1430_1603$$ctor = function Cont$func$deletee$ansi$_mls_L0_1430_1603$$ctor(n$0, s$1, l$2, consume$3, scrut$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$deletee$ansi$_mls_L0_1430_1603$1.class(pc);
    return tmp(n$0, s$1, l$2, consume$3, scrut$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12)
  }
};
Cont$func$deletee$ansi$_mls_L0_1430_1603$1 = function Cont$func$deletee$ansi$_mls_L0_1430_1603$(pc1) {
  return (n$01, s$11, l$21, consume$31, scrut$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, curDepth$111, stackDelayRes$121) => {
    return new Cont$func$deletee$ansi$_mls_L0_1430_1603$.class(pc1)(n$01, s$11, l$21, consume$31, scrut$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, curDepth$111, stackDelayRes$121);
  }
};
Cont$func$deletee$ansi$_mls_L0_1430_1603$1.class = class Cont$func$deletee$ansi$_mls_L0_1430_1603$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (n$0, s$1, l$2, consume$3, scrut$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12) => {
      let tmp;
      tmp = super(null);
      this.n$0 = n$0;
      this.s$1 = s$1;
      this.l$2 = l$2;
      this.consume$3 = consume$3;
      this.scrut$4 = scrut$4;
      this.tmp$5 = tmp$5;
      this.tmp$6 = tmp$6;
      this.tmp$7 = tmp$7;
      this.tmp$8 = tmp$8;
      this.tmp$9 = tmp$9;
      this.tmp$10 = tmp$10;
      this.curDepth$11 = curDepth$11;
      this.stackDelayRes$12 = stackDelayRes$12;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 92) {
      this.stackDelayRes$12 = value$;
    } else if (this.pc === 96) {
      this.tmp$9 = value$;
    } else if (this.pc === 97) {
      this.tmp$10 = value$;
    } else if (this.pc === 93) {
      this.tmp$5 = value$;
    } else if (this.pc === 94) {
      this.tmp$7 = value$;
    } else if (this.pc === 95) {
      this.tmp$8 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 92) {
        this.scrut$4 = this.n$0 > 0;
        if (this.scrut$4 === true) {
          this.pc = 102;
          continue contLoop;
        } else {
          this.pc = 105;
          continue contLoop;
        }
        this.pc = 98;
        continue contLoop;
      } else if (this.pc === 98) {
        break contLoop;
      } else if (this.pc === 103) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.ringBell(this.tmp$10)
      } else if (this.pc === 104) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$10 = ansi1.loop(0, this.tmp$9, this.l$2, this.consume$3);
        if (this.tmp$10 instanceof runtime.EffectSig.class) {
          this.pc = 97;
          this.tmp$10.contTrace.last.next = this;
          this.tmp$10.contTrace.last = this;
          return this.tmp$10
        }
        this.pc = 97;
        continue contLoop;
      } else if (this.pc === 105) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = NofibPrelude.nofibStringToList("");
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 96;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 96;
        continue contLoop;
      } else if (this.pc === 96) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$11);
        this.pc = 104;
        continue contLoop;
      } else if (this.pc === 97) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$11);
        this.pc = 103;
        continue contLoop;
      } else if (this.pc === 99) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.writeString(this.tmp$5, this.tmp$8)
      } else if (this.pc === 102) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = NofibPrelude.nofibStringToList("BS_BS");
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 93;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 93;
        continue contLoop;
      } else if (this.pc === 93) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$11);
        this.tmp$6 = this.n$0 - 1;
        this.pc = 101;
        continue contLoop;
      } else if (this.pc === 100) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = ansi1.loop(this.tmp$6, this.tmp$7, this.l$2, this.consume$3);
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 95;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 95;
        continue contLoop;
      } else if (this.pc === 101) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = NofibPrelude.tail(this.s$1);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 94;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 94;
        continue contLoop;
      } else if (this.pc === 94) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$11);
        this.pc = 100;
        continue contLoop;
      } else if (this.pc === 95) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$11);
        this.pc = 99;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$deletee$ansi$_mls_L0_1430_1603$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$returnn$ansi$_mls_L0_1290_1331$$ = function Cont$func$returnn$ansi$_mls_L0_1290_1331$$(s$0, consume$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$returnn$ansi$_mls_L0_1290_1331$1.class(pc);
  return tmp(s$0, consume$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$returnn$ansi$_mls_L0_1290_1331$$ctor = function Cont$func$returnn$ansi$_mls_L0_1290_1331$$ctor(s$0, consume$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$returnn$ansi$_mls_L0_1290_1331$1.class(pc);
    return tmp(s$0, consume$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$returnn$ansi$_mls_L0_1290_1331$1 = function Cont$func$returnn$ansi$_mls_L0_1290_1331$(pc1) {
  return (s$01, consume$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$returnn$ansi$_mls_L0_1290_1331$.class(pc1)(s$01, consume$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$returnn$ansi$_mls_L0_1290_1331$1.class = class Cont$func$returnn$ansi$_mls_L0_1290_1331$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (s$0, consume$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.s$0 = s$0;
      this.consume$1 = consume$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 88) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 89) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 88) {
        this.pc = 91;
        continue contLoop;
      } else if (this.pc === 90) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.consume$1(this.tmp$2))
      } else if (this.pc === 91) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = NofibPrelude.reverse(this.s$0);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 89;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 89;
        continue contLoop;
      } else if (this.pc === 89) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        this.pc = 90;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$returnn$ansi$_mls_L0_1290_1331$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$moveTo$ansi$_mls_L0_1211_1284$$ = function Cont$func$moveTo$ansi$_mls_L0_1211_1284$$(x_y$0, a$1, first1$2, first0$3, x$4, y$5, tmp$6, curDepth$7, stackDelayRes$8, pc) {
  let tmp;
  tmp = new Cont$func$moveTo$ansi$_mls_L0_1211_1284$1.class(pc);
  return tmp(x_y$0, a$1, first1$2, first0$3, x$4, y$5, tmp$6, curDepth$7, stackDelayRes$8)
};
Cont$func$moveTo$ansi$_mls_L0_1211_1284$$ctor = function Cont$func$moveTo$ansi$_mls_L0_1211_1284$$ctor(x_y$0, a$1, first1$2, first0$3, x$4, y$5, tmp$6, curDepth$7, stackDelayRes$8) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$moveTo$ansi$_mls_L0_1211_1284$1.class(pc);
    return tmp(x_y$0, a$1, first1$2, first0$3, x$4, y$5, tmp$6, curDepth$7, stackDelayRes$8)
  }
};
Cont$func$moveTo$ansi$_mls_L0_1211_1284$1 = function Cont$func$moveTo$ansi$_mls_L0_1211_1284$(pc1) {
  return (x_y$01, a$11, first1$21, first0$31, x$41, y$51, tmp$61, curDepth$71, stackDelayRes$81) => {
    return new Cont$func$moveTo$ansi$_mls_L0_1211_1284$.class(pc1)(x_y$01, a$11, first1$21, first0$31, x$41, y$51, tmp$61, curDepth$71, stackDelayRes$81);
  }
};
Cont$func$moveTo$ansi$_mls_L0_1211_1284$1.class = class Cont$func$moveTo$ansi$_mls_L0_1211_1284$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x_y$0, a$1, first1$2, first0$3, x$4, y$5, tmp$6, curDepth$7, stackDelayRes$8) => {
      let tmp;
      tmp = super(null);
      this.x_y$0 = x_y$0;
      this.a$1 = a$1;
      this.first1$2 = first1$2;
      this.first0$3 = first0$3;
      this.x$4 = x$4;
      this.y$5 = y$5;
      this.tmp$6 = tmp$6;
      this.curDepth$7 = curDepth$7;
      this.stackDelayRes$8 = stackDelayRes$8;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 81) {
      this.stackDelayRes$8 = value$;
    } else if (this.pc === 86) {
      this.tmp$6 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 81) {
        if (globalThis.Array.isArray(this.x_y$0) && this.x_y$0.length === 2) {
          this.first0$3 = this.x_y$0[0];
          this.first1$2 = this.x_y$0[1];
          this.x$4 = this.first0$3;
          this.y$5 = this.first1$2;
          return runtime.safeCall(lambda2(this.a$1, this.x$4, this.y$5))
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$6 = new globalThis.Error("match error");
          if (this.tmp$6 instanceof runtime.EffectSig.class) {
            this.pc = 86;
            this.tmp$6.contTrace.last.next = this;
            this.tmp$6.contTrace.last = this;
            return this.tmp$6
          }
          this.pc = 86;
          continue contLoop;
        }
        this.pc = 87;
        continue contLoop;
      } else if (this.pc === 87) {
        break contLoop;
      } else if (this.pc === 86) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$7);
        throw this.tmp$6;
      }
      break;
    }
  }
  toString() { return "Cont$func$moveTo$ansi$_mls_L0_1211_1284$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$3 = function Cont$func$lambda$$$(a$0, x$1, y$2, p$3, tmp$4, curDepth$5, stackDelayRes$6, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$12.class(pc);
  return tmp(a$0, x$1, y$2, p$3, tmp$4, curDepth$5, stackDelayRes$6)
};
Cont$func$lambda$$$ctor3 = function Cont$func$lambda$$$ctor(a$0, x$1, y$2, p$3, tmp$4, curDepth$5, stackDelayRes$6) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$12.class(pc);
    return tmp(a$0, x$1, y$2, p$3, tmp$4, curDepth$5, stackDelayRes$6)
  }
};
Cont$func$lambda$$12 = function Cont$func$lambda$$(pc1) {
  return (a$01, x$11, y$21, p$31, tmp$41, curDepth$51, stackDelayRes$61) => {
    return new Cont$func$lambda$$.class(pc1)(a$01, x$11, y$21, p$31, tmp$41, curDepth$51, stackDelayRes$61);
  }
};
Cont$func$lambda$$12.class = class Cont$func$lambda$$7 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (a$0, x$1, y$2, p$3, tmp$4, curDepth$5, stackDelayRes$6) => {
      let tmp;
      tmp = super(null);
      this.a$0 = a$0;
      this.x$1 = x$1;
      this.y$2 = y$2;
      this.p$3 = p$3;
      this.tmp$4 = tmp$4;
      this.curDepth$5 = curDepth$5;
      this.stackDelayRes$6 = stackDelayRes$6;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 82) {
      this.stackDelayRes$6 = value$;
    } else if (this.pc === 83) {
      this.tmp$4 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 82) {
        this.pc = 85;
        continue contLoop;
      } else if (this.pc === 84) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.writeString(this.tmp$4, this.a$0, this.p$3)
      } else if (this.pc === 85) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$4 = ansi1.goto(this.x$1, this.y$2);
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 83;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 83;
        continue contLoop;
      } else if (this.pc === 83) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$5);
        this.pc = 84;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda$2 = function lambda$(a, x, y, p) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$3(a, x, y, p, tmp, curDepth, stackDelayRes, 82);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = ansi1.goto(x, y);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$3(a, x, y, p, tmp, curDepth, stackDelayRes, 83);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return ansi1.writeString(tmp, a, p)
};
lambda2 = (undefined, function (a, x, y) {
  return (p) => {
    return lambda$2(a, x, y, p)
  }
});
Cont$func$writeAt$ansi$_mls_L0_1123_1205$$ = function Cont$func$writeAt$ansi$_mls_L0_1123_1205$$(x_y$0, s$1, a$2, first1$3, first0$4, x$5, y$6, tmp$7, curDepth$8, stackDelayRes$9, pc) {
  let tmp;
  tmp = new Cont$func$writeAt$ansi$_mls_L0_1123_1205$1.class(pc);
  return tmp(x_y$0, s$1, a$2, first1$3, first0$4, x$5, y$6, tmp$7, curDepth$8, stackDelayRes$9)
};
Cont$func$writeAt$ansi$_mls_L0_1123_1205$$ctor = function Cont$func$writeAt$ansi$_mls_L0_1123_1205$$ctor(x_y$0, s$1, a$2, first1$3, first0$4, x$5, y$6, tmp$7, curDepth$8, stackDelayRes$9) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$writeAt$ansi$_mls_L0_1123_1205$1.class(pc);
    return tmp(x_y$0, s$1, a$2, first1$3, first0$4, x$5, y$6, tmp$7, curDepth$8, stackDelayRes$9)
  }
};
Cont$func$writeAt$ansi$_mls_L0_1123_1205$1 = function Cont$func$writeAt$ansi$_mls_L0_1123_1205$(pc1) {
  return (x_y$01, s$11, a$21, first1$31, first0$41, x$51, y$61, tmp$71, curDepth$81, stackDelayRes$91) => {
    return new Cont$func$writeAt$ansi$_mls_L0_1123_1205$.class(pc1)(x_y$01, s$11, a$21, first1$31, first0$41, x$51, y$61, tmp$71, curDepth$81, stackDelayRes$91);
  }
};
Cont$func$writeAt$ansi$_mls_L0_1123_1205$1.class = class Cont$func$writeAt$ansi$_mls_L0_1123_1205$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x_y$0, s$1, a$2, first1$3, first0$4, x$5, y$6, tmp$7, curDepth$8, stackDelayRes$9) => {
      let tmp;
      tmp = super(null);
      this.x_y$0 = x_y$0;
      this.s$1 = s$1;
      this.a$2 = a$2;
      this.first1$3 = first1$3;
      this.first0$4 = first0$4;
      this.x$5 = x$5;
      this.y$6 = y$6;
      this.tmp$7 = tmp$7;
      this.curDepth$8 = curDepth$8;
      this.stackDelayRes$9 = stackDelayRes$9;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 72) {
      this.stackDelayRes$9 = value$;
    } else if (this.pc === 79) {
      this.tmp$7 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 72) {
        if (globalThis.Array.isArray(this.x_y$0) && this.x_y$0.length === 2) {
          this.first0$4 = this.x_y$0[0];
          this.first1$3 = this.x_y$0[1];
          this.x$5 = this.first0$4;
          this.y$6 = this.first1$3;
          return runtime.safeCall(lambda1(this.s$1, this.a$2, this.x$5, this.y$6))
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$7 = new globalThis.Error("match error");
          if (this.tmp$7 instanceof runtime.EffectSig.class) {
            this.pc = 79;
            this.tmp$7.contTrace.last.next = this;
            this.tmp$7.contTrace.last = this;
            return this.tmp$7
          }
          this.pc = 79;
          continue contLoop;
        }
        this.pc = 80;
        continue contLoop;
      } else if (this.pc === 80) {
        break contLoop;
      } else if (this.pc === 79) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$8);
        throw this.tmp$7;
      }
      break;
    }
  }
  toString() { return "Cont$func$writeAt$ansi$_mls_L0_1123_1205$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$2 = function Cont$func$lambda$$$(s$0, a$1, x$2, y$3, p$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$11.class(pc);
  return tmp(s$0, a$1, x$2, y$3, p$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8)
};
Cont$func$lambda$$$ctor2 = function Cont$func$lambda$$$ctor(s$0, a$1, x$2, y$3, p$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$11.class(pc);
    return tmp(s$0, a$1, x$2, y$3, p$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8)
  }
};
Cont$func$lambda$$11 = function Cont$func$lambda$$(pc1) {
  return (s$01, a$11, x$21, y$31, p$41, tmp$51, tmp$61, curDepth$71, stackDelayRes$81) => {
    return new Cont$func$lambda$$.class(pc1)(s$01, a$11, x$21, y$31, p$41, tmp$51, tmp$61, curDepth$71, stackDelayRes$81);
  }
};
Cont$func$lambda$$11.class = class Cont$func$lambda$$8 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (s$0, a$1, x$2, y$3, p$4, tmp$5, tmp$6, curDepth$7, stackDelayRes$8) => {
      let tmp;
      tmp = super(null);
      this.s$0 = s$0;
      this.a$1 = a$1;
      this.x$2 = x$2;
      this.y$3 = y$3;
      this.p$4 = p$4;
      this.tmp$5 = tmp$5;
      this.tmp$6 = tmp$6;
      this.curDepth$7 = curDepth$7;
      this.stackDelayRes$8 = stackDelayRes$8;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 73) {
      this.stackDelayRes$8 = value$;
    } else if (this.pc === 74) {
      this.tmp$5 = value$;
    } else if (this.pc === 75) {
      this.tmp$6 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 73) {
        this.pc = 78;
        continue contLoop;
      } else if (this.pc === 76) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.writeString(this.tmp$6, this.a$1, this.p$4)
      } else if (this.pc === 77) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = NofibPrelude.append(this.tmp$5, this.s$0);
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 75;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 75;
        continue contLoop;
      } else if (this.pc === 78) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = ansi1.goto(this.x$2, this.y$3);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 74;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 74;
        continue contLoop;
      } else if (this.pc === 74) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$7);
        this.pc = 77;
        continue contLoop;
      } else if (this.pc === 75) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$7);
        this.pc = 76;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda$1 = function lambda$(s, a, x, y, p) {
  let tmp, tmp1, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$2(s, a, x, y, p, tmp, tmp1, curDepth, stackDelayRes, 73);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = ansi1.goto(x, y);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$2(s, a, x, y, p, tmp, tmp1, curDepth, stackDelayRes, 74);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = NofibPrelude.append(tmp, s);
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$lambda$$$2(s, a, x, y, p, tmp, tmp1, curDepth, stackDelayRes, 75);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return ansi1.writeString(tmp1, a, p)
};
lambda1 = (undefined, function (s, a, x, y) {
  return (p) => {
    return lambda$1(s, a, x, y, p)
  }
});
Cont$func$clearScreen$ansi$_mls_L0_1075_1117$$ = function Cont$func$clearScreen$ansi$_mls_L0_1075_1117$$(a$0, b$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$clearScreen$ansi$_mls_L0_1075_1117$1.class(pc);
  return tmp(a$0, b$1, stackDelayRes$2)
};
Cont$func$clearScreen$ansi$_mls_L0_1075_1117$$ctor = function Cont$func$clearScreen$ansi$_mls_L0_1075_1117$$ctor(a$0, b$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$clearScreen$ansi$_mls_L0_1075_1117$1.class(pc);
    return tmp(a$0, b$1, stackDelayRes$2)
  }
};
Cont$func$clearScreen$ansi$_mls_L0_1075_1117$1 = function Cont$func$clearScreen$ansi$_mls_L0_1075_1117$(pc1) {
  return (a$01, b$11, stackDelayRes$21) => {
    return new Cont$func$clearScreen$ansi$_mls_L0_1075_1117$.class(pc1)(a$01, b$11, stackDelayRes$21);
  }
};
Cont$func$clearScreen$ansi$_mls_L0_1075_1117$1.class = class Cont$func$clearScreen$ansi$_mls_L0_1075_1117$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (a$0, b$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.a$0 = a$0;
      this.b$1 = b$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 70) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 70) {
        this.pc = 71;
        continue contLoop;
      } else if (this.pc === 71) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.writeString(ansi1.cls, this.a$0, this.b$1)
      }
      break;
    }
  }
  toString() { return "Cont$func$clearScreen$ansi$_mls_L0_1075_1117$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$ringBell$ansi$_mls_L0_1024_1069$$ = function Cont$func$ringBell$ansi$_mls_L0_1024_1069$$(prog$0, cs$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$ringBell$ansi$_mls_L0_1024_1069$1.class(pc);
  return tmp(prog$0, cs$1, stackDelayRes$2)
};
Cont$func$ringBell$ansi$_mls_L0_1024_1069$$ctor = function Cont$func$ringBell$ansi$_mls_L0_1024_1069$$ctor(prog$0, cs$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$ringBell$ansi$_mls_L0_1024_1069$1.class(pc);
    return tmp(prog$0, cs$1, stackDelayRes$2)
  }
};
Cont$func$ringBell$ansi$_mls_L0_1024_1069$1 = function Cont$func$ringBell$ansi$_mls_L0_1024_1069$(pc1) {
  return (prog$01, cs$11, stackDelayRes$21) => {
    return new Cont$func$ringBell$ansi$_mls_L0_1024_1069$.class(pc1)(prog$01, cs$11, stackDelayRes$21);
  }
};
Cont$func$ringBell$ansi$_mls_L0_1024_1069$1.class = class Cont$func$ringBell$ansi$_mls_L0_1024_1069$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (prog$0, cs$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.prog$0 = prog$0;
      this.cs$1 = cs$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 68) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 68) {
        this.pc = 69;
        continue contLoop;
      } else if (this.pc === 69) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.writeChar("B", this.prog$0, this.cs$1)
      }
      break;
    }
  }
  toString() { return "Cont$func$ringBell$ansi$_mls_L0_1024_1069$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$writes$ansi$_mls_L0_970_1018$$ = function Cont$func$writes$ansi$_mls_L0_970_1018$$(ss$0, a$1, b$2, tmp$3, curDepth$4, stackDelayRes$5, pc) {
  let tmp;
  tmp = new Cont$func$writes$ansi$_mls_L0_970_1018$1.class(pc);
  return tmp(ss$0, a$1, b$2, tmp$3, curDepth$4, stackDelayRes$5)
};
Cont$func$writes$ansi$_mls_L0_970_1018$$ctor = function Cont$func$writes$ansi$_mls_L0_970_1018$$ctor(ss$0, a$1, b$2, tmp$3, curDepth$4, stackDelayRes$5) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$writes$ansi$_mls_L0_970_1018$1.class(pc);
    return tmp(ss$0, a$1, b$2, tmp$3, curDepth$4, stackDelayRes$5)
  }
};
Cont$func$writes$ansi$_mls_L0_970_1018$1 = function Cont$func$writes$ansi$_mls_L0_970_1018$(pc1) {
  return (ss$01, a$11, b$21, tmp$31, curDepth$41, stackDelayRes$51) => {
    return new Cont$func$writes$ansi$_mls_L0_970_1018$.class(pc1)(ss$01, a$11, b$21, tmp$31, curDepth$41, stackDelayRes$51);
  }
};
Cont$func$writes$ansi$_mls_L0_970_1018$1.class = class Cont$func$writes$ansi$_mls_L0_970_1018$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (ss$0, a$1, b$2, tmp$3, curDepth$4, stackDelayRes$5) => {
      let tmp;
      tmp = super(null);
      this.ss$0 = ss$0;
      this.a$1 = a$1;
      this.b$2 = b$2;
      this.tmp$3 = tmp$3;
      this.curDepth$4 = curDepth$4;
      this.stackDelayRes$5 = stackDelayRes$5;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 64) {
      this.stackDelayRes$5 = value$;
    } else if (this.pc === 65) {
      this.tmp$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 64) {
        this.pc = 67;
        continue contLoop;
      } else if (this.pc === 66) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return ansi1.writeString(this.tmp$3, this.a$1, this.b$2)
      } else if (this.pc === 67) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = NofibPrelude.concat(this.ss$0);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 65;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 65;
        continue contLoop;
      } else if (this.pc === 65) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$4);
        this.pc = 66;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$writes$ansi$_mls_L0_970_1018$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$writeString$ansi$_mls_L0_924_964$$ = function Cont$func$writeString$ansi$_mls_L0_924_964$$(s$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5, pc) {
  let tmp;
  tmp = new Cont$func$writeString$ansi$_mls_L0_924_964$1.class(pc);
  return tmp(s$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5)
};
Cont$func$writeString$ansi$_mls_L0_924_964$$ctor = function Cont$func$writeString$ansi$_mls_L0_924_964$$ctor(s$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$writeString$ansi$_mls_L0_924_964$1.class(pc);
    return tmp(s$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5)
  }
};
Cont$func$writeString$ansi$_mls_L0_924_964$1 = function Cont$func$writeString$ansi$_mls_L0_924_964$(pc1) {
  return (s$01, prog$11, cs$21, tmp$31, curDepth$41, stackDelayRes$51) => {
    return new Cont$func$writeString$ansi$_mls_L0_924_964$.class(pc1)(s$01, prog$11, cs$21, tmp$31, curDepth$41, stackDelayRes$51);
  }
};
Cont$func$writeString$ansi$_mls_L0_924_964$1.class = class Cont$func$writeString$ansi$_mls_L0_924_964$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (s$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5) => {
      let tmp;
      tmp = super(null);
      this.s$0 = s$0;
      this.prog$1 = prog$1;
      this.cs$2 = cs$2;
      this.tmp$3 = tmp$3;
      this.curDepth$4 = curDepth$4;
      this.stackDelayRes$5 = stackDelayRes$5;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 60) {
      this.stackDelayRes$5 = value$;
    } else if (this.pc === 61) {
      this.tmp$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 60) {
        this.pc = 63;
        continue contLoop;
      } else if (this.pc === 62) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.append(this.s$0, this.tmp$3)
      } else if (this.pc === 63) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = runtime.safeCall(this.prog$1(this.cs$2));
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 61;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 61;
        continue contLoop;
      } else if (this.pc === 61) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$4);
        this.pc = 62;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$writeString$ansi$_mls_L0_924_964$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$writeChar$ansi$_mls_L0_880_918$$ = function Cont$func$writeChar$ansi$_mls_L0_880_918$$(c$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5, pc) {
  let tmp;
  tmp = new Cont$func$writeChar$ansi$_mls_L0_880_918$1.class(pc);
  return tmp(c$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5)
};
Cont$func$writeChar$ansi$_mls_L0_880_918$$ctor = function Cont$func$writeChar$ansi$_mls_L0_880_918$$ctor(c$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$writeChar$ansi$_mls_L0_880_918$1.class(pc);
    return tmp(c$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5)
  }
};
Cont$func$writeChar$ansi$_mls_L0_880_918$1 = function Cont$func$writeChar$ansi$_mls_L0_880_918$(pc1) {
  return (c$01, prog$11, cs$21, tmp$31, curDepth$41, stackDelayRes$51) => {
    return new Cont$func$writeChar$ansi$_mls_L0_880_918$.class(pc1)(c$01, prog$11, cs$21, tmp$31, curDepth$41, stackDelayRes$51);
  }
};
Cont$func$writeChar$ansi$_mls_L0_880_918$1.class = class Cont$func$writeChar$ansi$_mls_L0_880_918$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (c$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5) => {
      let tmp;
      tmp = super(null);
      this.c$0 = c$0;
      this.prog$1 = prog$1;
      this.cs$2 = cs$2;
      this.tmp$3 = tmp$3;
      this.curDepth$4 = curDepth$4;
      this.stackDelayRes$5 = stackDelayRes$5;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 56) {
      this.stackDelayRes$5 = value$;
    } else if (this.pc === 57) {
      this.tmp$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 56) {
        this.pc = 59;
        continue contLoop;
      } else if (this.pc === 58) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.c$0, this.tmp$3)
      } else if (this.pc === 59) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = runtime.safeCall(this.prog$1(this.cs$2));
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 57;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 57;
        continue contLoop;
      } else if (this.pc === 57) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$4);
        this.pc = 58;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$writeChar$ansi$_mls_L0_880_918$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$unreadChar$ansi$_mls_L0_835_874$$ = function Cont$func$unreadChar$ansi$_mls_L0_835_874$$(c$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5, pc) {
  let tmp;
  tmp = new Cont$func$unreadChar$ansi$_mls_L0_835_874$1.class(pc);
  return tmp(c$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5)
};
Cont$func$unreadChar$ansi$_mls_L0_835_874$$ctor = function Cont$func$unreadChar$ansi$_mls_L0_835_874$$ctor(c$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$unreadChar$ansi$_mls_L0_835_874$1.class(pc);
    return tmp(c$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5)
  }
};
Cont$func$unreadChar$ansi$_mls_L0_835_874$1 = function Cont$func$unreadChar$ansi$_mls_L0_835_874$(pc1) {
  return (c$01, prog$11, cs$21, tmp$31, curDepth$41, stackDelayRes$51) => {
    return new Cont$func$unreadChar$ansi$_mls_L0_835_874$.class(pc1)(c$01, prog$11, cs$21, tmp$31, curDepth$41, stackDelayRes$51);
  }
};
Cont$func$unreadChar$ansi$_mls_L0_835_874$1.class = class Cont$func$unreadChar$ansi$_mls_L0_835_874$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (c$0, prog$1, cs$2, tmp$3, curDepth$4, stackDelayRes$5) => {
      let tmp;
      tmp = super(null);
      this.c$0 = c$0;
      this.prog$1 = prog$1;
      this.cs$2 = cs$2;
      this.tmp$3 = tmp$3;
      this.curDepth$4 = curDepth$4;
      this.stackDelayRes$5 = stackDelayRes$5;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 52) {
      this.stackDelayRes$5 = value$;
    } else if (this.pc === 53) {
      this.tmp$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 52) {
        this.pc = 55;
        continue contLoop;
      } else if (this.pc === 54) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.prog$1(this.tmp$3))
      } else if (this.pc === 55) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = NofibPrelude.Cons(this.c$0, this.cs$2);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 53;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 53;
        continue contLoop;
      } else if (this.pc === 53) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$4);
        this.pc = 54;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$unreadChar$ansi$_mls_L0_835_874$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$pressAnyKey$ansi$_mls_L0_770_829$$ = function Cont$func$pressAnyKey$ansi$_mls_L0_770_829$$(prog$0, x$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$pressAnyKey$ansi$_mls_L0_770_829$1.class(pc);
  return tmp(prog$0, x$1, stackDelayRes$2)
};
Cont$func$pressAnyKey$ansi$_mls_L0_770_829$$ctor = function Cont$func$pressAnyKey$ansi$_mls_L0_770_829$$ctor(prog$0, x$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$pressAnyKey$ansi$_mls_L0_770_829$1.class(pc);
    return tmp(prog$0, x$1, stackDelayRes$2)
  }
};
Cont$func$pressAnyKey$ansi$_mls_L0_770_829$1 = function Cont$func$pressAnyKey$ansi$_mls_L0_770_829$(pc1) {
  return (prog$01, x$11, stackDelayRes$21) => {
    return new Cont$func$pressAnyKey$ansi$_mls_L0_770_829$.class(pc1)(prog$01, x$11, stackDelayRes$21);
  }
};
Cont$func$pressAnyKey$ansi$_mls_L0_770_829$1.class = class Cont$func$pressAnyKey$ansi$_mls_L0_770_829$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (prog$0, x$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.prog$0 = prog$0;
      this.x$1 = x$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    let lambda$this;
    if (this.pc === 48) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 48) {
        this.pc = 51;
        continue contLoop;
      } else if (this.pc === 51) {
        runtime.stackDepth = runtime.stackDepth + 1;
        lambda$this = runtime.safeCall(lambda(this.prog$0));
        return ansi1.readChar(this.prog$0, lambda$this, this.x$1)
      }
      break;
    }
  }
  toString() { return "Cont$func$pressAnyKey$ansi$_mls_L0_770_829$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$1 = function Cont$func$lambda$$$(prog$0, x$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$10.class(pc);
  return tmp(prog$0, x$1, stackDelayRes$2)
};
Cont$func$lambda$$$ctor1 = function Cont$func$lambda$$$ctor(prog$0, x$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$10.class(pc);
    return tmp(prog$0, x$1, stackDelayRes$2)
  }
};
Cont$func$lambda$$10 = function Cont$func$lambda$$(pc1) {
  return (prog$01, x$11, stackDelayRes$21) => {
    return new Cont$func$lambda$$.class(pc1)(prog$01, x$11, stackDelayRes$21);
  }
};
Cont$func$lambda$$10.class = class Cont$func$lambda$$9 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (prog$0, x$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.prog$0 = prog$0;
      this.x$1 = x$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 49) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 49) {
        this.pc = 50;
        continue contLoop;
      } else if (this.pc === 50) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.prog$0(this.x$1))
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda$ = function lambda$(prog, c, x) {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$1(prog, x, stackDelayRes, 49);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return runtime.safeCall(prog(x))
};
lambda = (undefined, function (prog) {
  return (c, x) => {
    return lambda$(prog, c, x)
  }
});
Cont$func$peekChar$ansi$_mls_L0_672_764$$ = function Cont$func$peekChar$ansi$_mls_L0_672_764$$(eof$0, consume$1, cs$2, param0$3, param1$4, c$5, cs$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10, pc) {
  let tmp;
  tmp = new Cont$func$peekChar$ansi$_mls_L0_672_764$1.class(pc);
  return tmp(eof$0, consume$1, cs$2, param0$3, param1$4, c$5, cs$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
};
Cont$func$peekChar$ansi$_mls_L0_672_764$$ctor = function Cont$func$peekChar$ansi$_mls_L0_672_764$$ctor(eof$0, consume$1, cs$2, param0$3, param1$4, c$5, cs$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$peekChar$ansi$_mls_L0_672_764$1.class(pc);
    return tmp(eof$0, consume$1, cs$2, param0$3, param1$4, c$5, cs$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
  }
};
Cont$func$peekChar$ansi$_mls_L0_672_764$1 = function Cont$func$peekChar$ansi$_mls_L0_672_764$(pc1) {
  return (eof$01, consume$11, cs$21, param0$31, param1$41, c$51, cs$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101) => {
    return new Cont$func$peekChar$ansi$_mls_L0_672_764$.class(pc1)(eof$01, consume$11, cs$21, param0$31, param1$41, c$51, cs$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101);
  }
};
Cont$func$peekChar$ansi$_mls_L0_672_764$1.class = class Cont$func$peekChar$ansi$_mls_L0_672_764$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (eof$0, consume$1, cs$2, param0$3, param1$4, c$5, cs$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) => {
      let tmp;
      tmp = super(null);
      this.eof$0 = eof$0;
      this.consume$1 = consume$1;
      this.cs$2 = cs$2;
      this.param0$3 = param0$3;
      this.param1$4 = param1$4;
      this.c$5 = c$5;
      this.cs$6 = cs$6;
      this.tmp$7 = tmp$7;
      this.curDepth$8 = curDepth$8;
      this.tmp$9 = tmp$9;
      this.stackDelayRes$10 = stackDelayRes$10;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 41) {
      this.stackDelayRes$10 = value$;
    } else if (this.pc === 43) {
      this.tmp$9 = value$;
    } else if (this.pc === 42) {
      this.tmp$7 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 41) {
        if (this.cs$2 instanceof NofibPrelude.Nil.class) {
          this.pc = 45;
          continue contLoop;
        } else if (this.cs$2 instanceof NofibPrelude.Cons.class) {
          this.param0$3 = this.cs$2.head;
          this.param1$4 = this.cs$2.tail;
          this.c$5 = this.param0$3;
          this.cs$6 = this.param1$4;
          this.pc = 47;
          continue contLoop;
          this.pc = 44;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$9 = new globalThis.Error("match error");
          if (this.tmp$9 instanceof runtime.EffectSig.class) {
            this.pc = 43;
            this.tmp$9.contTrace.last.next = this;
            this.tmp$9.contTrace.last = this;
            return this.tmp$9
          }
          this.pc = 43;
          continue contLoop;
        }
        this.pc = 44;
        continue contLoop;
      } else if (this.pc === 44) {
        break contLoop;
      } else if (this.pc === 43) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$8);
        throw this.tmp$9;
      } else if (this.pc === 46) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.consume$1(this.c$5, this.tmp$7))
      } else if (this.pc === 47) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = NofibPrelude.Cons(this.c$5, this.cs$6);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 42;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 42;
        continue contLoop;
      } else if (this.pc === 42) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$8);
        this.pc = 46;
        continue contLoop;
      } else if (this.pc === 45) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.eof$0(NofibPrelude.Nil))
      }
      break;
    }
  }
  toString() { return "Cont$func$peekChar$ansi$_mls_L0_672_764$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$readChar$ansi$_mls_L0_579_666$$ = function Cont$func$readChar$ansi$_mls_L0_579_666$$(eof$0, consume$1, cs$2, param0$3, param1$4, c$5, cs$6, tmp$7, curDepth$8, stackDelayRes$9, pc) {
  let tmp;
  tmp = new Cont$func$readChar$ansi$_mls_L0_579_666$1.class(pc);
  return tmp(eof$0, consume$1, cs$2, param0$3, param1$4, c$5, cs$6, tmp$7, curDepth$8, stackDelayRes$9)
};
Cont$func$readChar$ansi$_mls_L0_579_666$$ctor = function Cont$func$readChar$ansi$_mls_L0_579_666$$ctor(eof$0, consume$1, cs$2, param0$3, param1$4, c$5, cs$6, tmp$7, curDepth$8, stackDelayRes$9) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$readChar$ansi$_mls_L0_579_666$1.class(pc);
    return tmp(eof$0, consume$1, cs$2, param0$3, param1$4, c$5, cs$6, tmp$7, curDepth$8, stackDelayRes$9)
  }
};
Cont$func$readChar$ansi$_mls_L0_579_666$1 = function Cont$func$readChar$ansi$_mls_L0_579_666$(pc1) {
  return (eof$01, consume$11, cs$21, param0$31, param1$41, c$51, cs$61, tmp$71, curDepth$81, stackDelayRes$91) => {
    return new Cont$func$readChar$ansi$_mls_L0_579_666$.class(pc1)(eof$01, consume$11, cs$21, param0$31, param1$41, c$51, cs$61, tmp$71, curDepth$81, stackDelayRes$91);
  }
};
Cont$func$readChar$ansi$_mls_L0_579_666$1.class = class Cont$func$readChar$ansi$_mls_L0_579_666$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (eof$0, consume$1, cs$2, param0$3, param1$4, c$5, cs$6, tmp$7, curDepth$8, stackDelayRes$9) => {
      let tmp;
      tmp = super(null);
      this.eof$0 = eof$0;
      this.consume$1 = consume$1;
      this.cs$2 = cs$2;
      this.param0$3 = param0$3;
      this.param1$4 = param1$4;
      this.c$5 = c$5;
      this.cs$6 = cs$6;
      this.tmp$7 = tmp$7;
      this.curDepth$8 = curDepth$8;
      this.stackDelayRes$9 = stackDelayRes$9;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 36) {
      this.stackDelayRes$9 = value$;
    } else if (this.pc === 37) {
      this.tmp$7 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 36) {
        if (this.cs$2 instanceof NofibPrelude.Nil.class) {
          this.pc = 39;
          continue contLoop;
        } else if (this.cs$2 instanceof NofibPrelude.Cons.class) {
          this.param0$3 = this.cs$2.head;
          this.param1$4 = this.cs$2.tail;
          this.c$5 = this.param0$3;
          this.cs$6 = this.param1$4;
          this.pc = 40;
          continue contLoop;
          this.pc = 38;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$7 = new globalThis.Error("match error");
          if (this.tmp$7 instanceof runtime.EffectSig.class) {
            this.pc = 37;
            this.tmp$7.contTrace.last.next = this;
            this.tmp$7.contTrace.last = this;
            return this.tmp$7
          }
          this.pc = 37;
          continue contLoop;
        }
        this.pc = 38;
        continue contLoop;
      } else if (this.pc === 38) {
        break contLoop;
      } else if (this.pc === 37) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$8);
        throw this.tmp$7;
      } else if (this.pc === 40) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.consume$1(this.c$5, this.cs$6))
      } else if (this.pc === 39) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.eof$0(NofibPrelude.Nil))
      }
      break;
    }
  }
  toString() { return "Cont$func$readChar$ansi$_mls_L0_579_666$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$end$ansi$_mls_L0_542_573$$ = function Cont$func$end$ansi$_mls_L0_542_573$$(stackDelayRes$0, pc) {
  let tmp;
  tmp = new Cont$func$end$ansi$_mls_L0_542_573$1.class(pc);
  return tmp(stackDelayRes$0)
};
Cont$func$end$ansi$_mls_L0_542_573$$ctor = function Cont$func$end$ansi$_mls_L0_542_573$$ctor(stackDelayRes$0) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$end$ansi$_mls_L0_542_573$1.class(pc);
    return tmp(stackDelayRes$0)
  }
};
Cont$func$end$ansi$_mls_L0_542_573$1 = function Cont$func$end$ansi$_mls_L0_542_573$(pc1) {
  return (stackDelayRes$01) => {
    return new Cont$func$end$ansi$_mls_L0_542_573$.class(pc1)(stackDelayRes$01);
  }
};
Cont$func$end$ansi$_mls_L0_542_573$1.class = class Cont$func$end$ansi$_mls_L0_542_573$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (stackDelayRes$0) => {
      let tmp;
      tmp = super(null);
      this.stackDelayRes$0 = stackDelayRes$0;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 34) {
      this.stackDelayRes$0 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 34) {
        this.pc = 35;
        continue contLoop;
      } else if (this.pc === 35) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.nofibStringToList("")
      }
      break;
    }
  }
  toString() { return "Cont$func$end$ansi$_mls_L0_542_573$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$highlight$ansi$_mls_L0_458_536$$ = function Cont$func$highlight$ansi$_mls_L0_458_536$$(s$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5, pc) {
  let tmp;
  tmp = new Cont$func$highlight$ansi$_mls_L0_458_536$1.class(pc);
  return tmp(s$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5)
};
Cont$func$highlight$ansi$_mls_L0_458_536$$ctor = function Cont$func$highlight$ansi$_mls_L0_458_536$$ctor(s$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$highlight$ansi$_mls_L0_458_536$1.class(pc);
    return tmp(s$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5)
  }
};
Cont$func$highlight$ansi$_mls_L0_458_536$1 = function Cont$func$highlight$ansi$_mls_L0_458_536$(pc1) {
  return (s$01, tmp$11, tmp$21, tmp$31, curDepth$41, stackDelayRes$51) => {
    return new Cont$func$highlight$ansi$_mls_L0_458_536$.class(pc1)(s$01, tmp$11, tmp$21, tmp$31, curDepth$41, stackDelayRes$51);
  }
};
Cont$func$highlight$ansi$_mls_L0_458_536$1.class = class Cont$func$highlight$ansi$_mls_L0_458_536$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (s$0, tmp$1, tmp$2, tmp$3, curDepth$4, stackDelayRes$5) => {
      let tmp;
      tmp = super(null);
      this.s$0 = s$0;
      this.tmp$1 = tmp$1;
      this.tmp$2 = tmp$2;
      this.tmp$3 = tmp$3;
      this.curDepth$4 = curDepth$4;
      this.stackDelayRes$5 = stackDelayRes$5;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 26) {
      this.stackDelayRes$5 = value$;
    } else if (this.pc === 27) {
      this.tmp$1 = value$;
    } else if (this.pc === 28) {
      this.tmp$2 = value$;
    } else if (this.pc === 29) {
      this.tmp$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 26) {
        this.pc = 33;
        continue contLoop;
      } else if (this.pc === 30) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.append(this.tmp$1, this.tmp$3)
      } else if (this.pc === 33) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = NofibPrelude.nofibStringToList("ESC[7m");
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 27;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 27;
        continue contLoop;
      } else if (this.pc === 27) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$4);
        this.pc = 32;
        continue contLoop;
      } else if (this.pc === 31) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = NofibPrelude.append(this.s$0, this.tmp$2);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 29;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 29;
        continue contLoop;
      } else if (this.pc === 32) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = NofibPrelude.nofibStringToList("ESC[0m");
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 28;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 28;
        continue contLoop;
      } else if (this.pc === 28) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$4);
        this.pc = 31;
        continue contLoop;
      } else if (this.pc === 29) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$4);
        this.pc = 30;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$highlight$ansi$_mls_L0_458_536$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$at$ansi$_mls_L0_402_452$$ = function Cont$func$at$ansi$_mls_L0_402_452$$(x_y$0, s$1, first1$2, first0$3, x$4, y$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9, pc) {
  let tmp;
  tmp = new Cont$func$at$ansi$_mls_L0_402_452$1.class(pc);
  return tmp(x_y$0, s$1, first1$2, first0$3, x$4, y$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9)
};
Cont$func$at$ansi$_mls_L0_402_452$$ctor = function Cont$func$at$ansi$_mls_L0_402_452$$ctor(x_y$0, s$1, first1$2, first0$3, x$4, y$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$at$ansi$_mls_L0_402_452$1.class(pc);
    return tmp(x_y$0, s$1, first1$2, first0$3, x$4, y$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9)
  }
};
Cont$func$at$ansi$_mls_L0_402_452$1 = function Cont$func$at$ansi$_mls_L0_402_452$(pc1) {
  return (x_y$01, s$11, first1$21, first0$31, x$41, y$51, tmp$61, curDepth$71, tmp$81, stackDelayRes$91) => {
    return new Cont$func$at$ansi$_mls_L0_402_452$.class(pc1)(x_y$01, s$11, first1$21, first0$31, x$41, y$51, tmp$61, curDepth$71, tmp$81, stackDelayRes$91);
  }
};
Cont$func$at$ansi$_mls_L0_402_452$1.class = class Cont$func$at$ansi$_mls_L0_402_452$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x_y$0, s$1, first1$2, first0$3, x$4, y$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9) => {
      let tmp;
      tmp = super(null);
      this.x_y$0 = x_y$0;
      this.s$1 = s$1;
      this.first1$2 = first1$2;
      this.first0$3 = first0$3;
      this.x$4 = x$4;
      this.y$5 = y$5;
      this.tmp$6 = tmp$6;
      this.curDepth$7 = curDepth$7;
      this.tmp$8 = tmp$8;
      this.stackDelayRes$9 = stackDelayRes$9;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 20) {
      this.stackDelayRes$9 = value$;
    } else if (this.pc === 22) {
      this.tmp$8 = value$;
    } else if (this.pc === 21) {
      this.tmp$6 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 20) {
        if (globalThis.Array.isArray(this.x_y$0) && this.x_y$0.length === 2) {
          this.first0$3 = this.x_y$0[0];
          this.first1$2 = this.x_y$0[1];
          this.x$4 = this.first0$3;
          this.y$5 = this.first1$2;
          this.pc = 25;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$8 = new globalThis.Error("match error");
          if (this.tmp$8 instanceof runtime.EffectSig.class) {
            this.pc = 22;
            this.tmp$8.contTrace.last.next = this;
            this.tmp$8.contTrace.last = this;
            return this.tmp$8
          }
          this.pc = 22;
          continue contLoop;
        }
        this.pc = 23;
        continue contLoop;
      } else if (this.pc === 23) {
        break contLoop;
      } else if (this.pc === 22) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$7);
        throw this.tmp$8;
      } else if (this.pc === 24) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.append(this.tmp$6, this.s$1)
      } else if (this.pc === 25) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = ansi1.goto(this.x$4, this.y$5);
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 21;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 21;
        continue contLoop;
      } else if (this.pc === 21) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$7);
        this.pc = 24;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$at$ansi$_mls_L0_402_452$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$goto$ansi$_mls_L0_262_396$$ = function Cont$func$goto$ansi$_mls_L0_262_396$$(x$0, y$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12, pc) {
  let tmp;
  tmp = new Cont$func$goto$ansi$_mls_L0_262_396$1.class(pc);
  return tmp(x$0, y$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12)
};
Cont$func$goto$ansi$_mls_L0_262_396$$ctor = function Cont$func$goto$ansi$_mls_L0_262_396$$ctor(x$0, y$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$goto$ansi$_mls_L0_262_396$1.class(pc);
    return tmp(x$0, y$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12)
  }
};
Cont$func$goto$ansi$_mls_L0_262_396$1 = function Cont$func$goto$ansi$_mls_L0_262_396$(pc1) {
  return (x$01, y$11, tmp$21, tmp$31, tmp$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, curDepth$111, stackDelayRes$121) => {
    return new Cont$func$goto$ansi$_mls_L0_262_396$.class(pc1)(x$01, y$11, tmp$21, tmp$31, tmp$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, curDepth$111, stackDelayRes$121);
  }
};
Cont$func$goto$ansi$_mls_L0_262_396$1.class = class Cont$func$goto$ansi$_mls_L0_262_396$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, y$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12) => {
      let tmp;
      tmp = super(null);
      this.x$0 = x$0;
      this.y$1 = y$1;
      this.tmp$2 = tmp$2;
      this.tmp$3 = tmp$3;
      this.tmp$4 = tmp$4;
      this.tmp$5 = tmp$5;
      this.tmp$6 = tmp$6;
      this.tmp$7 = tmp$7;
      this.tmp$8 = tmp$8;
      this.tmp$9 = tmp$9;
      this.tmp$10 = tmp$10;
      this.curDepth$11 = curDepth$11;
      this.stackDelayRes$12 = stackDelayRes$12;
      this.pc = pc;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 0) {
      this.stackDelayRes$12 = value$;
    } else if (this.pc === 1) {
      this.tmp$2 = value$;
    } else if (this.pc === 2) {
      this.tmp$3 = value$;
    } else if (this.pc === 3) {
      this.tmp$4 = value$;
    } else if (this.pc === 4) {
      this.tmp$5 = value$;
    } else if (this.pc === 5) {
      this.tmp$6 = value$;
    } else if (this.pc === 6) {
      this.tmp$7 = value$;
    } else if (this.pc === 7) {
      this.tmp$8 = value$;
    } else if (this.pc === 8) {
      this.tmp$9 = value$;
    } else if (this.pc === 9) {
      this.tmp$10 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 0) {
        this.pc = 19;
        continue contLoop;
      } else if (this.pc === 10) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons("E", this.tmp$10)
      } else if (this.pc === 11) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$10 = NofibPrelude.Cons("[", this.tmp$9);
        if (this.tmp$10 instanceof runtime.EffectSig.class) {
          this.pc = 9;
          this.tmp$10.contTrace.last.next = this;
          this.tmp$10.contTrace.last = this;
          return this.tmp$10
        }
        this.pc = 9;
        continue contLoop;
      } else if (this.pc === 12) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = NofibPrelude.append(this.tmp$3, this.tmp$8);
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 8;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 8;
        continue contLoop;
      } else if (this.pc === 18) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = NofibPrelude.nofibStringToList(this.tmp$2);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 2;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 2;
        continue contLoop;
      } else if (this.pc === 19) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = NofibPrelude.stringOfInt(this.y$1);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 1;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 1;
        continue contLoop;
      } else if (this.pc === 1) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$11);
        this.pc = 18;
        continue contLoop;
      } else if (this.pc === 2) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$11);
        this.pc = 17;
        continue contLoop;
      } else if (this.pc === 13) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = NofibPrelude.Cons(";", this.tmp$7);
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 7;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 7;
        continue contLoop;
      } else if (this.pc === 14) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = NofibPrelude.append(this.tmp$5, this.tmp$6);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 6;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 6;
        continue contLoop;
      } else if (this.pc === 16) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = NofibPrelude.nofibStringToList(this.tmp$4);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 4;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 4;
        continue contLoop;
      } else if (this.pc === 17) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$4 = NofibPrelude.stringOfInt(this.x$0);
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 3;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 3;
        continue contLoop;
      } else if (this.pc === 3) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$11);
        this.pc = 16;
        continue contLoop;
      } else if (this.pc === 4) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$11);
        this.pc = 15;
        continue contLoop;
      } else if (this.pc === 15) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = NofibPrelude.nofibStringToList("H");
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 5;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 5;
        continue contLoop;
      } else if (this.pc === 5) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$11);
        this.pc = 14;
        continue contLoop;
      } else if (this.pc === 6) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$11);
        this.pc = 13;
        continue contLoop;
      } else if (this.pc === 7) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$11);
        this.pc = 12;
        continue contLoop;
      } else if (this.pc === 8) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$11);
        this.pc = 11;
        continue contLoop;
      } else if (this.pc === 9) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$11);
        this.pc = 10;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$goto$ansi$_mls_L0_262_396$(" + globalThis.Predef.render(this.pc) + ")"; }
};
ansi1 = class ansi {
  static #cls;
  static {
    let tmp, lambda10, res, lambda11, lambda12;
    lambda11 = (undefined, function () {
      return NofibPrelude.nofibStringToList("L")
    });
    tmp = runtime.runStackSafe(500, lambda11);
    if (tmp instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    ansi.#cls = tmp;
    lambda10 = (undefined, function () {
      let tmp1, curDepth, stackDelayRes;
      curDepth = runtime.stackDepth;
      stackDelayRes = runtime.checkDepth();
      if (stackDelayRes instanceof runtime.EffectSig.class) {
        stackDelayRes.contTrace.last.next = Cont$func$lambda$$$(tmp1, curDepth, stackDelayRes, 216);
        stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
        return stackDelayRes
      }
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = ansi.testAnsi_nofib(1);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = Cont$func$lambda$$$(tmp1, curDepth, stackDelayRes, 217);
        tmp1.contTrace.last = tmp1.contTrace.last.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.nofibListToString(tmp1)
    });
    lambda12 = (undefined, function () {
      return BenchmarkPrelude.benchmark(lambda10)
    });
    res = runtime.runStackSafe(500, lambda12);
    if (res instanceof runtime.EffectSig.class) {
      throw new globalThis.Error("Unhandled effects");
    }
    res
  }
  static goto(x, y) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$goto$ansi$_mls_L0_262_396$$(x, y, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, stackDelayRes, 0);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = NofibPrelude.stringOfInt(y);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$goto$ansi$_mls_L0_262_396$$(x, y, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, stackDelayRes, 1);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = NofibPrelude.nofibStringToList(tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$goto$ansi$_mls_L0_262_396$$(x, y, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, stackDelayRes, 2);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = NofibPrelude.stringOfInt(x);
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$goto$ansi$_mls_L0_262_396$$(x, y, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, stackDelayRes, 3);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp3 = NofibPrelude.nofibStringToList(tmp2);
    if (tmp3 instanceof runtime.EffectSig.class) {
      tmp3.contTrace.last.next = Cont$func$goto$ansi$_mls_L0_262_396$$(x, y, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, stackDelayRes, 4);
      tmp3.contTrace.last = tmp3.contTrace.last.next;
      return tmp3
    }
    tmp3 = runtime.resetDepth(tmp3, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp4 = NofibPrelude.nofibStringToList("H");
    if (tmp4 instanceof runtime.EffectSig.class) {
      tmp4.contTrace.last.next = Cont$func$goto$ansi$_mls_L0_262_396$$(x, y, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, stackDelayRes, 5);
      tmp4.contTrace.last = tmp4.contTrace.last.next;
      return tmp4
    }
    tmp4 = runtime.resetDepth(tmp4, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp5 = NofibPrelude.append(tmp3, tmp4);
    if (tmp5 instanceof runtime.EffectSig.class) {
      tmp5.contTrace.last.next = Cont$func$goto$ansi$_mls_L0_262_396$$(x, y, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, stackDelayRes, 6);
      tmp5.contTrace.last = tmp5.contTrace.last.next;
      return tmp5
    }
    tmp5 = runtime.resetDepth(tmp5, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp6 = NofibPrelude.Cons(";", tmp5);
    if (tmp6 instanceof runtime.EffectSig.class) {
      tmp6.contTrace.last.next = Cont$func$goto$ansi$_mls_L0_262_396$$(x, y, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, stackDelayRes, 7);
      tmp6.contTrace.last = tmp6.contTrace.last.next;
      return tmp6
    }
    tmp6 = runtime.resetDepth(tmp6, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp7 = NofibPrelude.append(tmp1, tmp6);
    if (tmp7 instanceof runtime.EffectSig.class) {
      tmp7.contTrace.last.next = Cont$func$goto$ansi$_mls_L0_262_396$$(x, y, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, stackDelayRes, 8);
      tmp7.contTrace.last = tmp7.contTrace.last.next;
      return tmp7
    }
    tmp7 = runtime.resetDepth(tmp7, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp8 = NofibPrelude.Cons("[", tmp7);
    if (tmp8 instanceof runtime.EffectSig.class) {
      tmp8.contTrace.last.next = Cont$func$goto$ansi$_mls_L0_262_396$$(x, y, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, curDepth, stackDelayRes, 9);
      tmp8.contTrace.last = tmp8.contTrace.last.next;
      return tmp8
    }
    tmp8 = runtime.resetDepth(tmp8, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.Cons("E", tmp8)
  } 
  static at(x_y, s) {
    let first1, first0, x1, y1, tmp, curDepth, tmp1, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$at$ansi$_mls_L0_402_452$$(x_y, s, first1, first0, x1, y1, tmp, curDepth, tmp1, stackDelayRes, 20);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    if (globalThis.Array.isArray(x_y) && x_y.length === 2) {
      first0 = x_y[0];
      first1 = x_y[1];
      x1 = first0;
      y1 = first1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = ansi.goto(x1, y1);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$at$ansi$_mls_L0_402_452$$(x_y, s, first1, first0, x1, y1, tmp, curDepth, tmp1, stackDelayRes, 21);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.append(tmp, s)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = new globalThis.Error("match error");
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = Cont$func$at$ansi$_mls_L0_402_452$$(x_y, s, first1, first0, x1, y1, tmp, curDepth, tmp1, stackDelayRes, 22);
        tmp1.contTrace.last = tmp1.contTrace.last.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      throw tmp1;
    }
  } 
  static highlight(s1) {
    let tmp, tmp1, tmp2, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$highlight$ansi$_mls_L0_458_536$$(s1, tmp, tmp1, tmp2, curDepth, stackDelayRes, 26);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = NofibPrelude.nofibStringToList("ESC[7m");
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$highlight$ansi$_mls_L0_458_536$$(s1, tmp, tmp1, tmp2, curDepth, stackDelayRes, 27);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = NofibPrelude.nofibStringToList("ESC[0m");
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$highlight$ansi$_mls_L0_458_536$$(s1, tmp, tmp1, tmp2, curDepth, stackDelayRes, 28);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = NofibPrelude.append(s1, tmp1);
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$highlight$ansi$_mls_L0_458_536$$(s1, tmp, tmp1, tmp2, curDepth, stackDelayRes, 29);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.append(tmp, tmp2)
  } 
  static end(xs) {
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$end$ansi$_mls_L0_542_573$$(stackDelayRes, 34);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.nofibStringToList("")
  } 
  static readChar(eof, consume, cs) {
    let param0, param1, c, cs1, tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$readChar$ansi$_mls_L0_579_666$$(eof, consume, cs, param0, param1, c, cs1, tmp, curDepth, stackDelayRes, 36);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    if (cs instanceof NofibPrelude.Nil.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(eof(NofibPrelude.Nil))
    } else if (cs instanceof NofibPrelude.Cons.class) {
      param0 = cs.head;
      param1 = cs.tail;
      c = param0;
      cs1 = param1;
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(consume(c, cs1))
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = new globalThis.Error("match error");
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$readChar$ansi$_mls_L0_579_666$$(eof, consume, cs, param0, param1, c, cs1, tmp, curDepth, stackDelayRes, 37);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      throw tmp;
    }
  } 
  static peekChar(eof1, consume1, cs1) {
    let param0, param1, c, cs2, tmp, curDepth, tmp1, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$peekChar$ansi$_mls_L0_672_764$$(eof1, consume1, cs1, param0, param1, c, cs2, tmp, curDepth, tmp1, stackDelayRes, 41);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    if (cs1 instanceof NofibPrelude.Nil.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(eof1(NofibPrelude.Nil))
    } else if (cs1 instanceof NofibPrelude.Cons.class) {
      param0 = cs1.head;
      param1 = cs1.tail;
      c = param0;
      cs2 = param1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = NofibPrelude.Cons(c, cs2);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$peekChar$ansi$_mls_L0_672_764$$(eof1, consume1, cs1, param0, param1, c, cs2, tmp, curDepth, tmp1, stackDelayRes, 42);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runtime.safeCall(consume1(c, tmp))
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = new globalThis.Error("match error");
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = Cont$func$peekChar$ansi$_mls_L0_672_764$$(eof1, consume1, cs1, param0, param1, c, cs2, tmp, curDepth, tmp1, stackDelayRes, 43);
        tmp1.contTrace.last = tmp1.contTrace.last.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      throw tmp1;
    }
  } 
  static pressAnyKey(prog, x1) {
    let stackDelayRes, lambda$this;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$pressAnyKey$ansi$_mls_L0_770_829$$(prog, x1, stackDelayRes, 48);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    lambda$this = runtime.safeCall(lambda(prog));
    return ansi.readChar(prog, lambda$this, x1)
  } 
  static unreadChar(c, prog1, cs2) {
    let tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$unreadChar$ansi$_mls_L0_835_874$$(c, prog1, cs2, tmp, curDepth, stackDelayRes, 52);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = NofibPrelude.Cons(c, cs2);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$unreadChar$ansi$_mls_L0_835_874$$(c, prog1, cs2, tmp, curDepth, stackDelayRes, 53);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(prog1(tmp))
  } 
  static writeChar(c1, prog2, cs3) {
    let tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$writeChar$ansi$_mls_L0_880_918$$(c1, prog2, cs3, tmp, curDepth, stackDelayRes, 56);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = runtime.safeCall(prog2(cs3));
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$writeChar$ansi$_mls_L0_880_918$$(c1, prog2, cs3, tmp, curDepth, stackDelayRes, 57);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.Cons(c1, tmp)
  } 
  static writeString(s2, prog3, cs4) {
    let tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$writeString$ansi$_mls_L0_924_964$$(s2, prog3, cs4, tmp, curDepth, stackDelayRes, 60);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = runtime.safeCall(prog3(cs4));
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$writeString$ansi$_mls_L0_924_964$$(s2, prog3, cs4, tmp, curDepth, stackDelayRes, 61);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.append(s2, tmp)
  } 
  static writes(ss, a, b) {
    let tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$writes$ansi$_mls_L0_970_1018$$(ss, a, b, tmp, curDepth, stackDelayRes, 64);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = NofibPrelude.concat(ss);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$writes$ansi$_mls_L0_970_1018$$(ss, a, b, tmp, curDepth, stackDelayRes, 65);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return ansi.writeString(tmp, a, b)
  } 
  static ringBell(prog4, cs5) {
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$ringBell$ansi$_mls_L0_1024_1069$$(prog4, cs5, stackDelayRes, 68);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return ansi.writeChar("B", prog4, cs5)
  } 
  static clearScreen(a1, b1) {
    let stackDelayRes;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$clearScreen$ansi$_mls_L0_1075_1117$$(a1, b1, stackDelayRes, 70);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    return ansi.writeString(ansi.#cls, a1, b1)
  } 
  static writeAt(x_y1, s3, a2) {
    let first1, first0, x2, y1, tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$writeAt$ansi$_mls_L0_1123_1205$$(x_y1, s3, a2, first1, first0, x2, y1, tmp, curDepth, stackDelayRes, 72);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    if (globalThis.Array.isArray(x_y1) && x_y1.length === 2) {
      first0 = x_y1[0];
      first1 = x_y1[1];
      x2 = first0;
      y1 = first1;
      return runtime.safeCall(lambda1(s3, a2, x2, y1))
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = new globalThis.Error("match error");
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$writeAt$ansi$_mls_L0_1123_1205$$(x_y1, s3, a2, first1, first0, x2, y1, tmp, curDepth, stackDelayRes, 79);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      throw tmp;
    }
  } 
  static moveTo(x_y2, a3) {
    let first1, first0, x2, y1, tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$moveTo$ansi$_mls_L0_1211_1284$$(x_y2, a3, first1, first0, x2, y1, tmp, curDepth, stackDelayRes, 81);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    if (globalThis.Array.isArray(x_y2) && x_y2.length === 2) {
      first0 = x_y2[0];
      first1 = x_y2[1];
      x2 = first0;
      y1 = first1;
      return runtime.safeCall(lambda2(a3, x2, y1))
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = new globalThis.Error("match error");
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$moveTo$ansi$_mls_L0_1211_1284$$(x_y2, a3, first1, first0, x2, y1, tmp, curDepth, stackDelayRes, 86);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      throw tmp;
    }
  } 
  static returnn(s4, consume2) {
    let tmp, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$returnn$ansi$_mls_L0_1290_1331$$(s4, consume2, tmp, curDepth, stackDelayRes, 88);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = NofibPrelude.reverse(s4);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$returnn$ansi$_mls_L0_1290_1331$$(s4, consume2, tmp, curDepth, stackDelayRes, 89);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(consume2(tmp))
  } 
  static deletee(n, s5, l, consume3) {
    let scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$deletee$ansi$_mls_L0_1430_1603$$(n, s5, l, consume3, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 92);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    scrut = n > 0;
    if (scrut === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = NofibPrelude.nofibStringToList("BS_BS");
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$deletee$ansi$_mls_L0_1430_1603$$(n, s5, l, consume3, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 93);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      tmp1 = n - 1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = NofibPrelude.tail(s5);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.contTrace.last.next = Cont$func$deletee$ansi$_mls_L0_1430_1603$$(n, s5, l, consume3, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 94);
        tmp2.contTrace.last = tmp2.contTrace.last.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = ansi.loop(tmp1, tmp2, l, consume3);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.contTrace.last.next = Cont$func$deletee$ansi$_mls_L0_1430_1603$$(n, s5, l, consume3, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 95);
        tmp3.contTrace.last = tmp3.contTrace.last.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return ansi.writeString(tmp, tmp3)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = NofibPrelude.nofibStringToList("");
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.contTrace.last.next = Cont$func$deletee$ansi$_mls_L0_1430_1603$$(n, s5, l, consume3, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 96);
        tmp4.contTrace.last = tmp4.contTrace.last.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp5 = ansi.loop(0, tmp4, l, consume3);
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.contTrace.last.next = Cont$func$deletee$ansi$_mls_L0_1430_1603$$(n, s5, l, consume3, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, stackDelayRes, 97);
        tmp5.contTrace.last = tmp5.contTrace.last.next;
        return tmp5
      }
      tmp5 = runtime.resetDepth(tmp5, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return ansi.ringBell(tmp5)
    }
  } 
  static loop(n1, s6, l1, consume4) {
    return runtime.safeCall(lambda3(n1, s6, l1, consume4))
  } 
  static readAt(x_y3, l2, consume5) {
    let tmp, tmp1, tmp2, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$readAt$ansi$_mls_L0_2058_2153$$(x_y3, l2, consume5, tmp, tmp1, tmp2, curDepth, stackDelayRes, 123);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = NofibPrelude.replicate(l2, "_");
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$readAt$ansi$_mls_L0_2058_2153$$(x_y3, l2, consume5, tmp, tmp1, tmp2, curDepth, stackDelayRes, 124);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = ansi.loop(0, "", l2, consume5);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$readAt$ansi$_mls_L0_2058_2153$$(x_y3, l2, consume5, tmp, tmp1, tmp2, curDepth, stackDelayRes, 125);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = ansi.moveTo(x_y3, tmp1);
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$readAt$ansi$_mls_L0_2058_2153$$(x_y3, l2, consume5, tmp, tmp1, tmp2, curDepth, stackDelayRes, 126);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return ansi.writeAt(x_y3, tmp, tmp2)
  } 
  static promptReadAt(x_y4, l3, prompt, consume6) {
    let first1, first0, x2, y1, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$$(x_y4, l3, prompt, consume6, first1, first0, x2, y1, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 131);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    if (globalThis.Array.isArray(x_y4) && x_y4.length === 2) {
      first0 = x_y4[0];
      first1 = x_y4[1];
      x2 = first0;
      y1 = first1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = NofibPrelude.listLen(prompt);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$$(x_y4, l3, prompt, consume6, first1, first0, x2, y1, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 132);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      tmp1 = x2 + tmp;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = ansi.readAt([
        tmp1,
        y1
      ], l3, consume6);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.contTrace.last.next = Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$$(x_y4, l3, prompt, consume6, first1, first0, x2, y1, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 133);
        tmp2.contTrace.last = tmp2.contTrace.last.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return ansi.writeAt([
        x2,
        y1
      ], prompt, tmp2)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = new globalThis.Error("match error");
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.contTrace.last.next = Cont$func$promptReadAt$ansi$_mls_L0_2159_2292$$(x_y4, l3, prompt, consume6, first1, first0, x2, y1, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 134);
        tmp3.contTrace.last = tmp3.contTrace.last.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      throw tmp3;
    }
  } 
  static program(input) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 139);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = NofibPrelude.nofibStringToList("Demonstration program");
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 140);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = ansi.highlight(tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 141);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = ansi.at([
      17,
      5
    ], tmp1);
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 142);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp3 = NofibPrelude.nofibStringToList("Version 1.0");
    if (tmp3 instanceof runtime.EffectSig.class) {
      tmp3.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 143);
      tmp3.contTrace.last = tmp3.contTrace.last.next;
      return tmp3
    }
    tmp3 = runtime.resetDepth(tmp3, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp4 = ansi.at([
      48,
      5
    ], tmp3);
    if (tmp4 instanceof runtime.EffectSig.class) {
      tmp4.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 144);
      tmp4.contTrace.last = tmp4.contTrace.last.next;
      return tmp4
    }
    tmp4 = runtime.resetDepth(tmp4, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp5 = NofibPrelude.nofibStringToList("This program illustrates a simple approach");
    if (tmp5 instanceof runtime.EffectSig.class) {
      tmp5.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 145);
      tmp5.contTrace.last = tmp5.contTrace.last.next;
      return tmp5
    }
    tmp5 = runtime.resetDepth(tmp5, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp6 = ansi.at([
      17,
      7
    ], tmp5);
    if (tmp6 instanceof runtime.EffectSig.class) {
      tmp6.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 146);
      tmp6.contTrace.last = tmp6.contTrace.last.next;
      return tmp6
    }
    tmp6 = runtime.resetDepth(tmp6, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp7 = NofibPrelude.nofibStringToList("to screen-based interactive programs using");
    if (tmp7 instanceof runtime.EffectSig.class) {
      tmp7.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 147);
      tmp7.contTrace.last = tmp7.contTrace.last.next;
      return tmp7
    }
    tmp7 = runtime.resetDepth(tmp7, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp8 = ansi.at([
      17,
      8
    ], tmp7);
    if (tmp8 instanceof runtime.EffectSig.class) {
      tmp8.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 148);
      tmp8.contTrace.last = tmp8.contTrace.last.next;
      return tmp8
    }
    tmp8 = runtime.resetDepth(tmp8, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp9 = NofibPrelude.nofibStringToList("the Hugs functional programming system.");
    if (tmp9 instanceof runtime.EffectSig.class) {
      tmp9.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 149);
      tmp9.contTrace.last = tmp9.contTrace.last.next;
      return tmp9
    }
    tmp9 = runtime.resetDepth(tmp9, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp10 = ansi.at([
      17,
      9
    ], tmp9);
    if (tmp10 instanceof runtime.EffectSig.class) {
      tmp10.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 150);
      tmp10.contTrace.last = tmp10.contTrace.last.next;
      return tmp10
    }
    tmp10 = runtime.resetDepth(tmp10, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp11 = NofibPrelude.nofibStringToList("Please press any key to continue ...");
    if (tmp11 instanceof runtime.EffectSig.class) {
      tmp11.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 151);
      tmp11.contTrace.last = tmp11.contTrace.last.next;
      return tmp11
    }
    tmp11 = runtime.resetDepth(tmp11, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp12 = ansi.at([
      17,
      11
    ], tmp11);
    if (tmp12 instanceof runtime.EffectSig.class) {
      tmp12.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 152);
      tmp12.contTrace.last = tmp12.contTrace.last.next;
      return tmp12
    }
    tmp12 = runtime.resetDepth(tmp12, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp13 = NofibPrelude.Cons(tmp12, NofibPrelude.Nil);
    if (tmp13 instanceof runtime.EffectSig.class) {
      tmp13.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 153);
      tmp13.contTrace.last = tmp13.contTrace.last.next;
      return tmp13
    }
    tmp13 = runtime.resetDepth(tmp13, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp14 = NofibPrelude.Cons(tmp10, tmp13);
    if (tmp14 instanceof runtime.EffectSig.class) {
      tmp14.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 154);
      tmp14.contTrace.last = tmp14.contTrace.last.next;
      return tmp14
    }
    tmp14 = runtime.resetDepth(tmp14, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp15 = NofibPrelude.Cons(tmp8, tmp14);
    if (tmp15 instanceof runtime.EffectSig.class) {
      tmp15.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 155);
      tmp15.contTrace.last = tmp15.contTrace.last.next;
      return tmp15
    }
    tmp15 = runtime.resetDepth(tmp15, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp16 = NofibPrelude.Cons(tmp6, tmp15);
    if (tmp16 instanceof runtime.EffectSig.class) {
      tmp16.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 156);
      tmp16.contTrace.last = tmp16.contTrace.last.next;
      return tmp16
    }
    tmp16 = runtime.resetDepth(tmp16, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp17 = NofibPrelude.Cons(tmp4, tmp16);
    if (tmp17 instanceof runtime.EffectSig.class) {
      tmp17.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 157);
      tmp17.contTrace.last = tmp17.contTrace.last.next;
      return tmp17
    }
    tmp17 = runtime.resetDepth(tmp17, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp18 = NofibPrelude.Cons(tmp2, tmp17);
    if (tmp18 instanceof runtime.EffectSig.class) {
      tmp18.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 158);
      tmp18.contTrace.last = tmp18.contTrace.last.next;
      return tmp18
    }
    tmp18 = runtime.resetDepth(tmp18, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp19 = NofibPrelude.Cons(ansi.#cls, tmp18);
    if (tmp19 instanceof runtime.EffectSig.class) {
      tmp19.contTrace.last.next = Cont$func$program$ansi$_mls_L0_2300_3219$$(input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, curDepth, stackDelayRes, 159);
      tmp19.contTrace.last = tmp19.contTrace.last.next;
      return tmp19
    }
    tmp19 = runtime.resetDepth(tmp19, curDepth);
    tmp20 = lambda5;
    runtime.stackDepth = runtime.stackDepth + 1;
    return ansi.writes(tmp19, tmp20, input)
  } 
  static testAnsi_nofib(n2) {
    let tmp, tmp1, tmp2, curDepth, stackDelayRes;
    curDepth = runtime.stackDepth;
    stackDelayRes = runtime.checkDepth();
    if (stackDelayRes instanceof runtime.EffectSig.class) {
      stackDelayRes.contTrace.last.next = Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$$(n2, tmp, tmp1, tmp2, curDepth, stackDelayRes, 207);
      stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
      return stackDelayRes
    }
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = NofibPrelude.replicate(n2, ansi.program);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$$(n2, tmp, tmp1, tmp2, curDepth, stackDelayRes, 208);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = NofibPrelude.foldr(NofibPrelude.compose, lambda9, tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$$(n2, tmp, tmp1, tmp2, curDepth, stackDelayRes, 209);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = NofibPrelude.nofibStringToList("testtesttest");
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$testAnsi_nofib$ansi$_mls_L0_3225_3327$$(n2, tmp, tmp1, tmp2, curDepth, stackDelayRes, 210);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return runtime.safeCall(tmp1(tmp2))
  }
  static toString() { return "ansi"; }
};
let ansi = ansi1; export default ansi;
