import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let lscomp2, lscomp1, split, trins, to_tree, mkTree, readTree, to_tree1, mkTree1, readTree1, to_heap, clear, heap, mix, runsplit, merge, merge_lists, sort, eqList, compareList, ltList, Tip1, Twig21, unlines, Branch21, LT1, prependToAll, treeSort, insertSort, quickSort, leList, lines, odd, testSorting_nofib, heapSort, partition, Tree1, quickerSort, GT1, Tree21, int_of_char, select, geList, mergeSort, EQ1, hash, mangle, gtList, quickSort2, Tip21, intersperse, z_of_int, Branch1, treeSort2, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, res, Cont$func$int_of_char$sorting$_mls_L0_155_188$1, Cont$func$compareList$sorting$_mls_L0_217_484$1, Cont$func$gtList$sorting$_mls_L0_490_528$1, Cont$func$leList$sorting$_mls_L0_534_566$1, Cont$func$ltList$sorting$_mls_L0_572_610$1, Cont$func$geList$sorting$_mls_L0_616_648$1, Cont$func$eqList$sorting$_mls_L0_654_692$1, Cont$func$prependToAll$sorting$_mls_L0_698_796$1, Cont$func$intersperse$sorting$_mls_L0_802_892$1, Cont$func$lines$sorting$_mls_L0_898_1060$1, Cont$func$lambda$$6, Cont$func$unlines$sorting$_mls_L0_1066_1120$1, Cont$func$odd$sorting$_mls_L0_1126_1153$1, Cont$func$z_of_int$sorting$_mls_L0_1159_1193$1, Cont$func$lambda$$7, Cont$func$hash$sorting$_mls_L0_1199_1303$1, Cont$func$lscomp1$sorting$_mls_L0_1373_1497$1, Cont$func$lscomp2$sorting$_mls_L0_1506_1630$1, Cont$func$quickSort$sorting$_mls_L0_1309_1692$1, Cont$func$select$sorting$_mls_L0_1698_1791$1, Cont$func$lambda$$8, Cont$func$partition$sorting$_mls_L0_1797_1864$1, Cont$func$lambda$$9, Cont$func$quickSort2$sorting$_mls_L0_1870_2030$1, Cont$func$split$sorting$_mls_L0_2128_2328$1, Cont$func$quickerSort$sorting$_mls_L0_2036_2355$1, Cont$func$trins$sorting$_mls_L0_2427_2738$1, Cont$func$insertSort$sorting$_mls_L0_2361_2767$1, Cont$func$to_tree$sorting$_mls_L0_2964_3143$1, Cont$func$mkTree$sorting$_mls_L0_2935_3179$1, Cont$func$readTree$sorting$_mls_L0_3186_3283$1, Cont$func$treeSort$sorting$_mls_L0_2911_3309$1, Cont$func$to_tree$sorting$_mls_L0_3563_3847$1, Cont$func$mkTree$sorting$_mls_L0_3534_3884$1, Cont$func$readTree$sorting$_mls_L0_3891_4017$1, Cont$func$treeSort2$sorting$_mls_L0_3509_4043$1, Cont$func$heap$sorting$_mls_L0_4070_4159$1, Cont$func$to_heap$sorting$_mls_L0_4166_4505$1, Cont$func$clear$sorting$_mls_L0_4512_4594$1, Cont$func$mix$sorting$_mls_L0_4601_4832$1, Cont$func$heapSort$sorting$_mls_L0_4049_4853$1, Cont$func$runsplit$sorting$_mls_L0_4884_5375$1, Cont$func$merge_lists$sorting$_mls_L0_5382_5470$1, Cont$func$merge$sorting$_mls_L0_5477_5718$1, Cont$func$mergeSort$sorting$_mls_L0_4859_5754$1, Cont$func$lambda$$10, Cont$func$sort$sorting$_mls_L0_5781_6003$1, Cont$func$mangle$sorting$_mls_L0_5760_6032$1, Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$1, Cont$func$lambda$$11, lambda9, Cont$func$int_of_char$sorting$_mls_L0_155_188$$ctor, Cont$func$int_of_char$sorting$_mls_L0_155_188$$, Cont$func$compareList$sorting$_mls_L0_217_484$$ctor, Cont$func$compareList$sorting$_mls_L0_217_484$$, Cont$func$gtList$sorting$_mls_L0_490_528$$ctor, Cont$func$gtList$sorting$_mls_L0_490_528$$, Cont$func$leList$sorting$_mls_L0_534_566$$ctor, Cont$func$leList$sorting$_mls_L0_534_566$$, Cont$func$ltList$sorting$_mls_L0_572_610$$ctor, Cont$func$ltList$sorting$_mls_L0_572_610$$, Cont$func$geList$sorting$_mls_L0_616_648$$ctor, Cont$func$geList$sorting$_mls_L0_616_648$$, Cont$func$eqList$sorting$_mls_L0_654_692$$ctor, Cont$func$eqList$sorting$_mls_L0_654_692$$, Cont$func$prependToAll$sorting$_mls_L0_698_796$$ctor, Cont$func$prependToAll$sorting$_mls_L0_698_796$$, Cont$func$intersperse$sorting$_mls_L0_802_892$$ctor, Cont$func$intersperse$sorting$_mls_L0_802_892$$, Cont$func$lines$sorting$_mls_L0_898_1060$$ctor, Cont$func$lines$sorting$_mls_L0_898_1060$$, Cont$func$lambda$$$ctor, Cont$func$lambda$$$, Cont$func$unlines$sorting$_mls_L0_1066_1120$$ctor, Cont$func$unlines$sorting$_mls_L0_1066_1120$$, Cont$func$odd$sorting$_mls_L0_1126_1153$$ctor, Cont$func$odd$sorting$_mls_L0_1126_1153$$, Cont$func$z_of_int$sorting$_mls_L0_1159_1193$$ctor, Cont$func$z_of_int$sorting$_mls_L0_1159_1193$$, Cont$func$lambda$$$ctor1, Cont$func$lambda$$$1, Cont$func$hash$sorting$_mls_L0_1199_1303$$ctor, Cont$func$hash$sorting$_mls_L0_1199_1303$$, lscomp2$, Cont$func$lscomp2$sorting$_mls_L0_1506_1630$$ctor, Cont$func$lscomp2$sorting$_mls_L0_1506_1630$$, lscomp1$, Cont$func$lscomp1$sorting$_mls_L0_1373_1497$$ctor, Cont$func$lscomp1$sorting$_mls_L0_1373_1497$$, Cont$func$quickSort$sorting$_mls_L0_1309_1692$$ctor, Cont$func$quickSort$sorting$_mls_L0_1309_1692$$, Cont$func$select$sorting$_mls_L0_1698_1791$$ctor, Cont$func$select$sorting$_mls_L0_1698_1791$$, lambda$, Cont$func$lambda$$$ctor2, Cont$func$lambda$$$2, Cont$func$partition$sorting$_mls_L0_1797_1864$$ctor, Cont$func$partition$sorting$_mls_L0_1797_1864$$, lambda$1, Cont$func$lambda$$$ctor3, Cont$func$lambda$$$3, Cont$func$quickSort2$sorting$_mls_L0_1870_2030$$ctor, Cont$func$quickSort2$sorting$_mls_L0_1870_2030$$, split$, Cont$func$split$sorting$_mls_L0_2128_2328$$ctor, Cont$func$split$sorting$_mls_L0_2128_2328$$, Cont$func$quickerSort$sorting$_mls_L0_2036_2355$$ctor, Cont$func$quickerSort$sorting$_mls_L0_2036_2355$$, quickerSort$capture1, Cont$func$trins$sorting$_mls_L0_2427_2738$$ctor, Cont$func$trins$sorting$_mls_L0_2427_2738$$, Cont$func$insertSort$sorting$_mls_L0_2361_2767$$ctor, Cont$func$insertSort$sorting$_mls_L0_2361_2767$$, Cont$func$readTree$sorting$_mls_L0_3186_3283$$ctor, Cont$func$readTree$sorting$_mls_L0_3186_3283$$, Cont$func$to_tree$sorting$_mls_L0_2964_3143$$ctor, Cont$func$to_tree$sorting$_mls_L0_2964_3143$$, Cont$func$mkTree$sorting$_mls_L0_2935_3179$$ctor, Cont$func$mkTree$sorting$_mls_L0_2935_3179$$, Cont$func$treeSort$sorting$_mls_L0_2911_3309$$ctor, Cont$func$treeSort$sorting$_mls_L0_2911_3309$$, Cont$func$readTree$sorting$_mls_L0_3891_4017$$ctor, Cont$func$readTree$sorting$_mls_L0_3891_4017$$, Cont$func$to_tree$sorting$_mls_L0_3563_3847$$ctor, Cont$func$to_tree$sorting$_mls_L0_3563_3847$$, Cont$func$mkTree$sorting$_mls_L0_3534_3884$$ctor, Cont$func$mkTree$sorting$_mls_L0_3534_3884$$, Cont$func$treeSort2$sorting$_mls_L0_3509_4043$$ctor, Cont$func$treeSort2$sorting$_mls_L0_3509_4043$$, Cont$func$mix$sorting$_mls_L0_4601_4832$$ctor, Cont$func$mix$sorting$_mls_L0_4601_4832$$, Cont$func$clear$sorting$_mls_L0_4512_4594$$ctor, Cont$func$clear$sorting$_mls_L0_4512_4594$$, Cont$func$to_heap$sorting$_mls_L0_4166_4505$$ctor, Cont$func$to_heap$sorting$_mls_L0_4166_4505$$, Cont$func$heap$sorting$_mls_L0_4070_4159$$ctor, Cont$func$heap$sorting$_mls_L0_4070_4159$$, Cont$func$heapSort$sorting$_mls_L0_4049_4853$$ctor, Cont$func$heapSort$sorting$_mls_L0_4049_4853$$, Cont$func$merge$sorting$_mls_L0_5477_5718$$ctor, Cont$func$merge$sorting$_mls_L0_5477_5718$$, Cont$func$merge_lists$sorting$_mls_L0_5382_5470$$ctor, Cont$func$merge_lists$sorting$_mls_L0_5382_5470$$, Cont$func$runsplit$sorting$_mls_L0_4884_5375$$ctor, Cont$func$runsplit$sorting$_mls_L0_4884_5375$$, Cont$func$mergeSort$sorting$_mls_L0_4859_5754$$ctor, Cont$func$mergeSort$sorting$_mls_L0_4859_5754$$, lambda$2, Cont$func$lambda$$$ctor4, Cont$func$lambda$$$4, Cont$func$sort$sorting$_mls_L0_5781_6003$$ctor, Cont$func$sort$sorting$_mls_L0_5781_6003$$, Cont$func$mangle$sorting$_mls_L0_5760_6032$$ctor, Cont$func$mangle$sorting$_mls_L0_5760_6032$$, Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$$ctor, Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$$, Cont$func$lambda$$$ctor5, Cont$func$lambda$$$5;
Cont$func$int_of_char$sorting$_mls_L0_155_188$$ = function Cont$func$int_of_char$sorting$_mls_L0_155_188$$(c$0, stackDelayRes$1, pc) {
  let tmp;
  tmp = new Cont$func$int_of_char$sorting$_mls_L0_155_188$1.class(pc);
  return tmp(c$0, stackDelayRes$1)
};
Cont$func$int_of_char$sorting$_mls_L0_155_188$$ctor = function Cont$func$int_of_char$sorting$_mls_L0_155_188$$ctor(c$0, stackDelayRes$1) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$int_of_char$sorting$_mls_L0_155_188$1.class(pc);
    return tmp(c$0, stackDelayRes$1)
  }
};
Cont$func$int_of_char$sorting$_mls_L0_155_188$1 = function Cont$func$int_of_char$sorting$_mls_L0_155_188$(pc1) {
  return (c$01, stackDelayRes$11) => {
    return new Cont$func$int_of_char$sorting$_mls_L0_155_188$.class(pc1)(c$01, stackDelayRes$11);
  }
};
Cont$func$int_of_char$sorting$_mls_L0_155_188$1.class = class Cont$func$int_of_char$sorting$_mls_L0_155_188$ extends runtime.FunctionContFrame.class {
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
    if (this.pc === 0) {
      this.stackDelayRes$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 0) {
        this.pc = 1;
        continue contLoop;
      } else if (this.pc === 1) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.c$0.codePointAt(0))
      }
      break;
    }
  }
  toString() { return "Cont$func$int_of_char$sorting$_mls_L0_155_188$(" + globalThis.Predef.render(this.pc) + ")"; }
};
int_of_char = function int_of_char(c) {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$int_of_char$sorting$_mls_L0_155_188$$(c, stackDelayRes, 0);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return runtime.safeCall(c.codePointAt(0))
};
Cont$func$compareList$sorting$_mls_L0_217_484$$ = function Cont$func$compareList$sorting$_mls_L0_217_484$$(xs$0, ys$1, param0$2, param1$3, x$4, xs_$5, param0$6, param1$7, y$8, ys_$9, scrut$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, tmp$19, stackDelayRes$20, pc) {
  let tmp;
  tmp = new Cont$func$compareList$sorting$_mls_L0_217_484$1.class(pc);
  return tmp(xs$0, ys$1, param0$2, param1$3, x$4, xs_$5, param0$6, param1$7, y$8, ys_$9, scrut$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, tmp$19, stackDelayRes$20)
};
Cont$func$compareList$sorting$_mls_L0_217_484$$ctor = function Cont$func$compareList$sorting$_mls_L0_217_484$$ctor(xs$0, ys$1, param0$2, param1$3, x$4, xs_$5, param0$6, param1$7, y$8, ys_$9, scrut$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, tmp$19, stackDelayRes$20) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$compareList$sorting$_mls_L0_217_484$1.class(pc);
    return tmp(xs$0, ys$1, param0$2, param1$3, x$4, xs_$5, param0$6, param1$7, y$8, ys_$9, scrut$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, tmp$19, stackDelayRes$20)
  }
};
Cont$func$compareList$sorting$_mls_L0_217_484$1 = function Cont$func$compareList$sorting$_mls_L0_217_484$(pc1) {
  return (xs$01, ys$11, param0$21, param1$31, x$41, xs_$51, param0$61, param1$71, y$81, ys_$91, scrut$101, scrut$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, curDepth$171, tmp$181, tmp$191, stackDelayRes$201) => {
    return new Cont$func$compareList$sorting$_mls_L0_217_484$.class(pc1)(xs$01, ys$11, param0$21, param1$31, x$41, xs_$51, param0$61, param1$71, y$81, ys_$91, scrut$101, scrut$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, curDepth$171, tmp$181, tmp$191, stackDelayRes$201);
  }
};
Cont$func$compareList$sorting$_mls_L0_217_484$1.class = class Cont$func$compareList$sorting$_mls_L0_217_484$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (xs$0, ys$1, param0$2, param1$3, x$4, xs_$5, param0$6, param1$7, y$8, ys_$9, scrut$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, curDepth$17, tmp$18, tmp$19, stackDelayRes$20) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.xs$0 = xs$0;
      this.ys$1 = ys$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.x$4 = x$4;
      this.xs_$5 = xs_$5;
      this.param0$6 = param0$6;
      this.param1$7 = param1$7;
      this.y$8 = y$8;
      this.ys_$9 = ys_$9;
      this.scrut$10 = scrut$10;
      this.scrut$11 = scrut$11;
      this.tmp$12 = tmp$12;
      this.tmp$13 = tmp$13;
      this.tmp$14 = tmp$14;
      this.tmp$15 = tmp$15;
      this.tmp$16 = tmp$16;
      this.curDepth$17 = curDepth$17;
      this.tmp$18 = tmp$18;
      this.tmp$19 = tmp$19;
      this.stackDelayRes$20 = stackDelayRes$20;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 2) {
      this.stackDelayRes$20 = value$;
    } else if (this.pc === 9) {
      this.tmp$19 = value$;
    } else if (this.pc === 8) {
      this.tmp$18 = value$;
    } else if (this.pc === 4) {
      this.tmp$12 = value$;
    } else if (this.pc === 5) {
      this.tmp$13 = value$;
    } else if (this.pc === 6) {
      this.tmp$14 = value$;
    } else if (this.pc === 7) {
      this.tmp$15 = value$;
    } else if (this.pc === 3) {
      this.tmp$16 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 2) {
        if (this.xs$0 instanceof NofibPrelude.Nil.class) {
          if (this.ys$1 instanceof NofibPrelude.Nil.class) {
            return EQ1
          } else if (this.ys$1 instanceof NofibPrelude.Cons.class) {
            this.param0$6 = this.ys$1.head;
            this.param1$7 = this.ys$1.tail;
            return LT1;
            this.pc = 10;
            continue contLoop;
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.tmp$16 = new globalThis.Error("match error");
            if (this.tmp$16 instanceof runtime.EffectSig.class) {
              this.pc = 3;
              this.tmp$16.contTrace.last.next = this;
              this.tmp$16.contTrace.last = this;
              return this.tmp$16
            }
            this.pc = 3;
            continue contLoop;
          }
          this.pc = 10;
          continue contLoop;
        } else if (this.xs$0 instanceof NofibPrelude.Cons.class) {
          this.param0$2 = this.xs$0.head;
          this.param1$3 = this.xs$0.tail;
          this.x$4 = this.param0$2;
          this.xs_$5 = this.param1$3;
          if (this.ys$1 instanceof NofibPrelude.Nil.class) {
            return GT1
          } else if (this.ys$1 instanceof NofibPrelude.Cons.class) {
            this.param0$6 = this.ys$1.head;
            this.param1$7 = this.ys$1.tail;
            this.y$8 = this.param0$6;
            this.ys_$9 = this.param1$7;
            this.pc = 15;
            continue contLoop;
            this.pc = 10;
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
          this.pc = 10;
          continue contLoop;
          this.pc = 10;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$19 = new globalThis.Error("match error");
          if (this.tmp$19 instanceof runtime.EffectSig.class) {
            this.pc = 9;
            this.tmp$19.contTrace.last.next = this;
            this.tmp$19.contTrace.last = this;
            return this.tmp$19
          }
          this.pc = 9;
          continue contLoop;
        }
        this.pc = 10;
        continue contLoop;
      } else if (this.pc === 10) {
        break contLoop;
      } else if (this.pc === 9) {
        this.tmp$19 = runtime.resetDepth(this.tmp$19, this.curDepth$17);
        throw this.tmp$19;
      } else if (this.pc === 8) {
        this.tmp$18 = runtime.resetDepth(this.tmp$18, this.curDepth$17);
        throw this.tmp$18;
      } else if (this.pc === 15) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$12 = NofibPrelude.int_of_char(this.x$4);
        if (this.tmp$12 instanceof runtime.EffectSig.class) {
          this.pc = 4;
          this.tmp$12.contTrace.last.next = this;
          this.tmp$12.contTrace.last = this;
          return this.tmp$12
        }
        this.pc = 4;
        continue contLoop;
      } else if (this.pc === 4) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$17);
        this.pc = 14;
        continue contLoop;
      } else if (this.pc === 14) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$13 = NofibPrelude.int_of_char(this.y$8);
        if (this.tmp$13 instanceof runtime.EffectSig.class) {
          this.pc = 5;
          this.tmp$13.contTrace.last.next = this;
          this.tmp$13.contTrace.last = this;
          return this.tmp$13
        }
        this.pc = 5;
        continue contLoop;
      } else if (this.pc === 5) {
        this.tmp$13 = runtime.resetDepth(this.tmp$13, this.curDepth$17);
        this.scrut$11 = this.tmp$12 === this.tmp$13;
        if (this.scrut$11 === true) {
          this.pc = 11;
          continue contLoop;
        } else {
          this.pc = 13;
          continue contLoop;
        }
        this.pc = 10;
        continue contLoop;
      } else if (this.pc === 13) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$14 = NofibPrelude.int_of_char(this.x$4);
        if (this.tmp$14 instanceof runtime.EffectSig.class) {
          this.pc = 6;
          this.tmp$14.contTrace.last.next = this;
          this.tmp$14.contTrace.last = this;
          return this.tmp$14
        }
        this.pc = 6;
        continue contLoop;
      } else if (this.pc === 6) {
        this.tmp$14 = runtime.resetDepth(this.tmp$14, this.curDepth$17);
        this.pc = 12;
        continue contLoop;
      } else if (this.pc === 12) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$15 = NofibPrelude.int_of_char(this.y$8);
        if (this.tmp$15 instanceof runtime.EffectSig.class) {
          this.pc = 7;
          this.tmp$15.contTrace.last.next = this;
          this.tmp$15.contTrace.last = this;
          return this.tmp$15
        }
        this.pc = 7;
        continue contLoop;
      } else if (this.pc === 7) {
        this.tmp$15 = runtime.resetDepth(this.tmp$15, this.curDepth$17);
        this.scrut$10 = this.tmp$14 < this.tmp$15;
        if (this.scrut$10 === true) {
          return LT1
        } else {
          return GT1
        }
        this.pc = 10;
        continue contLoop;
      } else if (this.pc === 11) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return compareList(this.xs_$5, this.ys_$9)
      } else if (this.pc === 3) {
        this.tmp$16 = runtime.resetDepth(this.tmp$16, this.curDepth$17);
        throw this.tmp$16;
      }
      break;
    }
  }
  toString() { return "Cont$func$compareList$sorting$_mls_L0_217_484$(" + globalThis.Predef.render(this.pc) + ")"; }
};
compareList = function compareList(xs, ys) {
  let param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$compareList$sorting$_mls_L0_217_484$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, stackDelayRes, 2);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (xs instanceof NofibPrelude.Nil.class) {
    if (ys instanceof NofibPrelude.Nil.class) {
      return EQ1
    } else if (ys instanceof NofibPrelude.Cons.class) {
      param01 = ys.head;
      param11 = ys.tail;
      return LT1
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = new globalThis.Error("match error");
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.contTrace.last.next = Cont$func$compareList$sorting$_mls_L0_217_484$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, stackDelayRes, 3);
        tmp4.contTrace.last = tmp4.contTrace.last.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      throw tmp4;
    }
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs_ = param1;
    if (ys instanceof NofibPrelude.Nil.class) {
      return GT1
    } else if (ys instanceof NofibPrelude.Cons.class) {
      param01 = ys.head;
      param11 = ys.tail;
      y = param01;
      ys_ = param11;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = NofibPrelude.int_of_char(x);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$compareList$sorting$_mls_L0_217_484$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, stackDelayRes, 4);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = NofibPrelude.int_of_char(y);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = Cont$func$compareList$sorting$_mls_L0_217_484$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, stackDelayRes, 5);
        tmp1.contTrace.last = tmp1.contTrace.last.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      scrut1 = tmp === tmp1;
      if (scrut1 === true) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return compareList(xs_, ys_)
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp2 = NofibPrelude.int_of_char(x);
        if (tmp2 instanceof runtime.EffectSig.class) {
          tmp2.contTrace.last.next = Cont$func$compareList$sorting$_mls_L0_217_484$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, stackDelayRes, 6);
          tmp2.contTrace.last = tmp2.contTrace.last.next;
          return tmp2
        }
        tmp2 = runtime.resetDepth(tmp2, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp3 = NofibPrelude.int_of_char(y);
        if (tmp3 instanceof runtime.EffectSig.class) {
          tmp3.contTrace.last.next = Cont$func$compareList$sorting$_mls_L0_217_484$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, stackDelayRes, 7);
          tmp3.contTrace.last = tmp3.contTrace.last.next;
          return tmp3
        }
        tmp3 = runtime.resetDepth(tmp3, curDepth);
        scrut = tmp2 < tmp3;
        if (scrut === true) {
          return LT1
        } else {
          return GT1
        }
      }
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp5 = new globalThis.Error("match error");
      if (tmp5 instanceof runtime.EffectSig.class) {
        tmp5.contTrace.last.next = Cont$func$compareList$sorting$_mls_L0_217_484$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, stackDelayRes, 8);
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
      tmp6.contTrace.last.next = Cont$func$compareList$sorting$_mls_L0_217_484$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, tmp6, stackDelayRes, 9);
      tmp6.contTrace.last = tmp6.contTrace.last.next;
      return tmp6
    }
    tmp6 = runtime.resetDepth(tmp6, curDepth);
    throw tmp6;
  }
};
Cont$func$gtList$sorting$_mls_L0_490_528$$ = function Cont$func$gtList$sorting$_mls_L0_490_528$$(a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$gtList$sorting$_mls_L0_490_528$1.class(pc);
  return tmp(a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4)
};
Cont$func$gtList$sorting$_mls_L0_490_528$$ctor = function Cont$func$gtList$sorting$_mls_L0_490_528$$ctor(a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$gtList$sorting$_mls_L0_490_528$1.class(pc);
    return tmp(a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$gtList$sorting$_mls_L0_490_528$1 = function Cont$func$gtList$sorting$_mls_L0_490_528$(pc1) {
  return (a$01, b$11, scrut$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$gtList$sorting$_mls_L0_490_528$.class(pc1)(a$01, b$11, scrut$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$gtList$sorting$_mls_L0_490_528$1.class = class Cont$func$gtList$sorting$_mls_L0_490_528$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.a$0 = a$0;
      this.b$1 = b$1;
      this.scrut$2 = scrut$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 16) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 17) {
      this.scrut$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 16) {
        this.pc = 19;
        continue contLoop;
      } else if (this.pc === 19) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$2 = compareList(this.a$0, this.b$1);
        if (this.scrut$2 instanceof runtime.EffectSig.class) {
          this.pc = 17;
          this.scrut$2.contTrace.last.next = this;
          this.scrut$2.contTrace.last = this;
          return this.scrut$2
        }
        this.pc = 17;
        continue contLoop;
      } else if (this.pc === 17) {
        this.scrut$2 = runtime.resetDepth(this.scrut$2, this.curDepth$3);
        if (this.scrut$2 instanceof GT1.class) {
          return true
        } else {
          return false
        }
        this.pc = 18;
        continue contLoop;
      } else if (this.pc === 18) {
        break contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$gtList$sorting$_mls_L0_490_528$(" + globalThis.Predef.render(this.pc) + ")"; }
};
gtList = function gtList(a, b) {
  let scrut, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$gtList$sorting$_mls_L0_490_528$$(a, b, scrut, curDepth, stackDelayRes, 16);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  scrut = compareList(a, b);
  if (scrut instanceof runtime.EffectSig.class) {
    scrut.contTrace.last.next = Cont$func$gtList$sorting$_mls_L0_490_528$$(a, b, scrut, curDepth, stackDelayRes, 17);
    scrut.contTrace.last = scrut.contTrace.last.next;
    return scrut
  }
  scrut = runtime.resetDepth(scrut, curDepth);
  if (scrut instanceof GT1.class) {
    return true
  } else {
    return false
  }
};
Cont$func$leList$sorting$_mls_L0_534_566$$ = function Cont$func$leList$sorting$_mls_L0_534_566$$(a$0, b$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$leList$sorting$_mls_L0_534_566$1.class(pc);
  return tmp(a$0, b$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$leList$sorting$_mls_L0_534_566$$ctor = function Cont$func$leList$sorting$_mls_L0_534_566$$ctor(a$0, b$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$leList$sorting$_mls_L0_534_566$1.class(pc);
    return tmp(a$0, b$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$leList$sorting$_mls_L0_534_566$1 = function Cont$func$leList$sorting$_mls_L0_534_566$(pc1) {
  return (a$01, b$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$leList$sorting$_mls_L0_534_566$.class(pc1)(a$01, b$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$leList$sorting$_mls_L0_534_566$1.class = class Cont$func$leList$sorting$_mls_L0_534_566$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (a$0, b$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.a$0 = a$0;
      this.b$1 = b$1;
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
        return BenchmarkPrelude.not(this.tmp$2)
      } else if (this.pc === 23) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = gtList(this.a$0, this.b$1);
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
  toString() { return "Cont$func$leList$sorting$_mls_L0_534_566$(" + globalThis.Predef.render(this.pc) + ")"; }
};
leList = function leList(a, b) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$leList$sorting$_mls_L0_534_566$$(a, b, tmp, curDepth, stackDelayRes, 20);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = gtList(a, b);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$leList$sorting$_mls_L0_534_566$$(a, b, tmp, curDepth, stackDelayRes, 21);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return BenchmarkPrelude.not(tmp)
};
Cont$func$ltList$sorting$_mls_L0_572_610$$ = function Cont$func$ltList$sorting$_mls_L0_572_610$$(a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$ltList$sorting$_mls_L0_572_610$1.class(pc);
  return tmp(a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4)
};
Cont$func$ltList$sorting$_mls_L0_572_610$$ctor = function Cont$func$ltList$sorting$_mls_L0_572_610$$ctor(a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$ltList$sorting$_mls_L0_572_610$1.class(pc);
    return tmp(a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$ltList$sorting$_mls_L0_572_610$1 = function Cont$func$ltList$sorting$_mls_L0_572_610$(pc1) {
  return (a$01, b$11, scrut$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$ltList$sorting$_mls_L0_572_610$.class(pc1)(a$01, b$11, scrut$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$ltList$sorting$_mls_L0_572_610$1.class = class Cont$func$ltList$sorting$_mls_L0_572_610$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.a$0 = a$0;
      this.b$1 = b$1;
      this.scrut$2 = scrut$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 24) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 25) {
      this.scrut$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 24) {
        this.pc = 27;
        continue contLoop;
      } else if (this.pc === 27) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$2 = compareList(this.a$0, this.b$1);
        if (this.scrut$2 instanceof runtime.EffectSig.class) {
          this.pc = 25;
          this.scrut$2.contTrace.last.next = this;
          this.scrut$2.contTrace.last = this;
          return this.scrut$2
        }
        this.pc = 25;
        continue contLoop;
      } else if (this.pc === 25) {
        this.scrut$2 = runtime.resetDepth(this.scrut$2, this.curDepth$3);
        if (this.scrut$2 instanceof LT1.class) {
          return true
        } else {
          return false
        }
        this.pc = 26;
        continue contLoop;
      } else if (this.pc === 26) {
        break contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$ltList$sorting$_mls_L0_572_610$(" + globalThis.Predef.render(this.pc) + ")"; }
};
ltList = function ltList(a, b) {
  let scrut, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$ltList$sorting$_mls_L0_572_610$$(a, b, scrut, curDepth, stackDelayRes, 24);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  scrut = compareList(a, b);
  if (scrut instanceof runtime.EffectSig.class) {
    scrut.contTrace.last.next = Cont$func$ltList$sorting$_mls_L0_572_610$$(a, b, scrut, curDepth, stackDelayRes, 25);
    scrut.contTrace.last = scrut.contTrace.last.next;
    return scrut
  }
  scrut = runtime.resetDepth(scrut, curDepth);
  if (scrut instanceof LT1.class) {
    return true
  } else {
    return false
  }
};
Cont$func$geList$sorting$_mls_L0_616_648$$ = function Cont$func$geList$sorting$_mls_L0_616_648$$(a$0, b$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$geList$sorting$_mls_L0_616_648$1.class(pc);
  return tmp(a$0, b$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$geList$sorting$_mls_L0_616_648$$ctor = function Cont$func$geList$sorting$_mls_L0_616_648$$ctor(a$0, b$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$geList$sorting$_mls_L0_616_648$1.class(pc);
    return tmp(a$0, b$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$geList$sorting$_mls_L0_616_648$1 = function Cont$func$geList$sorting$_mls_L0_616_648$(pc1) {
  return (a$01, b$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$geList$sorting$_mls_L0_616_648$.class(pc1)(a$01, b$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$geList$sorting$_mls_L0_616_648$1.class = class Cont$func$geList$sorting$_mls_L0_616_648$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (a$0, b$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.a$0 = a$0;
      this.b$1 = b$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 28) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 29) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 28) {
        this.pc = 31;
        continue contLoop;
      } else if (this.pc === 30) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return BenchmarkPrelude.not(this.tmp$2)
      } else if (this.pc === 31) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = NofibPrelude.ltList(this.a$0, this.b$1);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 29;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 29;
        continue contLoop;
      } else if (this.pc === 29) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        this.pc = 30;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$geList$sorting$_mls_L0_616_648$(" + globalThis.Predef.render(this.pc) + ")"; }
};
geList = function geList(a, b) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$geList$sorting$_mls_L0_616_648$$(a, b, tmp, curDepth, stackDelayRes, 28);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = NofibPrelude.ltList(a, b);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$geList$sorting$_mls_L0_616_648$$(a, b, tmp, curDepth, stackDelayRes, 29);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return BenchmarkPrelude.not(tmp)
};
Cont$func$eqList$sorting$_mls_L0_654_692$$ = function Cont$func$eqList$sorting$_mls_L0_654_692$$(a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$eqList$sorting$_mls_L0_654_692$1.class(pc);
  return tmp(a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4)
};
Cont$func$eqList$sorting$_mls_L0_654_692$$ctor = function Cont$func$eqList$sorting$_mls_L0_654_692$$ctor(a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$eqList$sorting$_mls_L0_654_692$1.class(pc);
    return tmp(a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$eqList$sorting$_mls_L0_654_692$1 = function Cont$func$eqList$sorting$_mls_L0_654_692$(pc1) {
  return (a$01, b$11, scrut$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$eqList$sorting$_mls_L0_654_692$.class(pc1)(a$01, b$11, scrut$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$eqList$sorting$_mls_L0_654_692$1.class = class Cont$func$eqList$sorting$_mls_L0_654_692$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (a$0, b$1, scrut$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.a$0 = a$0;
      this.b$1 = b$1;
      this.scrut$2 = scrut$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 32) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 33) {
      this.scrut$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 32) {
        this.pc = 35;
        continue contLoop;
      } else if (this.pc === 35) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$2 = compareList(this.a$0, this.b$1);
        if (this.scrut$2 instanceof runtime.EffectSig.class) {
          this.pc = 33;
          this.scrut$2.contTrace.last.next = this;
          this.scrut$2.contTrace.last = this;
          return this.scrut$2
        }
        this.pc = 33;
        continue contLoop;
      } else if (this.pc === 33) {
        this.scrut$2 = runtime.resetDepth(this.scrut$2, this.curDepth$3);
        if (this.scrut$2 instanceof EQ1.class) {
          return true
        } else {
          return false
        }
        this.pc = 34;
        continue contLoop;
      } else if (this.pc === 34) {
        break contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$eqList$sorting$_mls_L0_654_692$(" + globalThis.Predef.render(this.pc) + ")"; }
};
eqList = function eqList(a, b) {
  let scrut, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$eqList$sorting$_mls_L0_654_692$$(a, b, scrut, curDepth, stackDelayRes, 32);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  scrut = compareList(a, b);
  if (scrut instanceof runtime.EffectSig.class) {
    scrut.contTrace.last.next = Cont$func$eqList$sorting$_mls_L0_654_692$$(a, b, scrut, curDepth, stackDelayRes, 33);
    scrut.contTrace.last = scrut.contTrace.last.next;
    return scrut
  }
  scrut = runtime.resetDepth(scrut, curDepth);
  if (scrut instanceof EQ1.class) {
    return true
  } else {
    return false
  }
};
Cont$func$prependToAll$sorting$_mls_L0_698_796$$ = function Cont$func$prependToAll$sorting$_mls_L0_698_796$$(sep$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10, pc) {
  let tmp;
  tmp = new Cont$func$prependToAll$sorting$_mls_L0_698_796$1.class(pc);
  return tmp(sep$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
};
Cont$func$prependToAll$sorting$_mls_L0_698_796$$ctor = function Cont$func$prependToAll$sorting$_mls_L0_698_796$$ctor(sep$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$prependToAll$sorting$_mls_L0_698_796$1.class(pc);
    return tmp(sep$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
  }
};
Cont$func$prependToAll$sorting$_mls_L0_698_796$1 = function Cont$func$prependToAll$sorting$_mls_L0_698_796$(pc1) {
  return (sep$01, xs$11, param0$21, param1$31, x$41, xs_$51, tmp$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101) => {
    return new Cont$func$prependToAll$sorting$_mls_L0_698_796$.class(pc1)(sep$01, xs$11, param0$21, param1$31, x$41, xs_$51, tmp$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101);
  }
};
Cont$func$prependToAll$sorting$_mls_L0_698_796$1.class = class Cont$func$prependToAll$sorting$_mls_L0_698_796$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (sep$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.sep$0 = sep$0;
      this.xs$1 = xs$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.x$4 = x$4;
      this.xs_$5 = xs_$5;
      this.tmp$6 = tmp$6;
      this.tmp$7 = tmp$7;
      this.curDepth$8 = curDepth$8;
      this.tmp$9 = tmp$9;
      this.stackDelayRes$10 = stackDelayRes$10;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 36) {
      this.stackDelayRes$10 = value$;
    } else if (this.pc === 39) {
      this.tmp$9 = value$;
    } else if (this.pc === 37) {
      this.tmp$6 = value$;
    } else if (this.pc === 38) {
      this.tmp$7 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 36) {
        if (this.xs$1 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (this.xs$1 instanceof NofibPrelude.Cons.class) {
          this.param0$2 = this.xs$1.head;
          this.param1$3 = this.xs$1.tail;
          this.x$4 = this.param0$2;
          this.xs_$5 = this.param1$3;
          this.pc = 43;
          continue contLoop;
          this.pc = 40;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$9 = new globalThis.Error("match error");
          if (this.tmp$9 instanceof runtime.EffectSig.class) {
            this.pc = 39;
            this.tmp$9.contTrace.last.next = this;
            this.tmp$9.contTrace.last = this;
            return this.tmp$9
          }
          this.pc = 39;
          continue contLoop;
        }
        this.pc = 40;
        continue contLoop;
      } else if (this.pc === 40) {
        break contLoop;
      } else if (this.pc === 39) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$8);
        throw this.tmp$9;
      } else if (this.pc === 41) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.sep$0, this.tmp$7)
      } else if (this.pc === 42) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = NofibPrelude.Cons(this.x$4, this.tmp$6);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 38;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 38;
        continue contLoop;
      } else if (this.pc === 43) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = prependToAll(this.sep$0, this.xs_$5);
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 37;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 37;
        continue contLoop;
      } else if (this.pc === 37) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$8);
        this.pc = 42;
        continue contLoop;
      } else if (this.pc === 38) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$8);
        this.pc = 41;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$prependToAll$sorting$_mls_L0_698_796$(" + globalThis.Predef.render(this.pc) + ")"; }
};
prependToAll = function prependToAll(sep, xs) {
  let param0, param1, x, xs_, tmp, tmp1, curDepth, tmp2, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$prependToAll$sorting$_mls_L0_698_796$$(sep, xs, param0, param1, x, xs_, tmp, tmp1, curDepth, tmp2, stackDelayRes, 36);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (xs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs_ = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = prependToAll(sep, xs_);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$prependToAll$sorting$_mls_L0_698_796$$(sep, xs, param0, param1, x, xs_, tmp, tmp1, curDepth, tmp2, stackDelayRes, 37);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = NofibPrelude.Cons(x, tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$prependToAll$sorting$_mls_L0_698_796$$(sep, xs, param0, param1, x, xs_, tmp, tmp1, curDepth, tmp2, stackDelayRes, 38);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.Cons(sep, tmp1)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = new globalThis.Error("match error");
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$prependToAll$sorting$_mls_L0_698_796$$(sep, xs, param0, param1, x, xs_, tmp, tmp1, curDepth, tmp2, stackDelayRes, 39);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    throw tmp2;
  }
};
Cont$func$intersperse$sorting$_mls_L0_802_892$$ = function Cont$func$intersperse$sorting$_mls_L0_802_892$$(sep$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9, pc) {
  let tmp;
  tmp = new Cont$func$intersperse$sorting$_mls_L0_802_892$1.class(pc);
  return tmp(sep$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9)
};
Cont$func$intersperse$sorting$_mls_L0_802_892$$ctor = function Cont$func$intersperse$sorting$_mls_L0_802_892$$ctor(sep$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$intersperse$sorting$_mls_L0_802_892$1.class(pc);
    return tmp(sep$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9)
  }
};
Cont$func$intersperse$sorting$_mls_L0_802_892$1 = function Cont$func$intersperse$sorting$_mls_L0_802_892$(pc1) {
  return (sep$01, xs$11, param0$21, param1$31, x$41, xs_$51, tmp$61, curDepth$71, tmp$81, stackDelayRes$91) => {
    return new Cont$func$intersperse$sorting$_mls_L0_802_892$.class(pc1)(sep$01, xs$11, param0$21, param1$31, x$41, xs_$51, tmp$61, curDepth$71, tmp$81, stackDelayRes$91);
  }
};
Cont$func$intersperse$sorting$_mls_L0_802_892$1.class = class Cont$func$intersperse$sorting$_mls_L0_802_892$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (sep$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, curDepth$7, tmp$8, stackDelayRes$9) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.sep$0 = sep$0;
      this.xs$1 = xs$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.x$4 = x$4;
      this.xs_$5 = xs_$5;
      this.tmp$6 = tmp$6;
      this.curDepth$7 = curDepth$7;
      this.tmp$8 = tmp$8;
      this.stackDelayRes$9 = stackDelayRes$9;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 44) {
      this.stackDelayRes$9 = value$;
    } else if (this.pc === 46) {
      this.tmp$8 = value$;
    } else if (this.pc === 45) {
      this.tmp$6 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 44) {
        if (this.xs$1 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (this.xs$1 instanceof NofibPrelude.Cons.class) {
          this.param0$2 = this.xs$1.head;
          this.param1$3 = this.xs$1.tail;
          this.x$4 = this.param0$2;
          this.xs_$5 = this.param1$3;
          this.pc = 49;
          continue contLoop;
          this.pc = 47;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$8 = new globalThis.Error("match error");
          if (this.tmp$8 instanceof runtime.EffectSig.class) {
            this.pc = 46;
            this.tmp$8.contTrace.last.next = this;
            this.tmp$8.contTrace.last = this;
            return this.tmp$8
          }
          this.pc = 46;
          continue contLoop;
        }
        this.pc = 47;
        continue contLoop;
      } else if (this.pc === 47) {
        break contLoop;
      } else if (this.pc === 46) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$7);
        throw this.tmp$8;
      } else if (this.pc === 48) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.x$4, this.tmp$6)
      } else if (this.pc === 49) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = prependToAll(this.sep$0, this.xs_$5);
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 45;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 45;
        continue contLoop;
      } else if (this.pc === 45) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$7);
        this.pc = 48;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$intersperse$sorting$_mls_L0_802_892$(" + globalThis.Predef.render(this.pc) + ")"; }
};
intersperse = function intersperse(sep, xs) {
  let param0, param1, x, xs_, tmp, curDepth, tmp1, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$intersperse$sorting$_mls_L0_802_892$$(sep, xs, param0, param1, x, xs_, tmp, curDepth, tmp1, stackDelayRes, 44);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (xs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs_ = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = prependToAll(sep, xs_);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$intersperse$sorting$_mls_L0_802_892$$(sep, xs, param0, param1, x, xs_, tmp, curDepth, tmp1, stackDelayRes, 45);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.Cons(x, tmp)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = new globalThis.Error("match error");
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$intersperse$sorting$_mls_L0_802_892$$(sep, xs, param0, param1, x, xs_, tmp, curDepth, tmp1, stackDelayRes, 46);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    throw tmp1;
  }
};
Cont$func$lines$sorting$_mls_L0_898_1060$$ = function Cont$func$lines$sorting$_mls_L0_898_1060$$(s$0, scrut$1, first1$2, first0$3, l$4, s_$5, tt$6, param0$7, param1$8, s__$9, tmp$10, curDepth$11, tmp$12, tmp$13, stackDelayRes$14, pc) {
  let tmp;
  tmp = new Cont$func$lines$sorting$_mls_L0_898_1060$1.class(pc);
  return tmp(s$0, scrut$1, first1$2, first0$3, l$4, s_$5, tt$6, param0$7, param1$8, s__$9, tmp$10, curDepth$11, tmp$12, tmp$13, stackDelayRes$14)
};
Cont$func$lines$sorting$_mls_L0_898_1060$$ctor = function Cont$func$lines$sorting$_mls_L0_898_1060$$ctor(s$0, scrut$1, first1$2, first0$3, l$4, s_$5, tt$6, param0$7, param1$8, s__$9, tmp$10, curDepth$11, tmp$12, tmp$13, stackDelayRes$14) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lines$sorting$_mls_L0_898_1060$1.class(pc);
    return tmp(s$0, scrut$1, first1$2, first0$3, l$4, s_$5, tt$6, param0$7, param1$8, s__$9, tmp$10, curDepth$11, tmp$12, tmp$13, stackDelayRes$14)
  }
};
Cont$func$lines$sorting$_mls_L0_898_1060$1 = function Cont$func$lines$sorting$_mls_L0_898_1060$(pc1) {
  return (s$01, scrut$11, first1$21, first0$31, l$41, s_$51, tt$61, param0$71, param1$81, s__$91, tmp$101, curDepth$111, tmp$121, tmp$131, stackDelayRes$141) => {
    return new Cont$func$lines$sorting$_mls_L0_898_1060$.class(pc1)(s$01, scrut$11, first1$21, first0$31, l$41, s_$51, tt$61, param0$71, param1$81, s__$91, tmp$101, curDepth$111, tmp$121, tmp$131, stackDelayRes$141);
  }
};
Cont$func$lines$sorting$_mls_L0_898_1060$1.class = class Cont$func$lines$sorting$_mls_L0_898_1060$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (s$0, scrut$1, first1$2, first0$3, l$4, s_$5, tt$6, param0$7, param1$8, s__$9, tmp$10, curDepth$11, tmp$12, tmp$13, stackDelayRes$14) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.s$0 = s$0;
      this.scrut$1 = scrut$1;
      this.first1$2 = first1$2;
      this.first0$3 = first0$3;
      this.l$4 = l$4;
      this.s_$5 = s_$5;
      this.tt$6 = tt$6;
      this.param0$7 = param0$7;
      this.param1$8 = param1$8;
      this.s__$9 = s__$9;
      this.tmp$10 = tmp$10;
      this.curDepth$11 = curDepth$11;
      this.tmp$12 = tmp$12;
      this.tmp$13 = tmp$13;
      this.stackDelayRes$14 = stackDelayRes$14;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 50) {
      this.stackDelayRes$14 = value$;
    } else if (this.pc === 51) {
      this.scrut$1 = value$;
    } else if (this.pc === 54) {
      this.tmp$13 = value$;
    } else if (this.pc === 53) {
      this.tmp$12 = value$;
    } else if (this.pc === 52) {
      this.tmp$10 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 50) {
        if (this.s$0 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else {
          this.pc = 59;
          continue contLoop;
        }
        this.pc = 55;
        continue contLoop;
      } else if (this.pc === 55) {
        break contLoop;
      } else if (this.pc === 59) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$1 = NofibPrelude.break_(lambda, this.s$0);
        if (this.scrut$1 instanceof runtime.EffectSig.class) {
          this.pc = 51;
          this.scrut$1.contTrace.last.next = this;
          this.scrut$1.contTrace.last = this;
          return this.scrut$1
        }
        this.pc = 51;
        continue contLoop;
      } else if (this.pc === 51) {
        this.scrut$1 = runtime.resetDepth(this.scrut$1, this.curDepth$11);
        if (globalThis.Array.isArray(this.scrut$1) && this.scrut$1.length === 2) {
          this.first0$3 = this.scrut$1[0];
          this.first1$2 = this.scrut$1[1];
          this.l$4 = this.first0$3;
          this.s_$5 = this.first1$2;
          if (this.s_$5 instanceof NofibPrelude.Nil.class) {
            this.tmp$10 = NofibPrelude.Nil;
            this.pc = 57;
            continue contLoop;
          } else if (this.s_$5 instanceof NofibPrelude.Cons.class) {
            this.param0$7 = this.s_$5.head;
            this.param1$8 = this.s_$5.tail;
            this.s__$9 = this.param1$8;
            this.pc = 58;
            continue contLoop;
            this.pc = 57;
            continue contLoop;
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.tmp$12 = new globalThis.Error("match error");
            if (this.tmp$12 instanceof runtime.EffectSig.class) {
              this.pc = 53;
              this.tmp$12.contTrace.last.next = this;
              this.tmp$12.contTrace.last = this;
              return this.tmp$12
            }
            this.pc = 53;
            continue contLoop;
          }
          this.pc = 57;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$13 = new globalThis.Error("match error");
          if (this.tmp$13 instanceof runtime.EffectSig.class) {
            this.pc = 54;
            this.tmp$13.contTrace.last.next = this;
            this.tmp$13.contTrace.last = this;
            return this.tmp$13
          }
          this.pc = 54;
          continue contLoop;
        }
        this.pc = 55;
        continue contLoop;
      } else if (this.pc === 54) {
        this.tmp$13 = runtime.resetDepth(this.tmp$13, this.curDepth$11);
        throw this.tmp$13;
      } else if (this.pc === 57) {
        this.tt$6 = this.tmp$10;
        this.pc = 56;
        continue contLoop;
      } else if (this.pc === 53) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$11);
        throw this.tmp$12;
      } else if (this.pc === 58) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$10 = lines(this.s__$9);
        if (this.tmp$10 instanceof runtime.EffectSig.class) {
          this.pc = 52;
          this.tmp$10.contTrace.last.next = this;
          this.tmp$10.contTrace.last = this;
          return this.tmp$10
        }
        this.pc = 52;
        continue contLoop;
      } else if (this.pc === 52) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$11);
        this.pc = 57;
        continue contLoop;
      } else if (this.pc === 56) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.l$4, this.tt$6)
      }
      break;
    }
  }
  toString() { return "Cont$func$lines$sorting$_mls_L0_898_1060$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda = (undefined, function (x) {
  return x === "\n"
});
lines = function lines(s) {
  let scrut, first1, first0, l, s_, tt, param0, param1, s__, tmp, curDepth, tmp1, tmp2, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lines$sorting$_mls_L0_898_1060$$(s, scrut, first1, first0, l, s_, tt, param0, param1, s__, tmp, curDepth, tmp1, tmp2, stackDelayRes, 50);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (s instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    scrut = NofibPrelude.break_(lambda, s);
    if (scrut instanceof runtime.EffectSig.class) {
      scrut.contTrace.last.next = Cont$func$lines$sorting$_mls_L0_898_1060$$(s, scrut, first1, first0, l, s_, tt, param0, param1, s__, tmp, curDepth, tmp1, tmp2, stackDelayRes, 51);
      scrut.contTrace.last = scrut.contTrace.last.next;
      return scrut
    }
    scrut = runtime.resetDepth(scrut, curDepth);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      l = first0;
      s_ = first1;
      if (s_ instanceof NofibPrelude.Nil.class) {
        tmp = NofibPrelude.Nil;
      } else if (s_ instanceof NofibPrelude.Cons.class) {
        param0 = s_.head;
        param1 = s_.tail;
        s__ = param1;
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp = lines(s__);
        if (tmp instanceof runtime.EffectSig.class) {
          tmp.contTrace.last.next = Cont$func$lines$sorting$_mls_L0_898_1060$$(s, scrut, first1, first0, l, s_, tt, param0, param1, s__, tmp, curDepth, tmp1, tmp2, stackDelayRes, 52);
          tmp.contTrace.last = tmp.contTrace.last.next;
          return tmp
        }
        tmp = runtime.resetDepth(tmp, curDepth);
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp1 = new globalThis.Error("match error");
        if (tmp1 instanceof runtime.EffectSig.class) {
          tmp1.contTrace.last.next = Cont$func$lines$sorting$_mls_L0_898_1060$$(s, scrut, first1, first0, l, s_, tt, param0, param1, s__, tmp, curDepth, tmp1, tmp2, stackDelayRes, 53);
          tmp1.contTrace.last = tmp1.contTrace.last.next;
          return tmp1
        }
        tmp1 = runtime.resetDepth(tmp1, curDepth);
        throw tmp1;
      }
      tt = tmp;
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.Cons(l, tt)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = new globalThis.Error("match error");
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.contTrace.last.next = Cont$func$lines$sorting$_mls_L0_898_1060$$(s, scrut, first1, first0, l, s_, tt, param0, param1, s__, tmp, curDepth, tmp1, tmp2, stackDelayRes, 54);
        tmp2.contTrace.last = tmp2.contTrace.last.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      throw tmp2;
    }
  }
};
Cont$func$unlines$sorting$_mls_L0_1066_1120$$ = function Cont$func$unlines$sorting$_mls_L0_1066_1120$$(ls$0, tmp$1, curDepth$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$unlines$sorting$_mls_L0_1066_1120$1.class(pc);
  return tmp(ls$0, tmp$1, curDepth$2, stackDelayRes$3)
};
Cont$func$unlines$sorting$_mls_L0_1066_1120$$ctor = function Cont$func$unlines$sorting$_mls_L0_1066_1120$$ctor(ls$0, tmp$1, curDepth$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$unlines$sorting$_mls_L0_1066_1120$1.class(pc);
    return tmp(ls$0, tmp$1, curDepth$2, stackDelayRes$3)
  }
};
Cont$func$unlines$sorting$_mls_L0_1066_1120$1 = function Cont$func$unlines$sorting$_mls_L0_1066_1120$(pc1) {
  return (ls$01, tmp$11, curDepth$21, stackDelayRes$31) => {
    return new Cont$func$unlines$sorting$_mls_L0_1066_1120$.class(pc1)(ls$01, tmp$11, curDepth$21, stackDelayRes$31);
  }
};
Cont$func$unlines$sorting$_mls_L0_1066_1120$1.class = class Cont$func$unlines$sorting$_mls_L0_1066_1120$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (ls$0, tmp$1, curDepth$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.ls$0 = ls$0;
      this.tmp$1 = tmp$1;
      this.curDepth$2 = curDepth$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 60) {
      this.stackDelayRes$3 = value$;
    } else if (this.pc === 65) {
      this.tmp$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 60) {
        this.pc = 67;
        continue contLoop;
      } else if (this.pc === 66) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.concat(this.tmp$1)
      } else if (this.pc === 67) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = NofibPrelude.map(lambda1, this.ls$0);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 65;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 65;
        continue contLoop;
      } else if (this.pc === 65) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$2);
        this.pc = 66;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$unlines$sorting$_mls_L0_1066_1120$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$ = function Cont$func$lambda$$$(l$0, tmp$1, curDepth$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$6.class(pc);
  return tmp(l$0, tmp$1, curDepth$2, stackDelayRes$3)
};
Cont$func$lambda$$$ctor = function Cont$func$lambda$$$ctor(l$0, tmp$1, curDepth$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$6.class(pc);
    return tmp(l$0, tmp$1, curDepth$2, stackDelayRes$3)
  }
};
Cont$func$lambda$$6 = function Cont$func$lambda$$(pc1) {
  return (l$01, tmp$11, curDepth$21, stackDelayRes$31) => {
    return new Cont$func$lambda$$.class(pc1)(l$01, tmp$11, curDepth$21, stackDelayRes$31);
  }
};
Cont$func$lambda$$6.class = class Cont$func$lambda$$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (l$0, tmp$1, curDepth$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.l$0 = l$0;
      this.tmp$1 = tmp$1;
      this.curDepth$2 = curDepth$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 61) {
      this.stackDelayRes$3 = value$;
    } else if (this.pc === 62) {
      this.tmp$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 61) {
        this.pc = 64;
        continue contLoop;
      } else if (this.pc === 63) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.append(this.l$0, this.tmp$1)
      } else if (this.pc === 64) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = NofibPrelude.Cons("\n", NofibPrelude.Nil);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 62;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 62;
        continue contLoop;
      } else if (this.pc === 62) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$2);
        this.pc = 63;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda1 = (undefined, function (l) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$(l, tmp, curDepth, stackDelayRes, 61);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = NofibPrelude.Cons("\n", NofibPrelude.Nil);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$(l, tmp, curDepth, stackDelayRes, 62);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return NofibPrelude.append(l, tmp)
});
unlines = function unlines(ls) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$unlines$sorting$_mls_L0_1066_1120$$(ls, tmp, curDepth, stackDelayRes, 60);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = NofibPrelude.map(lambda1, ls);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$unlines$sorting$_mls_L0_1066_1120$$(ls, tmp, curDepth, stackDelayRes, 65);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return NofibPrelude.concat(tmp)
};
Cont$func$odd$sorting$_mls_L0_1126_1153$$ = function Cont$func$odd$sorting$_mls_L0_1126_1153$$(x$0, tmp$1, curDepth$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$odd$sorting$_mls_L0_1126_1153$1.class(pc);
  return tmp(x$0, tmp$1, curDepth$2, stackDelayRes$3)
};
Cont$func$odd$sorting$_mls_L0_1126_1153$$ctor = function Cont$func$odd$sorting$_mls_L0_1126_1153$$ctor(x$0, tmp$1, curDepth$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$odd$sorting$_mls_L0_1126_1153$1.class(pc);
    return tmp(x$0, tmp$1, curDepth$2, stackDelayRes$3)
  }
};
Cont$func$odd$sorting$_mls_L0_1126_1153$1 = function Cont$func$odd$sorting$_mls_L0_1126_1153$(pc1) {
  return (x$01, tmp$11, curDepth$21, stackDelayRes$31) => {
    return new Cont$func$odd$sorting$_mls_L0_1126_1153$.class(pc1)(x$01, tmp$11, curDepth$21, stackDelayRes$31);
  }
};
Cont$func$odd$sorting$_mls_L0_1126_1153$1.class = class Cont$func$odd$sorting$_mls_L0_1126_1153$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, tmp$1, curDepth$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$0 = x$0;
      this.tmp$1 = tmp$1;
      this.curDepth$2 = curDepth$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 68) {
      this.stackDelayRes$3 = value$;
    } else if (this.pc === 69) {
      this.tmp$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 68) {
        this.pc = 70;
        continue contLoop;
      } else if (this.pc === 70) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = NofibPrelude.intMod(this.x$0, 2);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 69;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 69;
        continue contLoop;
      } else if (this.pc === 69) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$2);
        return this.tmp$1 === 0
      }
      break;
    }
  }
  toString() { return "Cont$func$odd$sorting$_mls_L0_1126_1153$(" + globalThis.Predef.render(this.pc) + ")"; }
};
odd = function odd(x) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$odd$sorting$_mls_L0_1126_1153$$(x, tmp, curDepth, stackDelayRes, 68);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = NofibPrelude.intMod(x, 2);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$odd$sorting$_mls_L0_1126_1153$$(x, tmp, curDepth, stackDelayRes, 69);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  return tmp === 0
};
Cont$func$z_of_int$sorting$_mls_L0_1159_1193$$ = function Cont$func$z_of_int$sorting$_mls_L0_1159_1193$$(x$0, stackDelayRes$1, pc) {
  let tmp;
  tmp = new Cont$func$z_of_int$sorting$_mls_L0_1159_1193$1.class(pc);
  return tmp(x$0, stackDelayRes$1)
};
Cont$func$z_of_int$sorting$_mls_L0_1159_1193$$ctor = function Cont$func$z_of_int$sorting$_mls_L0_1159_1193$$ctor(x$0, stackDelayRes$1) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$z_of_int$sorting$_mls_L0_1159_1193$1.class(pc);
    return tmp(x$0, stackDelayRes$1)
  }
};
Cont$func$z_of_int$sorting$_mls_L0_1159_1193$1 = function Cont$func$z_of_int$sorting$_mls_L0_1159_1193$(pc1) {
  return (x$01, stackDelayRes$11) => {
    return new Cont$func$z_of_int$sorting$_mls_L0_1159_1193$.class(pc1)(x$01, stackDelayRes$11);
  }
};
Cont$func$z_of_int$sorting$_mls_L0_1159_1193$1.class = class Cont$func$z_of_int$sorting$_mls_L0_1159_1193$ extends runtime.FunctionContFrame.class {
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
    if (this.pc === 71) {
      this.stackDelayRes$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 71) {
        this.pc = 72;
        continue contLoop;
      } else if (this.pc === 72) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(globalThis.BigInt(this.x$0))
      }
      break;
    }
  }
  toString() { return "Cont$func$z_of_int$sorting$_mls_L0_1159_1193$(" + globalThis.Predef.render(this.pc) + ")"; }
};
z_of_int = function z_of_int(x) {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$z_of_int$sorting$_mls_L0_1159_1193$$(x, stackDelayRes, 71);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return runtime.safeCall(globalThis.BigInt(x))
};
Cont$func$hash$sorting$_mls_L0_1199_1303$$ = function Cont$func$hash$sorting$_mls_L0_1199_1303$$(str$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$hash$sorting$_mls_L0_1199_1303$1.class(pc);
  return tmp(str$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$hash$sorting$_mls_L0_1199_1303$$ctor = function Cont$func$hash$sorting$_mls_L0_1199_1303$$ctor(str$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$hash$sorting$_mls_L0_1199_1303$1.class(pc);
    return tmp(str$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$hash$sorting$_mls_L0_1199_1303$1 = function Cont$func$hash$sorting$_mls_L0_1199_1303$(pc1) {
  return (str$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$hash$sorting$_mls_L0_1199_1303$.class(pc1)(str$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$hash$sorting$_mls_L0_1199_1303$1.class = class Cont$func$hash$sorting$_mls_L0_1199_1303$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (str$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.str$0 = str$0;
      this.tmp$1 = tmp$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 73) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 81) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 73) {
        this.tmp$1 = lambda2;
        this.pc = 83;
        continue contLoop;
      } else if (this.pc === 82) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.foldl(this.tmp$1, this.tmp$2, this.str$0)
      } else if (this.pc === 83) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = z_of_int(0);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 81;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 81;
        continue contLoop;
      } else if (this.pc === 81) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        this.pc = 82;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$hash$sorting$_mls_L0_1199_1303$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$1 = function Cont$func$lambda$$$(acc$0, c$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$7.class(pc);
  return tmp(acc$0, c$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7)
};
Cont$func$lambda$$$ctor1 = function Cont$func$lambda$$$ctor(acc$0, c$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$7.class(pc);
    return tmp(acc$0, c$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7)
  }
};
Cont$func$lambda$$7 = function Cont$func$lambda$$(pc1) {
  return (acc$01, c$11, tmp$21, tmp$31, tmp$41, tmp$51, curDepth$61, stackDelayRes$71) => {
    return new Cont$func$lambda$$.class(pc1)(acc$01, c$11, tmp$21, tmp$31, tmp$41, tmp$51, curDepth$61, stackDelayRes$71);
  }
};
Cont$func$lambda$$7.class = class Cont$func$lambda$$1 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (acc$0, c$1, tmp$2, tmp$3, tmp$4, tmp$5, curDepth$6, stackDelayRes$7) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.acc$0 = acc$0;
      this.c$1 = c$1;
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
    if (this.pc === 74) {
      this.stackDelayRes$7 = value$;
    } else if (this.pc === 75) {
      this.tmp$2 = value$;
    } else if (this.pc === 76) {
      this.tmp$3 = value$;
    } else if (this.pc === 77) {
      this.tmp$4 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 74) {
        this.pc = 80;
        continue contLoop;
      } else if (this.pc === 79) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = z_of_int(this.tmp$2);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 76;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 76;
        continue contLoop;
      } else if (this.pc === 80) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = NofibPrelude.int_of_char(this.c$1);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 75;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 75;
        continue contLoop;
      } else if (this.pc === 75) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$6);
        this.pc = 79;
        continue contLoop;
      } else if (this.pc === 76) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$6);
        this.pc = 78;
        continue contLoop;
      } else if (this.pc === 78) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$4 = z_of_int(31);
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 77;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 77;
        continue contLoop;
      } else if (this.pc === 77) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$6);
        this.tmp$5 = this.acc$0 * this.tmp$4;
        return this.tmp$3 + this.tmp$5
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda2 = (undefined, function (acc, c) {
  let tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$1(acc, c, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 74);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = NofibPrelude.int_of_char(c);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$1(acc, c, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 75);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = z_of_int(tmp);
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$lambda$$$1(acc, c, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 76);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp2 = z_of_int(31);
  if (tmp2 instanceof runtime.EffectSig.class) {
    tmp2.contTrace.last.next = Cont$func$lambda$$$1(acc, c, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 77);
    tmp2.contTrace.last = tmp2.contTrace.last.next;
    return tmp2
  }
  tmp2 = runtime.resetDepth(tmp2, curDepth);
  tmp3 = acc * tmp2;
  return tmp1 + tmp3
});
hash = function hash(str) {
  let tmp, tmp1, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$hash$sorting$_mls_L0_1199_1303$$(str, tmp, tmp1, curDepth, stackDelayRes, 73);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  tmp = lambda2;
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = z_of_int(0);
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$hash$sorting$_mls_L0_1199_1303$$(str, tmp, tmp1, curDepth, stackDelayRes, 81);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return NofibPrelude.foldl(tmp, tmp1, str)
};
Cont$func$quickSort$sorting$_mls_L0_1309_1692$$ = function Cont$func$quickSort$sorting$_mls_L0_1309_1692$$(xs$0, param0$1, param1$2, x$3, xs_$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12, pc) {
  let tmp;
  tmp = new Cont$func$quickSort$sorting$_mls_L0_1309_1692$1.class(pc);
  return tmp(xs$0, param0$1, param1$2, x$3, xs_$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12)
};
Cont$func$quickSort$sorting$_mls_L0_1309_1692$$ctor = function Cont$func$quickSort$sorting$_mls_L0_1309_1692$$ctor(xs$0, param0$1, param1$2, x$3, xs_$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$quickSort$sorting$_mls_L0_1309_1692$1.class(pc);
    return tmp(xs$0, param0$1, param1$2, x$3, xs_$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12)
  }
};
Cont$func$quickSort$sorting$_mls_L0_1309_1692$1 = function Cont$func$quickSort$sorting$_mls_L0_1309_1692$(pc1) {
  return (xs$01, param0$11, param1$21, x$31, xs_$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, curDepth$101, tmp$111, stackDelayRes$121) => {
    return new Cont$func$quickSort$sorting$_mls_L0_1309_1692$.class(pc1)(xs$01, param0$11, param1$21, x$31, xs_$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, curDepth$101, tmp$111, stackDelayRes$121);
  }
};
Cont$func$quickSort$sorting$_mls_L0_1309_1692$1.class = class Cont$func$quickSort$sorting$_mls_L0_1309_1692$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (xs$0, param0$1, param1$2, x$3, xs_$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.xs$0 = xs$0;
      this.param0$1 = param0$1;
      this.param1$2 = param1$2;
      this.x$3 = x$3;
      this.xs_$4 = xs_$4;
      this.tmp$5 = tmp$5;
      this.tmp$6 = tmp$6;
      this.tmp$7 = tmp$7;
      this.tmp$8 = tmp$8;
      this.tmp$9 = tmp$9;
      this.curDepth$10 = curDepth$10;
      this.tmp$11 = tmp$11;
      this.stackDelayRes$12 = stackDelayRes$12;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 84) {
      this.stackDelayRes$12 = value$;
    } else if (this.pc === 108) {
      this.tmp$11 = value$;
    } else if (this.pc === 103) {
      this.tmp$5 = value$;
    } else if (this.pc === 104) {
      this.tmp$6 = value$;
    } else if (this.pc === 105) {
      this.tmp$7 = value$;
    } else if (this.pc === 106) {
      this.tmp$8 = value$;
    } else if (this.pc === 107) {
      this.tmp$9 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 84) {
        if (this.xs$0 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (this.xs$0 instanceof NofibPrelude.Cons.class) {
          this.param0$1 = this.xs$0.head;
          this.param1$2 = this.xs$0.tail;
          this.x$3 = this.param0$1;
          this.xs_$4 = this.param1$2;
          this.pc = 115;
          continue contLoop;
          this.pc = 109;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$11 = new globalThis.Error("match error");
          if (this.tmp$11 instanceof runtime.EffectSig.class) {
            this.pc = 108;
            this.tmp$11.contTrace.last.next = this;
            this.tmp$11.contTrace.last = this;
            return this.tmp$11
          }
          this.pc = 108;
          continue contLoop;
        }
        this.pc = 109;
        continue contLoop;
      } else if (this.pc === 109) {
        break contLoop;
      } else if (this.pc === 108) {
        this.tmp$11 = runtime.resetDepth(this.tmp$11, this.curDepth$10);
        throw this.tmp$11;
      } else if (this.pc === 110) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.append(this.tmp$6, this.tmp$9)
      } else if (this.pc === 114) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = quickSort(this.tmp$5);
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 104;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 104;
        continue contLoop;
      } else if (this.pc === 115) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = lscomp1$(this.x$3, this.xs_$4);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 103;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 103;
        continue contLoop;
      } else if (this.pc === 103) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$10);
        this.pc = 114;
        continue contLoop;
      } else if (this.pc === 104) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$10);
        this.pc = 113;
        continue contLoop;
      } else if (this.pc === 111) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = NofibPrelude.Cons(this.x$3, this.tmp$8);
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 107;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 107;
        continue contLoop;
      } else if (this.pc === 112) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = quickSort(this.tmp$7);
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 106;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 106;
        continue contLoop;
      } else if (this.pc === 113) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = lscomp2$(this.x$3, this.xs_$4);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 105;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 105;
        continue contLoop;
      } else if (this.pc === 105) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$10);
        this.pc = 112;
        continue contLoop;
      } else if (this.pc === 106) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$10);
        this.pc = 111;
        continue contLoop;
      } else if (this.pc === 107) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$10);
        this.pc = 110;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$quickSort$sorting$_mls_L0_1309_1692$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lscomp1$sorting$_mls_L0_1373_1497$$ = function Cont$func$lscomp1$sorting$_mls_L0_1373_1497$$(x$0, ls$1, param0$2, param1$3, h$4, t$5, scrut$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10, pc) {
  let tmp;
  tmp = new Cont$func$lscomp1$sorting$_mls_L0_1373_1497$1.class(pc);
  return tmp(x$0, ls$1, param0$2, param1$3, h$4, t$5, scrut$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
};
Cont$func$lscomp1$sorting$_mls_L0_1373_1497$$ctor = function Cont$func$lscomp1$sorting$_mls_L0_1373_1497$$ctor(x$0, ls$1, param0$2, param1$3, h$4, t$5, scrut$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lscomp1$sorting$_mls_L0_1373_1497$1.class(pc);
    return tmp(x$0, ls$1, param0$2, param1$3, h$4, t$5, scrut$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
  }
};
Cont$func$lscomp1$sorting$_mls_L0_1373_1497$1 = function Cont$func$lscomp1$sorting$_mls_L0_1373_1497$(pc1) {
  return (x$01, ls$11, param0$21, param1$31, h$41, t$51, scrut$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101) => {
    return new Cont$func$lscomp1$sorting$_mls_L0_1373_1497$.class(pc1)(x$01, ls$11, param0$21, param1$31, h$41, t$51, scrut$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101);
  }
};
Cont$func$lscomp1$sorting$_mls_L0_1373_1497$1.class = class Cont$func$lscomp1$sorting$_mls_L0_1373_1497$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, ls$1, param0$2, param1$3, h$4, t$5, scrut$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$0 = x$0;
      this.ls$1 = ls$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.h$4 = h$4;
      this.t$5 = t$5;
      this.scrut$6 = scrut$6;
      this.tmp$7 = tmp$7;
      this.curDepth$8 = curDepth$8;
      this.tmp$9 = tmp$9;
      this.stackDelayRes$10 = stackDelayRes$10;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 85) {
      this.stackDelayRes$10 = value$;
    } else if (this.pc === 88) {
      this.tmp$9 = value$;
    } else if (this.pc === 86) {
      this.scrut$6 = value$;
    } else if (this.pc === 87) {
      this.tmp$7 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 85) {
        if (this.ls$1 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (this.ls$1 instanceof NofibPrelude.Cons.class) {
          this.param0$2 = this.ls$1.head;
          this.param1$3 = this.ls$1.tail;
          this.h$4 = this.param0$2;
          this.t$5 = this.param1$3;
          this.pc = 93;
          continue contLoop;
          this.pc = 89;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$9 = new globalThis.Error("match error");
          if (this.tmp$9 instanceof runtime.EffectSig.class) {
            this.pc = 88;
            this.tmp$9.contTrace.last.next = this;
            this.tmp$9.contTrace.last = this;
            return this.tmp$9
          }
          this.pc = 88;
          continue contLoop;
        }
        this.pc = 89;
        continue contLoop;
      } else if (this.pc === 89) {
        break contLoop;
      } else if (this.pc === 88) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$8);
        throw this.tmp$9;
      } else if (this.pc === 93) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$6 = leList(this.h$4, this.x$0);
        if (this.scrut$6 instanceof runtime.EffectSig.class) {
          this.pc = 86;
          this.scrut$6.contTrace.last.next = this;
          this.scrut$6.contTrace.last = this;
          return this.scrut$6
        }
        this.pc = 86;
        continue contLoop;
      } else if (this.pc === 86) {
        this.scrut$6 = runtime.resetDepth(this.scrut$6, this.curDepth$8);
        if (this.scrut$6 === true) {
          this.pc = 91;
          continue contLoop;
        } else {
          this.pc = 92;
          continue contLoop;
        }
        this.pc = 89;
        continue contLoop;
      } else if (this.pc === 92) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return lscomp1$(this.x$0, this.t$5)
      } else if (this.pc === 90) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.h$4, this.tmp$7)
      } else if (this.pc === 91) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = lscomp1$(this.x$0, this.t$5);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 87;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 87;
        continue contLoop;
      } else if (this.pc === 87) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$8);
        this.pc = 90;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lscomp1$sorting$_mls_L0_1373_1497$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lscomp1$ = function lscomp1$(x, ls) {
  let param0, param1, h, t, scrut, tmp, curDepth, tmp1, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lscomp1$sorting$_mls_L0_1373_1497$$(x, ls, param0, param1, h, t, scrut, tmp, curDepth, tmp1, stackDelayRes, 85);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    scrut = leList(h, x);
    if (scrut instanceof runtime.EffectSig.class) {
      scrut.contTrace.last.next = Cont$func$lscomp1$sorting$_mls_L0_1373_1497$$(x, ls, param0, param1, h, t, scrut, tmp, curDepth, tmp1, stackDelayRes, 86);
      scrut.contTrace.last = scrut.contTrace.last.next;
      return scrut
    }
    scrut = runtime.resetDepth(scrut, curDepth);
    if (scrut === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = lscomp1$(x, t);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$lscomp1$sorting$_mls_L0_1373_1497$$(x, ls, param0, param1, h, t, scrut, tmp, curDepth, tmp1, stackDelayRes, 87);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.Cons(h, tmp)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      return lscomp1$(x, t)
    }
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = new globalThis.Error("match error");
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$lscomp1$sorting$_mls_L0_1373_1497$$(x, ls, param0, param1, h, t, scrut, tmp, curDepth, tmp1, stackDelayRes, 88);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    throw tmp1;
  }
};
lscomp1 = function lscomp1(x) {
  return (ls) => {
    return lscomp1$(x, ls)
  }
};
Cont$func$lscomp2$sorting$_mls_L0_1506_1630$$ = function Cont$func$lscomp2$sorting$_mls_L0_1506_1630$$(x$0, ls$1, param0$2, param1$3, h$4, t$5, scrut$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10, pc) {
  let tmp;
  tmp = new Cont$func$lscomp2$sorting$_mls_L0_1506_1630$1.class(pc);
  return tmp(x$0, ls$1, param0$2, param1$3, h$4, t$5, scrut$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
};
Cont$func$lscomp2$sorting$_mls_L0_1506_1630$$ctor = function Cont$func$lscomp2$sorting$_mls_L0_1506_1630$$ctor(x$0, ls$1, param0$2, param1$3, h$4, t$5, scrut$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lscomp2$sorting$_mls_L0_1506_1630$1.class(pc);
    return tmp(x$0, ls$1, param0$2, param1$3, h$4, t$5, scrut$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
  }
};
Cont$func$lscomp2$sorting$_mls_L0_1506_1630$1 = function Cont$func$lscomp2$sorting$_mls_L0_1506_1630$(pc1) {
  return (x$01, ls$11, param0$21, param1$31, h$41, t$51, scrut$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101) => {
    return new Cont$func$lscomp2$sorting$_mls_L0_1506_1630$.class(pc1)(x$01, ls$11, param0$21, param1$31, h$41, t$51, scrut$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101);
  }
};
Cont$func$lscomp2$sorting$_mls_L0_1506_1630$1.class = class Cont$func$lscomp2$sorting$_mls_L0_1506_1630$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, ls$1, param0$2, param1$3, h$4, t$5, scrut$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$0 = x$0;
      this.ls$1 = ls$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.h$4 = h$4;
      this.t$5 = t$5;
      this.scrut$6 = scrut$6;
      this.tmp$7 = tmp$7;
      this.curDepth$8 = curDepth$8;
      this.tmp$9 = tmp$9;
      this.stackDelayRes$10 = stackDelayRes$10;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 94) {
      this.stackDelayRes$10 = value$;
    } else if (this.pc === 97) {
      this.tmp$9 = value$;
    } else if (this.pc === 95) {
      this.scrut$6 = value$;
    } else if (this.pc === 96) {
      this.tmp$7 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 94) {
        if (this.ls$1 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (this.ls$1 instanceof NofibPrelude.Cons.class) {
          this.param0$2 = this.ls$1.head;
          this.param1$3 = this.ls$1.tail;
          this.h$4 = this.param0$2;
          this.t$5 = this.param1$3;
          this.pc = 102;
          continue contLoop;
          this.pc = 98;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$9 = new globalThis.Error("match error");
          if (this.tmp$9 instanceof runtime.EffectSig.class) {
            this.pc = 97;
            this.tmp$9.contTrace.last.next = this;
            this.tmp$9.contTrace.last = this;
            return this.tmp$9
          }
          this.pc = 97;
          continue contLoop;
        }
        this.pc = 98;
        continue contLoop;
      } else if (this.pc === 98) {
        break contLoop;
      } else if (this.pc === 97) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$8);
        throw this.tmp$9;
      } else if (this.pc === 102) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$6 = gtList(this.h$4, this.x$0);
        if (this.scrut$6 instanceof runtime.EffectSig.class) {
          this.pc = 95;
          this.scrut$6.contTrace.last.next = this;
          this.scrut$6.contTrace.last = this;
          return this.scrut$6
        }
        this.pc = 95;
        continue contLoop;
      } else if (this.pc === 95) {
        this.scrut$6 = runtime.resetDepth(this.scrut$6, this.curDepth$8);
        if (this.scrut$6 === true) {
          this.pc = 100;
          continue contLoop;
        } else {
          this.pc = 101;
          continue contLoop;
        }
        this.pc = 98;
        continue contLoop;
      } else if (this.pc === 101) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return lscomp2$(this.x$0, this.t$5)
      } else if (this.pc === 99) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.h$4, this.tmp$7)
      } else if (this.pc === 100) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = lscomp2$(this.x$0, this.t$5);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 96;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 96;
        continue contLoop;
      } else if (this.pc === 96) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$8);
        this.pc = 99;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lscomp2$sorting$_mls_L0_1506_1630$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lscomp2$ = function lscomp2$(x, ls) {
  let param0, param1, h, t, scrut, tmp, curDepth, tmp1, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lscomp2$sorting$_mls_L0_1506_1630$$(x, ls, param0, param1, h, t, scrut, tmp, curDepth, tmp1, stackDelayRes, 94);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    scrut = gtList(h, x);
    if (scrut instanceof runtime.EffectSig.class) {
      scrut.contTrace.last.next = Cont$func$lscomp2$sorting$_mls_L0_1506_1630$$(x, ls, param0, param1, h, t, scrut, tmp, curDepth, tmp1, stackDelayRes, 95);
      scrut.contTrace.last = scrut.contTrace.last.next;
      return scrut
    }
    scrut = runtime.resetDepth(scrut, curDepth);
    if (scrut === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = lscomp2$(x, t);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$lscomp2$sorting$_mls_L0_1506_1630$$(x, ls, param0, param1, h, t, scrut, tmp, curDepth, tmp1, stackDelayRes, 96);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.Cons(h, tmp)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      return lscomp2$(x, t)
    }
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = new globalThis.Error("match error");
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$lscomp2$sorting$_mls_L0_1506_1630$$(x, ls, param0, param1, h, t, scrut, tmp, curDepth, tmp1, stackDelayRes, 97);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    throw tmp1;
  }
};
lscomp2 = function lscomp2(x) {
  return (ls) => {
    return lscomp2$(x, ls)
  }
};
quickSort = function quickSort(xs) {
  let param0, param1, x, xs_, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$quickSort$sorting$_mls_L0_1309_1692$$(xs, param0, param1, x, xs_, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 84);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (xs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs_ = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = lscomp1$(x, xs_);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$quickSort$sorting$_mls_L0_1309_1692$$(xs, param0, param1, x, xs_, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 103);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = quickSort(tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$quickSort$sorting$_mls_L0_1309_1692$$(xs, param0, param1, x, xs_, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 104);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = lscomp2$(x, xs_);
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$quickSort$sorting$_mls_L0_1309_1692$$(xs, param0, param1, x, xs_, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 105);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp3 = quickSort(tmp2);
    if (tmp3 instanceof runtime.EffectSig.class) {
      tmp3.contTrace.last.next = Cont$func$quickSort$sorting$_mls_L0_1309_1692$$(xs, param0, param1, x, xs_, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 106);
      tmp3.contTrace.last = tmp3.contTrace.last.next;
      return tmp3
    }
    tmp3 = runtime.resetDepth(tmp3, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp4 = NofibPrelude.Cons(x, tmp3);
    if (tmp4 instanceof runtime.EffectSig.class) {
      tmp4.contTrace.last.next = Cont$func$quickSort$sorting$_mls_L0_1309_1692$$(xs, param0, param1, x, xs_, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 107);
      tmp4.contTrace.last = tmp4.contTrace.last.next;
      return tmp4
    }
    tmp4 = runtime.resetDepth(tmp4, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.append(tmp1, tmp4)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp5 = new globalThis.Error("match error");
    if (tmp5 instanceof runtime.EffectSig.class) {
      tmp5.contTrace.last.next = Cont$func$quickSort$sorting$_mls_L0_1309_1692$$(xs, param0, param1, x, xs_, tmp, tmp1, tmp2, tmp3, tmp4, curDepth, tmp5, stackDelayRes, 108);
      tmp5.contTrace.last = tmp5.contTrace.last.next;
      return tmp5
    }
    tmp5 = runtime.resetDepth(tmp5, curDepth);
    throw tmp5;
  }
};
Cont$func$select$sorting$_mls_L0_1698_1791$$ = function Cont$func$select$sorting$_mls_L0_1698_1791$$(p$0, x$1, ts_fs$2, first1$3, first0$4, ts$5, fs$6, scrut$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12, pc) {
  let tmp;
  tmp = new Cont$func$select$sorting$_mls_L0_1698_1791$1.class(pc);
  return tmp(p$0, x$1, ts_fs$2, first1$3, first0$4, ts$5, fs$6, scrut$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12)
};
Cont$func$select$sorting$_mls_L0_1698_1791$$ctor = function Cont$func$select$sorting$_mls_L0_1698_1791$$ctor(p$0, x$1, ts_fs$2, first1$3, first0$4, ts$5, fs$6, scrut$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$select$sorting$_mls_L0_1698_1791$1.class(pc);
    return tmp(p$0, x$1, ts_fs$2, first1$3, first0$4, ts$5, fs$6, scrut$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12)
  }
};
Cont$func$select$sorting$_mls_L0_1698_1791$1 = function Cont$func$select$sorting$_mls_L0_1698_1791$(pc1) {
  return (p$01, x$11, ts_fs$21, first1$31, first0$41, ts$51, fs$61, scrut$71, tmp$81, tmp$91, curDepth$101, tmp$111, stackDelayRes$121) => {
    return new Cont$func$select$sorting$_mls_L0_1698_1791$.class(pc1)(p$01, x$11, ts_fs$21, first1$31, first0$41, ts$51, fs$61, scrut$71, tmp$81, tmp$91, curDepth$101, tmp$111, stackDelayRes$121);
  }
};
Cont$func$select$sorting$_mls_L0_1698_1791$1.class = class Cont$func$select$sorting$_mls_L0_1698_1791$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (p$0, x$1, ts_fs$2, first1$3, first0$4, ts$5, fs$6, scrut$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.p$0 = p$0;
      this.x$1 = x$1;
      this.ts_fs$2 = ts_fs$2;
      this.first1$3 = first1$3;
      this.first0$4 = first0$4;
      this.ts$5 = ts$5;
      this.fs$6 = fs$6;
      this.scrut$7 = scrut$7;
      this.tmp$8 = tmp$8;
      this.tmp$9 = tmp$9;
      this.curDepth$10 = curDepth$10;
      this.tmp$11 = tmp$11;
      this.stackDelayRes$12 = stackDelayRes$12;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 116) {
      this.stackDelayRes$12 = value$;
    } else if (this.pc === 120) {
      this.tmp$11 = value$;
    } else if (this.pc === 117) {
      this.scrut$7 = value$;
    } else if (this.pc === 119) {
      this.tmp$9 = value$;
    } else if (this.pc === 118) {
      this.tmp$8 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 116) {
        if (globalThis.Array.isArray(this.ts_fs$2) && this.ts_fs$2.length === 2) {
          this.first0$4 = this.ts_fs$2[0];
          this.first1$3 = this.ts_fs$2[1];
          this.ts$5 = this.first0$4;
          this.fs$6 = this.first1$3;
          this.pc = 124;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$11 = new globalThis.Error("match error");
          if (this.tmp$11 instanceof runtime.EffectSig.class) {
            this.pc = 120;
            this.tmp$11.contTrace.last.next = this;
            this.tmp$11.contTrace.last = this;
            return this.tmp$11
          }
          this.pc = 120;
          continue contLoop;
        }
        this.pc = 121;
        continue contLoop;
      } else if (this.pc === 121) {
        break contLoop;
      } else if (this.pc === 120) {
        this.tmp$11 = runtime.resetDepth(this.tmp$11, this.curDepth$10);
        throw this.tmp$11;
      } else if (this.pc === 124) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$7 = runtime.safeCall(this.p$0(this.x$1));
        if (this.scrut$7 instanceof runtime.EffectSig.class) {
          this.pc = 117;
          this.scrut$7.contTrace.last.next = this;
          this.scrut$7.contTrace.last = this;
          return this.scrut$7
        }
        this.pc = 117;
        continue contLoop;
      } else if (this.pc === 117) {
        this.scrut$7 = runtime.resetDepth(this.scrut$7, this.curDepth$10);
        if (this.scrut$7 === true) {
          this.pc = 122;
          continue contLoop;
        } else {
          this.pc = 123;
          continue contLoop;
        }
        this.pc = 121;
        continue contLoop;
      } else if (this.pc === 123) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = NofibPrelude.Cons(this.x$1, this.fs$6);
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 119;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 119;
        continue contLoop;
      } else if (this.pc === 119) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$10);
        return [
          this.ts$5,
          this.tmp$9
        ]
      } else if (this.pc === 122) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = NofibPrelude.Cons(this.x$1, this.ts$5);
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 118;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 118;
        continue contLoop;
      } else if (this.pc === 118) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$10);
        return [
          this.tmp$8,
          this.fs$6
        ]
      }
      break;
    }
  }
  toString() { return "Cont$func$select$sorting$_mls_L0_1698_1791$(" + globalThis.Predef.render(this.pc) + ")"; }
};
select = function select(p, x, ts_fs) {
  let first1, first0, ts, fs1, scrut, tmp, tmp1, curDepth, tmp2, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$select$sorting$_mls_L0_1698_1791$$(p, x, ts_fs, first1, first0, ts, fs1, scrut, tmp, tmp1, curDepth, tmp2, stackDelayRes, 116);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (globalThis.Array.isArray(ts_fs) && ts_fs.length === 2) {
    first0 = ts_fs[0];
    first1 = ts_fs[1];
    ts = first0;
    fs1 = first1;
    runtime.stackDepth = runtime.stackDepth + 1;
    scrut = runtime.safeCall(p(x));
    if (scrut instanceof runtime.EffectSig.class) {
      scrut.contTrace.last.next = Cont$func$select$sorting$_mls_L0_1698_1791$$(p, x, ts_fs, first1, first0, ts, fs1, scrut, tmp, tmp1, curDepth, tmp2, stackDelayRes, 117);
      scrut.contTrace.last = scrut.contTrace.last.next;
      return scrut
    }
    scrut = runtime.resetDepth(scrut, curDepth);
    if (scrut === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = NofibPrelude.Cons(x, ts);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$select$sorting$_mls_L0_1698_1791$$(p, x, ts_fs, first1, first0, ts, fs1, scrut, tmp, tmp1, curDepth, tmp2, stackDelayRes, 118);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      return [
        tmp,
        fs1
      ]
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = NofibPrelude.Cons(x, fs1);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = Cont$func$select$sorting$_mls_L0_1698_1791$$(p, x, ts_fs, first1, first0, ts, fs1, scrut, tmp, tmp1, curDepth, tmp2, stackDelayRes, 119);
        tmp1.contTrace.last = tmp1.contTrace.last.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      return [
        ts,
        tmp1
      ]
    }
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = new globalThis.Error("match error");
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$select$sorting$_mls_L0_1698_1791$$(p, x, ts_fs, first1, first0, ts, fs1, scrut, tmp, tmp1, curDepth, tmp2, stackDelayRes, 120);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    throw tmp2;
  }
};
Cont$func$partition$sorting$_mls_L0_1797_1864$$ = function Cont$func$partition$sorting$_mls_L0_1797_1864$$(p$0, xs$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$partition$sorting$_mls_L0_1797_1864$1.class(pc);
  return tmp(p$0, xs$1, stackDelayRes$2)
};
Cont$func$partition$sorting$_mls_L0_1797_1864$$ctor = function Cont$func$partition$sorting$_mls_L0_1797_1864$$ctor(p$0, xs$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$partition$sorting$_mls_L0_1797_1864$1.class(pc);
    return tmp(p$0, xs$1, stackDelayRes$2)
  }
};
Cont$func$partition$sorting$_mls_L0_1797_1864$1 = function Cont$func$partition$sorting$_mls_L0_1797_1864$(pc1) {
  return (p$01, xs$11, stackDelayRes$21) => {
    return new Cont$func$partition$sorting$_mls_L0_1797_1864$.class(pc1)(p$01, xs$11, stackDelayRes$21);
  }
};
Cont$func$partition$sorting$_mls_L0_1797_1864$1.class = class Cont$func$partition$sorting$_mls_L0_1797_1864$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (p$0, xs$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.p$0 = p$0;
      this.xs$1 = xs$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      return this;
    }
  }
  resume(value$) {
    let lambda$this;
    if (this.pc === 125) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 125) {
        this.pc = 128;
        continue contLoop;
      } else if (this.pc === 128) {
        runtime.stackDepth = runtime.stackDepth + 1;
        lambda$this = runtime.safeCall(lambda3(this.p$0));
        return NofibPrelude.foldr(lambda$this, [
          NofibPrelude.Nil,
          NofibPrelude.Nil
        ], this.xs$1)
      }
      break;
    }
  }
  toString() { return "Cont$func$partition$sorting$_mls_L0_1797_1864$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$2 = function Cont$func$lambda$$$(p$0, x$1, y$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$8.class(pc);
  return tmp(p$0, x$1, y$2, stackDelayRes$3)
};
Cont$func$lambda$$$ctor2 = function Cont$func$lambda$$$ctor(p$0, x$1, y$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$8.class(pc);
    return tmp(p$0, x$1, y$2, stackDelayRes$3)
  }
};
Cont$func$lambda$$8 = function Cont$func$lambda$$(pc1) {
  return (p$01, x$11, y$21, stackDelayRes$31) => {
    return new Cont$func$lambda$$.class(pc1)(p$01, x$11, y$21, stackDelayRes$31);
  }
};
Cont$func$lambda$$8.class = class Cont$func$lambda$$2 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (p$0, x$1, y$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.p$0 = p$0;
      this.x$1 = x$1;
      this.y$2 = y$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 126) {
      this.stackDelayRes$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 126) {
        this.pc = 127;
        continue contLoop;
      } else if (this.pc === 127) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return select(this.p$0, this.x$1, this.y$2)
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda$ = function lambda$(p, x, y) {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$2(p, x, y, stackDelayRes, 126);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return select(p, x, y)
};
lambda3 = (undefined, function (p) {
  return (x, y) => {
    return lambda$(p, x, y)
  }
});
partition = function partition(p, xs) {
  let stackDelayRes, lambda$this;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$partition$sorting$_mls_L0_1797_1864$$(p, xs, stackDelayRes, 125);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  lambda$this = runtime.safeCall(lambda3(p));
  return NofibPrelude.foldr(lambda$this, [
    NofibPrelude.Nil,
    NofibPrelude.Nil
  ], xs)
};
Cont$func$quickSort2$sorting$_mls_L0_1870_2030$$ = function Cont$func$quickSort2$sorting$_mls_L0_1870_2030$$(xs$0, param0$1, param1$2, x$3, xs_$4, scrut$5, first1$6, first0$7, lo$8, hi$9, tmp$10, tmp$11, tmp$12, curDepth$13, tmp$14, tmp$15, stackDelayRes$16, pc) {
  let tmp;
  tmp = new Cont$func$quickSort2$sorting$_mls_L0_1870_2030$1.class(pc);
  return tmp(xs$0, param0$1, param1$2, x$3, xs_$4, scrut$5, first1$6, first0$7, lo$8, hi$9, tmp$10, tmp$11, tmp$12, curDepth$13, tmp$14, tmp$15, stackDelayRes$16)
};
Cont$func$quickSort2$sorting$_mls_L0_1870_2030$$ctor = function Cont$func$quickSort2$sorting$_mls_L0_1870_2030$$ctor(xs$0, param0$1, param1$2, x$3, xs_$4, scrut$5, first1$6, first0$7, lo$8, hi$9, tmp$10, tmp$11, tmp$12, curDepth$13, tmp$14, tmp$15, stackDelayRes$16) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$quickSort2$sorting$_mls_L0_1870_2030$1.class(pc);
    return tmp(xs$0, param0$1, param1$2, x$3, xs_$4, scrut$5, first1$6, first0$7, lo$8, hi$9, tmp$10, tmp$11, tmp$12, curDepth$13, tmp$14, tmp$15, stackDelayRes$16)
  }
};
Cont$func$quickSort2$sorting$_mls_L0_1870_2030$1 = function Cont$func$quickSort2$sorting$_mls_L0_1870_2030$(pc1) {
  return (xs$01, param0$11, param1$21, x$31, xs_$41, scrut$51, first1$61, first0$71, lo$81, hi$91, tmp$101, tmp$111, tmp$121, curDepth$131, tmp$141, tmp$151, stackDelayRes$161) => {
    return new Cont$func$quickSort2$sorting$_mls_L0_1870_2030$.class(pc1)(xs$01, param0$11, param1$21, x$31, xs_$41, scrut$51, first1$61, first0$71, lo$81, hi$91, tmp$101, tmp$111, tmp$121, curDepth$131, tmp$141, tmp$151, stackDelayRes$161);
  }
};
Cont$func$quickSort2$sorting$_mls_L0_1870_2030$1.class = class Cont$func$quickSort2$sorting$_mls_L0_1870_2030$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (xs$0, param0$1, param1$2, x$3, xs_$4, scrut$5, first1$6, first0$7, lo$8, hi$9, tmp$10, tmp$11, tmp$12, curDepth$13, tmp$14, tmp$15, stackDelayRes$16) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.xs$0 = xs$0;
      this.param0$1 = param0$1;
      this.param1$2 = param1$2;
      this.x$3 = x$3;
      this.xs_$4 = xs_$4;
      this.scrut$5 = scrut$5;
      this.first1$6 = first1$6;
      this.first0$7 = first0$7;
      this.lo$8 = lo$8;
      this.hi$9 = hi$9;
      this.tmp$10 = tmp$10;
      this.tmp$11 = tmp$11;
      this.tmp$12 = tmp$12;
      this.curDepth$13 = curDepth$13;
      this.tmp$14 = tmp$14;
      this.tmp$15 = tmp$15;
      this.stackDelayRes$16 = stackDelayRes$16;
      return this;
    }
  }
  resume(value$) {
    let lambda$this;
    if (this.pc === 129) {
      this.stackDelayRes$16 = value$;
    } else if (this.pc === 137) {
      this.tmp$15 = value$;
    } else if (this.pc === 132) {
      this.scrut$5 = value$;
    } else if (this.pc === 136) {
      this.tmp$14 = value$;
    } else if (this.pc === 133) {
      this.tmp$10 = value$;
    } else if (this.pc === 134) {
      this.tmp$11 = value$;
    } else if (this.pc === 135) {
      this.tmp$12 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 129) {
        if (this.xs$0 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (this.xs$0 instanceof NofibPrelude.Cons.class) {
          this.param0$1 = this.xs$0.head;
          this.param1$2 = this.xs$0.tail;
          this.x$3 = this.param0$1;
          this.xs_$4 = this.param1$2;
          this.pc = 143;
          continue contLoop;
          this.pc = 138;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$15 = new globalThis.Error("match error");
          if (this.tmp$15 instanceof runtime.EffectSig.class) {
            this.pc = 137;
            this.tmp$15.contTrace.last.next = this;
            this.tmp$15.contTrace.last = this;
            return this.tmp$15
          }
          this.pc = 137;
          continue contLoop;
        }
        this.pc = 138;
        continue contLoop;
      } else if (this.pc === 138) {
        break contLoop;
      } else if (this.pc === 137) {
        this.tmp$15 = runtime.resetDepth(this.tmp$15, this.curDepth$13);
        throw this.tmp$15;
      } else if (this.pc === 143) {
        runtime.stackDepth = runtime.stackDepth + 1;
        lambda$this = runtime.safeCall(lambda4(this.x$3));
        this.scrut$5 = partition(lambda$this, this.xs_$4);
        if (this.scrut$5 instanceof runtime.EffectSig.class) {
          this.pc = 132;
          this.scrut$5.contTrace.last.next = this;
          this.scrut$5.contTrace.last = this;
          return this.scrut$5
        }
        this.pc = 132;
        continue contLoop;
      } else if (this.pc === 132) {
        this.scrut$5 = runtime.resetDepth(this.scrut$5, this.curDepth$13);
        if (globalThis.Array.isArray(this.scrut$5) && this.scrut$5.length === 2) {
          this.first0$7 = this.scrut$5[0];
          this.first1$6 = this.scrut$5[1];
          this.lo$8 = this.first0$7;
          this.hi$9 = this.first1$6;
          this.pc = 142;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$14 = new globalThis.Error("match error");
          if (this.tmp$14 instanceof runtime.EffectSig.class) {
            this.pc = 136;
            this.tmp$14.contTrace.last.next = this;
            this.tmp$14.contTrace.last = this;
            return this.tmp$14
          }
          this.pc = 136;
          continue contLoop;
        }
        this.pc = 138;
        continue contLoop;
      } else if (this.pc === 136) {
        this.tmp$14 = runtime.resetDepth(this.tmp$14, this.curDepth$13);
        throw this.tmp$14;
      } else if (this.pc === 139) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.append(this.tmp$10, this.tmp$12)
      } else if (this.pc === 142) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$10 = quickSort2(this.lo$8);
        if (this.tmp$10 instanceof runtime.EffectSig.class) {
          this.pc = 133;
          this.tmp$10.contTrace.last.next = this;
          this.tmp$10.contTrace.last = this;
          return this.tmp$10
        }
        this.pc = 133;
        continue contLoop;
      } else if (this.pc === 133) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$13);
        this.pc = 141;
        continue contLoop;
      } else if (this.pc === 140) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$12 = NofibPrelude.Cons(this.x$3, this.tmp$11);
        if (this.tmp$12 instanceof runtime.EffectSig.class) {
          this.pc = 135;
          this.tmp$12.contTrace.last.next = this;
          this.tmp$12.contTrace.last = this;
          return this.tmp$12
        }
        this.pc = 135;
        continue contLoop;
      } else if (this.pc === 141) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$11 = quickSort2(this.hi$9);
        if (this.tmp$11 instanceof runtime.EffectSig.class) {
          this.pc = 134;
          this.tmp$11.contTrace.last.next = this;
          this.tmp$11.contTrace.last = this;
          return this.tmp$11
        }
        this.pc = 134;
        continue contLoop;
      } else if (this.pc === 134) {
        this.tmp$11 = runtime.resetDepth(this.tmp$11, this.curDepth$13);
        this.pc = 140;
        continue contLoop;
      } else if (this.pc === 135) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$13);
        this.pc = 139;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$quickSort2$sorting$_mls_L0_1870_2030$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$3 = function Cont$func$lambda$$$(x$0, y$1, stackDelayRes$2, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$9.class(pc);
  return tmp(x$0, y$1, stackDelayRes$2)
};
Cont$func$lambda$$$ctor3 = function Cont$func$lambda$$$ctor(x$0, y$1, stackDelayRes$2) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$9.class(pc);
    return tmp(x$0, y$1, stackDelayRes$2)
  }
};
Cont$func$lambda$$9 = function Cont$func$lambda$$(pc1) {
  return (x$01, y$11, stackDelayRes$21) => {
    return new Cont$func$lambda$$.class(pc1)(x$01, y$11, stackDelayRes$21);
  }
};
Cont$func$lambda$$9.class = class Cont$func$lambda$$3 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, y$1, stackDelayRes$2) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$0 = x$0;
      this.y$1 = y$1;
      this.stackDelayRes$2 = stackDelayRes$2;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 130) {
      this.stackDelayRes$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 130) {
        this.pc = 131;
        continue contLoop;
      } else if (this.pc === 131) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return geList(this.x$0, this.y$1)
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda$1 = function lambda$(x, y) {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$3(x, y, stackDelayRes, 130);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return geList(x, y)
};
lambda4 = (undefined, function (x) {
  return (y) => {
    return lambda$1(x, y)
  }
});
quickSort2 = function quickSort2(xs) {
  let param0, param1, x, xs_, scrut, first1, first0, lo, hi, tmp, tmp1, tmp2, curDepth, tmp3, tmp4, stackDelayRes, lambda$this;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$quickSort2$sorting$_mls_L0_1870_2030$$(xs, param0, param1, x, xs_, scrut, first1, first0, lo, hi, tmp, tmp1, tmp2, curDepth, tmp3, tmp4, stackDelayRes, 129);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (xs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs_ = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    lambda$this = runtime.safeCall(lambda4(x));
    scrut = partition(lambda$this, xs_);
    if (scrut instanceof runtime.EffectSig.class) {
      scrut.contTrace.last.next = Cont$func$quickSort2$sorting$_mls_L0_1870_2030$$(xs, param0, param1, x, xs_, scrut, first1, first0, lo, hi, tmp, tmp1, tmp2, curDepth, tmp3, tmp4, stackDelayRes, 132);
      scrut.contTrace.last = scrut.contTrace.last.next;
      return scrut
    }
    scrut = runtime.resetDepth(scrut, curDepth);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      lo = first0;
      hi = first1;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = quickSort2(lo);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$quickSort2$sorting$_mls_L0_1870_2030$$(xs, param0, param1, x, xs_, scrut, first1, first0, lo, hi, tmp, tmp1, tmp2, curDepth, tmp3, tmp4, stackDelayRes, 133);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = quickSort2(hi);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = Cont$func$quickSort2$sorting$_mls_L0_1870_2030$$(xs, param0, param1, x, xs_, scrut, first1, first0, lo, hi, tmp, tmp1, tmp2, curDepth, tmp3, tmp4, stackDelayRes, 134);
        tmp1.contTrace.last = tmp1.contTrace.last.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = NofibPrelude.Cons(x, tmp1);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.contTrace.last.next = Cont$func$quickSort2$sorting$_mls_L0_1870_2030$$(xs, param0, param1, x, xs_, scrut, first1, first0, lo, hi, tmp, tmp1, tmp2, curDepth, tmp3, tmp4, stackDelayRes, 135);
        tmp2.contTrace.last = tmp2.contTrace.last.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.append(tmp, tmp2)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = new globalThis.Error("match error");
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.contTrace.last.next = Cont$func$quickSort2$sorting$_mls_L0_1870_2030$$(xs, param0, param1, x, xs_, scrut, first1, first0, lo, hi, tmp, tmp1, tmp2, curDepth, tmp3, tmp4, stackDelayRes, 136);
        tmp3.contTrace.last = tmp3.contTrace.last.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      throw tmp3;
    }
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp4 = new globalThis.Error("match error");
    if (tmp4 instanceof runtime.EffectSig.class) {
      tmp4.contTrace.last.next = Cont$func$quickSort2$sorting$_mls_L0_1870_2030$$(xs, param0, param1, x, xs_, scrut, first1, first0, lo, hi, tmp, tmp1, tmp2, curDepth, tmp3, tmp4, stackDelayRes, 137);
      tmp4.contTrace.last = tmp4.contTrace.last.next;
      return tmp4
    }
    tmp4 = runtime.resetDepth(tmp4, curDepth);
    throw tmp4;
  }
};
Cont$func$quickerSort$sorting$_mls_L0_2036_2355$$ = function Cont$func$quickerSort$sorting$_mls_L0_2036_2355$$(xss$1, curDepth$2, quickerSort$capture$0, pc) {
  let tmp;
  tmp = new Cont$func$quickerSort$sorting$_mls_L0_2036_2355$1.class(pc);
  return tmp(xss$1, curDepth$2, quickerSort$capture$0)
};
Cont$func$quickerSort$sorting$_mls_L0_2036_2355$$ctor = function Cont$func$quickerSort$sorting$_mls_L0_2036_2355$$ctor(xss$1, curDepth$2, quickerSort$capture$0) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$quickerSort$sorting$_mls_L0_2036_2355$1.class(pc);
    return tmp(xss$1, curDepth$2, quickerSort$capture$0)
  }
};
Cont$func$quickerSort$sorting$_mls_L0_2036_2355$1 = function Cont$func$quickerSort$sorting$_mls_L0_2036_2355$(pc1) {
  return (xss$11, curDepth$21, quickerSort$capture$01) => {
    return new Cont$func$quickerSort$sorting$_mls_L0_2036_2355$.class(pc1)(xss$11, curDepth$21, quickerSort$capture$01);
  }
};
Cont$func$quickerSort$sorting$_mls_L0_2036_2355$1.class = class Cont$func$quickerSort$sorting$_mls_L0_2036_2355$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (xss$1, curDepth$2, quickerSort$capture$0) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.xss$1 = xss$1;
      this.curDepth$2 = curDepth$2;
      this.quickerSort$capture$0 = quickerSort$capture$0;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 144) {
      this.quickerSort$capture$0.stackDelayRes1$ = value$;
    } else if (this.pc === 163) {
      this.quickerSort$capture$0.tmp4$ = value$;
    }
    contLoop: while (true) {
      if (this.pc === 144) {
        if (this.xss$1 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (this.xss$1 instanceof NofibPrelude.Cons.class) {
          this.quickerSort$capture$0.param06$ = this.xss$1.head;
          this.quickerSort$capture$0.param12$ = this.xss$1.tail;
          this.quickerSort$capture$0.x5$ = this.quickerSort$capture$0.param06$;
          if (this.quickerSort$capture$0.param12$ instanceof NofibPrelude.Nil.class) {
            this.pc = 165;
            continue contLoop;
          } else {
            this.quickerSort$capture$0.x3$ = this.quickerSort$capture$0.param06$;
            this.quickerSort$capture$0.xs0$ = this.quickerSort$capture$0.param12$;
            this.pc = 166;
            continue contLoop;
          }
          this.pc = 164;
          continue contLoop;
          this.pc = 164;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.quickerSort$capture$0.tmp4$ = new globalThis.Error("match error");
          if (this.quickerSort$capture$0.tmp4$ instanceof runtime.EffectSig.class) {
            this.pc = 163;
            this.quickerSort$capture$0.tmp4$.contTrace.last.next = this;
            this.quickerSort$capture$0.tmp4$.contTrace.last = this;
            return this.quickerSort$capture$0.tmp4$
          }
          this.pc = 163;
          continue contLoop;
        }
        this.pc = 164;
        continue contLoop;
      } else if (this.pc === 164) {
        break contLoop;
      } else if (this.pc === 163) {
        this.quickerSort$capture$0.tmp4$ = runtime.resetDepth(this.quickerSort$capture$0.tmp4$, this.curDepth$2);
        throw this.quickerSort$capture$0.tmp4$;
      } else if (this.pc === 166) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return split$(this.xss$1, this.curDepth$2, this.quickerSort$capture$0, this.quickerSort$capture$0.x3$, NofibPrelude.Nil, NofibPrelude.Nil, this.quickerSort$capture$0.xs0$)
      } else if (this.pc === 165) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.quickerSort$capture$0.x5$, NofibPrelude.Nil)
      }
      break;
    }
  }
  toString() { return "Cont$func$quickerSort$sorting$_mls_L0_2036_2355$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$split$sorting$_mls_L0_2128_2328$$ = function Cont$func$split$sorting$_mls_L0_2128_2328$$(xss$1, x$2, lo$3, hi$4, ys$5, param0$6, param1$7, y$8, ys_$9, scrut$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, tmp$17, stackDelayRes$18, curDepth$19, quickerSort$capture$0, pc) {
  let tmp;
  tmp = new Cont$func$split$sorting$_mls_L0_2128_2328$1.class(pc);
  return tmp(xss$1, x$2, lo$3, hi$4, ys$5, param0$6, param1$7, y$8, ys_$9, scrut$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, tmp$17, stackDelayRes$18, curDepth$19, quickerSort$capture$0)
};
Cont$func$split$sorting$_mls_L0_2128_2328$$ctor = function Cont$func$split$sorting$_mls_L0_2128_2328$$ctor(xss$1, x$2, lo$3, hi$4, ys$5, param0$6, param1$7, y$8, ys_$9, scrut$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, tmp$17, stackDelayRes$18, curDepth$19, quickerSort$capture$0) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$split$sorting$_mls_L0_2128_2328$1.class(pc);
    return tmp(xss$1, x$2, lo$3, hi$4, ys$5, param0$6, param1$7, y$8, ys_$9, scrut$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, tmp$17, stackDelayRes$18, curDepth$19, quickerSort$capture$0)
  }
};
Cont$func$split$sorting$_mls_L0_2128_2328$1 = function Cont$func$split$sorting$_mls_L0_2128_2328$(pc1) {
  return (xss$11, x$21, lo$31, hi$41, ys$51, param0$61, param1$71, y$81, ys_$91, scrut$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, curDepth$161, tmp$171, stackDelayRes$181, curDepth$191, quickerSort$capture$01) => {
    return new Cont$func$split$sorting$_mls_L0_2128_2328$.class(pc1)(xss$11, x$21, lo$31, hi$41, ys$51, param0$61, param1$71, y$81, ys_$91, scrut$101, tmp$111, tmp$121, tmp$131, tmp$141, tmp$151, curDepth$161, tmp$171, stackDelayRes$181, curDepth$191, quickerSort$capture$01);
  }
};
Cont$func$split$sorting$_mls_L0_2128_2328$1.class = class Cont$func$split$sorting$_mls_L0_2128_2328$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (xss$1, x$2, lo$3, hi$4, ys$5, param0$6, param1$7, y$8, ys_$9, scrut$10, tmp$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, tmp$17, stackDelayRes$18, curDepth$19, quickerSort$capture$0) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.xss$1 = xss$1;
      this.x$2 = x$2;
      this.lo$3 = lo$3;
      this.hi$4 = hi$4;
      this.ys$5 = ys$5;
      this.param0$6 = param0$6;
      this.param1$7 = param1$7;
      this.y$8 = y$8;
      this.ys_$9 = ys_$9;
      this.scrut$10 = scrut$10;
      this.tmp$11 = tmp$11;
      this.tmp$12 = tmp$12;
      this.tmp$13 = tmp$13;
      this.tmp$14 = tmp$14;
      this.tmp$15 = tmp$15;
      this.curDepth$16 = curDepth$16;
      this.tmp$17 = tmp$17;
      this.stackDelayRes$18 = stackDelayRes$18;
      this.curDepth$19 = curDepth$19;
      this.quickerSort$capture$0 = quickerSort$capture$0;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 145) {
      this.stackDelayRes$18 = value$;
    } else if (this.pc === 152) {
      this.tmp$17 = value$;
    } else if (this.pc === 149) {
      this.scrut$10 = value$;
    } else if (this.pc === 151) {
      this.tmp$15 = value$;
    } else if (this.pc === 150) {
      this.tmp$14 = value$;
    } else if (this.pc === 146) {
      this.tmp$11 = value$;
    } else if (this.pc === 147) {
      this.tmp$12 = value$;
    } else if (this.pc === 148) {
      this.tmp$13 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 145) {
        if (this.ys$5 instanceof NofibPrelude.Nil.class) {
          this.pc = 157;
          continue contLoop;
        } else if (this.ys$5 instanceof NofibPrelude.Cons.class) {
          this.param0$6 = this.ys$5.head;
          this.param1$7 = this.ys$5.tail;
          this.y$8 = this.param0$6;
          this.ys_$9 = this.param1$7;
          this.pc = 162;
          continue contLoop;
          this.pc = 153;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$17 = new globalThis.Error("match error");
          if (this.tmp$17 instanceof runtime.EffectSig.class) {
            this.pc = 152;
            this.tmp$17.contTrace.last.next = this;
            this.tmp$17.contTrace.last = this;
            return this.tmp$17
          }
          this.pc = 152;
          continue contLoop;
        }
        this.pc = 153;
        continue contLoop;
      } else if (this.pc === 153) {
        break contLoop;
      } else if (this.pc === 152) {
        this.tmp$17 = runtime.resetDepth(this.tmp$17, this.curDepth$16);
        throw this.tmp$17;
      } else if (this.pc === 162) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$10 = leList(this.y$8, this.x$2);
        if (this.scrut$10 instanceof runtime.EffectSig.class) {
          this.pc = 149;
          this.scrut$10.contTrace.last.next = this;
          this.scrut$10.contTrace.last = this;
          return this.scrut$10
        }
        this.pc = 149;
        continue contLoop;
      } else if (this.pc === 149) {
        this.scrut$10 = runtime.resetDepth(this.scrut$10, this.curDepth$16);
        if (this.scrut$10 === true) {
          this.pc = 159;
          continue contLoop;
        } else {
          this.pc = 161;
          continue contLoop;
        }
        this.pc = 153;
        continue contLoop;
      } else if (this.pc === 160) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return split$(this.xss$1, this.curDepth$19, this.quickerSort$capture$0, this.x$2, this.lo$3, this.tmp$15, this.ys_$9)
      } else if (this.pc === 161) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$15 = NofibPrelude.Cons(this.y$8, this.hi$4);
        if (this.tmp$15 instanceof runtime.EffectSig.class) {
          this.pc = 151;
          this.tmp$15.contTrace.last.next = this;
          this.tmp$15.contTrace.last = this;
          return this.tmp$15
        }
        this.pc = 151;
        continue contLoop;
      } else if (this.pc === 151) {
        this.tmp$15 = runtime.resetDepth(this.tmp$15, this.curDepth$16);
        this.pc = 160;
        continue contLoop;
      } else if (this.pc === 158) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return split$(this.xss$1, this.curDepth$19, this.quickerSort$capture$0, this.x$2, this.tmp$14, this.hi$4, this.ys_$9)
      } else if (this.pc === 159) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$14 = NofibPrelude.Cons(this.y$8, this.lo$3);
        if (this.tmp$14 instanceof runtime.EffectSig.class) {
          this.pc = 150;
          this.tmp$14.contTrace.last.next = this;
          this.tmp$14.contTrace.last = this;
          return this.tmp$14
        }
        this.pc = 150;
        continue contLoop;
      } else if (this.pc === 150) {
        this.tmp$14 = runtime.resetDepth(this.tmp$14, this.curDepth$16);
        this.pc = 158;
        continue contLoop;
      } else if (this.pc === 154) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.append(this.tmp$11, this.tmp$13)
      } else if (this.pc === 157) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$11 = quickerSort(this.lo$3);
        if (this.tmp$11 instanceof runtime.EffectSig.class) {
          this.pc = 146;
          this.tmp$11.contTrace.last.next = this;
          this.tmp$11.contTrace.last = this;
          return this.tmp$11
        }
        this.pc = 146;
        continue contLoop;
      } else if (this.pc === 146) {
        this.tmp$11 = runtime.resetDepth(this.tmp$11, this.curDepth$16);
        this.pc = 156;
        continue contLoop;
      } else if (this.pc === 155) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$13 = NofibPrelude.Cons(this.x$2, this.tmp$12);
        if (this.tmp$13 instanceof runtime.EffectSig.class) {
          this.pc = 148;
          this.tmp$13.contTrace.last.next = this;
          this.tmp$13.contTrace.last = this;
          return this.tmp$13
        }
        this.pc = 148;
        continue contLoop;
      } else if (this.pc === 156) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$12 = quickerSort(this.hi$4);
        if (this.tmp$12 instanceof runtime.EffectSig.class) {
          this.pc = 147;
          this.tmp$12.contTrace.last.next = this;
          this.tmp$12.contTrace.last = this;
          return this.tmp$12
        }
        this.pc = 147;
        continue contLoop;
      } else if (this.pc === 147) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$16);
        this.pc = 155;
        continue contLoop;
      } else if (this.pc === 148) {
        this.tmp$13 = runtime.resetDepth(this.tmp$13, this.curDepth$16);
        this.pc = 154;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$split$sorting$_mls_L0_2128_2328$(" + globalThis.Predef.render(this.pc) + ")"; }
};
split$ = function split$(xss, curDepth, quickerSort$capture2, x, lo, hi, ys) {
  let param0, param1, y, ys_, scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth1, tmp5, stackDelayRes;
  curDepth1 = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$split$sorting$_mls_L0_2128_2328$$(xss, x, lo, hi, ys, param0, param1, y, ys_, scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth1, tmp5, stackDelayRes, curDepth, quickerSort$capture2, 145);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (ys instanceof NofibPrelude.Nil.class) {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = quickerSort(lo);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$split$sorting$_mls_L0_2128_2328$$(xss, x, lo, hi, ys, param0, param1, y, ys_, scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth1, tmp5, stackDelayRes, curDepth, quickerSort$capture2, 146);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth1);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = quickerSort(hi);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$split$sorting$_mls_L0_2128_2328$$(xss, x, lo, hi, ys, param0, param1, y, ys_, scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth1, tmp5, stackDelayRes, curDepth, quickerSort$capture2, 147);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth1);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = NofibPrelude.Cons(x, tmp1);
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$split$sorting$_mls_L0_2128_2328$$(xss, x, lo, hi, ys, param0, param1, y, ys_, scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth1, tmp5, stackDelayRes, curDepth, quickerSort$capture2, 148);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth1);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.append(tmp, tmp2)
  } else if (ys instanceof NofibPrelude.Cons.class) {
    param0 = ys.head;
    param1 = ys.tail;
    y = param0;
    ys_ = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    scrut = leList(y, x);
    if (scrut instanceof runtime.EffectSig.class) {
      scrut.contTrace.last.next = Cont$func$split$sorting$_mls_L0_2128_2328$$(xss, x, lo, hi, ys, param0, param1, y, ys_, scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth1, tmp5, stackDelayRes, curDepth, quickerSort$capture2, 149);
      scrut.contTrace.last = scrut.contTrace.last.next;
      return scrut
    }
    scrut = runtime.resetDepth(scrut, curDepth1);
    if (scrut === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = NofibPrelude.Cons(y, lo);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.contTrace.last.next = Cont$func$split$sorting$_mls_L0_2128_2328$$(xss, x, lo, hi, ys, param0, param1, y, ys_, scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth1, tmp5, stackDelayRes, curDepth, quickerSort$capture2, 150);
        tmp3.contTrace.last = tmp3.contTrace.last.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth1);
      runtime.stackDepth = runtime.stackDepth + 1;
      return split$(xss, curDepth, quickerSort$capture2, x, tmp3, hi, ys_)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = NofibPrelude.Cons(y, hi);
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.contTrace.last.next = Cont$func$split$sorting$_mls_L0_2128_2328$$(xss, x, lo, hi, ys, param0, param1, y, ys_, scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth1, tmp5, stackDelayRes, curDepth, quickerSort$capture2, 151);
        tmp4.contTrace.last = tmp4.contTrace.last.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth1);
      runtime.stackDepth = runtime.stackDepth + 1;
      return split$(xss, curDepth, quickerSort$capture2, x, lo, tmp4, ys_)
    }
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp5 = new globalThis.Error("match error");
    if (tmp5 instanceof runtime.EffectSig.class) {
      tmp5.contTrace.last.next = Cont$func$split$sorting$_mls_L0_2128_2328$$(xss, x, lo, hi, ys, param0, param1, y, ys_, scrut, tmp, tmp1, tmp2, tmp3, tmp4, curDepth1, tmp5, stackDelayRes, curDepth, quickerSort$capture2, 152);
      tmp5.contTrace.last = tmp5.contTrace.last.next;
      return tmp5
    }
    tmp5 = runtime.resetDepth(tmp5, curDepth1);
    throw tmp5;
  }
};
split = function split(xss, curDepth, quickerSort$capture2) {
  return (x, lo, hi, ys) => {
    return split$(xss, curDepth, quickerSort$capture2, x, lo, hi, ys)
  }
};
quickerSort$capture1 = function quickerSort$capture(xs0$1, stackDelayRes1$1, param12$1, x3$1, tmp4$1, x5$1, param06$1) {
  return new quickerSort$capture.class(xs0$1, stackDelayRes1$1, param12$1, x3$1, tmp4$1, x5$1, param06$1);
};
quickerSort$capture1.class = class quickerSort$capture {
  constructor(xs0$, stackDelayRes1$, param12$, x3$, tmp4$, x5$, param06$) {
    this.xs0$ = xs0$;
    this.stackDelayRes1$ = stackDelayRes1$;
    this.param12$ = param12$;
    this.x3$ = x3$;
    this.tmp4$ = tmp4$;
    this.x5$ = x5$;
    this.param06$ = param06$;
  }
  toString() { return "quickerSort$capture(" + globalThis.Predef.render(this.xs0$) + ", " + globalThis.Predef.render(this.stackDelayRes1$) + ", " + globalThis.Predef.render(this.param12$) + ", " + globalThis.Predef.render(this.x3$) + ", " + globalThis.Predef.render(this.tmp4$) + ", " + globalThis.Predef.render(this.x5$) + ", " + globalThis.Predef.render(this.param06$) + ")"; }
};
quickerSort = function quickerSort(xss) {
  let curDepth, capture;
  capture = new quickerSort$capture1(null, null, null, null, null, null, null);
  curDepth = runtime.stackDepth;
  capture.stackDelayRes1$ = runtime.checkDepth();
  if (capture.stackDelayRes1$ instanceof runtime.EffectSig.class) {
    capture.stackDelayRes1$.contTrace.last.next = Cont$func$quickerSort$sorting$_mls_L0_2036_2355$$(xss, curDepth, capture, 144);
    capture.stackDelayRes1$.contTrace.last = capture.stackDelayRes1$.contTrace.last.next;
    return capture.stackDelayRes1$
  }
  if (xss instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (xss instanceof NofibPrelude.Cons.class) {
    capture.param06$ = xss.head;
    capture.param12$ = xss.tail;
    capture.x5$ = capture.param06$;
    if (capture.param12$ instanceof NofibPrelude.Nil.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.Cons(capture.x5$, NofibPrelude.Nil)
    } else {
      capture.x3$ = capture.param06$;
      capture.xs0$ = capture.param12$;
      runtime.stackDepth = runtime.stackDepth + 1;
      return split$(xss, curDepth, capture, capture.x3$, NofibPrelude.Nil, NofibPrelude.Nil, capture.xs0$)
    }
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    capture.tmp4$ = new globalThis.Error("match error");
    if (capture.tmp4$ instanceof runtime.EffectSig.class) {
      capture.tmp4$.contTrace.last.next = Cont$func$quickerSort$sorting$_mls_L0_2036_2355$$(xss, curDepth, capture, 163);
      capture.tmp4$.contTrace.last = capture.tmp4$.contTrace.last.next;
      return capture.tmp4$
    }
    capture.tmp4$ = runtime.resetDepth(capture.tmp4$, curDepth);
    throw capture.tmp4$;
  }
};
Cont$func$insertSort$sorting$_mls_L0_2361_2767$$ = function Cont$func$insertSort$sorting$_mls_L0_2361_2767$$(xss$0, param0$1, param1$2, x$3, xs$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8, pc) {
  let tmp;
  tmp = new Cont$func$insertSort$sorting$_mls_L0_2361_2767$1.class(pc);
  return tmp(xss$0, param0$1, param1$2, x$3, xs$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8)
};
Cont$func$insertSort$sorting$_mls_L0_2361_2767$$ctor = function Cont$func$insertSort$sorting$_mls_L0_2361_2767$$ctor(xss$0, param0$1, param1$2, x$3, xs$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$insertSort$sorting$_mls_L0_2361_2767$1.class(pc);
    return tmp(xss$0, param0$1, param1$2, x$3, xs$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8)
  }
};
Cont$func$insertSort$sorting$_mls_L0_2361_2767$1 = function Cont$func$insertSort$sorting$_mls_L0_2361_2767$(pc1) {
  return (xss$01, param0$11, param1$21, x$31, xs$41, tmp$51, curDepth$61, tmp$71, stackDelayRes$81) => {
    return new Cont$func$insertSort$sorting$_mls_L0_2361_2767$.class(pc1)(xss$01, param0$11, param1$21, x$31, xs$41, tmp$51, curDepth$61, tmp$71, stackDelayRes$81);
  }
};
Cont$func$insertSort$sorting$_mls_L0_2361_2767$1.class = class Cont$func$insertSort$sorting$_mls_L0_2361_2767$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (xss$0, param0$1, param1$2, x$3, xs$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.xss$0 = xss$0;
      this.param0$1 = param0$1;
      this.param1$2 = param1$2;
      this.x$3 = x$3;
      this.xs$4 = xs$4;
      this.tmp$5 = tmp$5;
      this.curDepth$6 = curDepth$6;
      this.tmp$7 = tmp$7;
      this.stackDelayRes$8 = stackDelayRes$8;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 167) {
      this.stackDelayRes$8 = value$;
    } else if (this.pc === 203) {
      this.tmp$7 = value$;
    } else if (this.pc === 202) {
      this.tmp$5 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 167) {
        if (this.xss$0 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (this.xss$0 instanceof NofibPrelude.Cons.class) {
          this.param0$1 = this.xss$0.head;
          this.param1$2 = this.xss$0.tail;
          this.x$3 = this.param0$1;
          this.xs$4 = this.param1$2;
          this.pc = 206;
          continue contLoop;
          this.pc = 204;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$7 = new globalThis.Error("match error");
          if (this.tmp$7 instanceof runtime.EffectSig.class) {
            this.pc = 203;
            this.tmp$7.contTrace.last.next = this;
            this.tmp$7.contTrace.last = this;
            return this.tmp$7
          }
          this.pc = 203;
          continue contLoop;
        }
        this.pc = 204;
        continue contLoop;
      } else if (this.pc === 204) {
        break contLoop;
      } else if (this.pc === 203) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$6);
        throw this.tmp$7;
      } else if (this.pc === 205) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return trins(NofibPrelude.Nil, this.tmp$5, this.xs$4)
      } else if (this.pc === 206) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = NofibPrelude.Cons(this.x$3, NofibPrelude.Nil);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 202;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 202;
        continue contLoop;
      } else if (this.pc === 202) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$6);
        this.pc = 205;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$insertSort$sorting$_mls_L0_2361_2767$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$trins$sorting$_mls_L0_2427_2738$$ = function Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev$0, xs$1, ys$2, param0$3, param1$4, x$5, xs_$6, param0$7, param1$8, y$9, ys_$10, scrut$11, xs$12, y$13, ys_$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, curDepth$26, tmp$27, tmp$28, tmp$29, stackDelayRes$30, pc) {
  let tmp;
  tmp = new Cont$func$trins$sorting$_mls_L0_2427_2738$1.class(pc);
  return tmp(rev$0, xs$1, ys$2, param0$3, param1$4, x$5, xs_$6, param0$7, param1$8, y$9, ys_$10, scrut$11, xs$12, y$13, ys_$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, curDepth$26, tmp$27, tmp$28, tmp$29, stackDelayRes$30)
};
Cont$func$trins$sorting$_mls_L0_2427_2738$$ctor = function Cont$func$trins$sorting$_mls_L0_2427_2738$$ctor(rev$0, xs$1, ys$2, param0$3, param1$4, x$5, xs_$6, param0$7, param1$8, y$9, ys_$10, scrut$11, xs$12, y$13, ys_$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, curDepth$26, tmp$27, tmp$28, tmp$29, stackDelayRes$30) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$trins$sorting$_mls_L0_2427_2738$1.class(pc);
    return tmp(rev$0, xs$1, ys$2, param0$3, param1$4, x$5, xs_$6, param0$7, param1$8, y$9, ys_$10, scrut$11, xs$12, y$13, ys_$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, curDepth$26, tmp$27, tmp$28, tmp$29, stackDelayRes$30)
  }
};
Cont$func$trins$sorting$_mls_L0_2427_2738$1 = function Cont$func$trins$sorting$_mls_L0_2427_2738$(pc1) {
  return (rev$01, xs$11, ys$21, param0$31, param1$41, x$51, xs_$61, param0$71, param1$81, y$91, ys_$101, scrut$111, xs$121, y$131, ys_$141, tmp$151, tmp$161, tmp$171, tmp$181, tmp$191, tmp$201, tmp$211, tmp$221, tmp$231, tmp$241, tmp$251, curDepth$261, tmp$271, tmp$281, tmp$291, stackDelayRes$301) => {
    return new Cont$func$trins$sorting$_mls_L0_2427_2738$.class(pc1)(rev$01, xs$11, ys$21, param0$31, param1$41, x$51, xs_$61, param0$71, param1$81, y$91, ys_$101, scrut$111, xs$121, y$131, ys_$141, tmp$151, tmp$161, tmp$171, tmp$181, tmp$191, tmp$201, tmp$211, tmp$221, tmp$231, tmp$241, tmp$251, curDepth$261, tmp$271, tmp$281, tmp$291, stackDelayRes$301);
  }
};
Cont$func$trins$sorting$_mls_L0_2427_2738$1.class = class Cont$func$trins$sorting$_mls_L0_2427_2738$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (rev$0, xs$1, ys$2, param0$3, param1$4, x$5, xs_$6, param0$7, param1$8, y$9, ys_$10, scrut$11, xs$12, y$13, ys_$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, curDepth$26, tmp$27, tmp$28, tmp$29, stackDelayRes$30) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.rev$0 = rev$0;
      this.xs$1 = xs$1;
      this.ys$2 = ys$2;
      this.param0$3 = param0$3;
      this.param1$4 = param1$4;
      this.x$5 = x$5;
      this.xs_$6 = xs_$6;
      this.param0$7 = param0$7;
      this.param1$8 = param1$8;
      this.y$9 = y$9;
      this.ys_$10 = ys_$10;
      this.scrut$11 = scrut$11;
      this.xs$12 = xs$12;
      this.y$13 = y$13;
      this.ys_$14 = ys_$14;
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
      this.curDepth$26 = curDepth$26;
      this.tmp$27 = tmp$27;
      this.tmp$28 = tmp$28;
      this.tmp$29 = tmp$29;
      this.stackDelayRes$30 = stackDelayRes$30;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 168) {
      this.stackDelayRes$30 = value$;
    } else if (this.pc === 183) {
      this.tmp$29 = value$;
    } else if (this.pc === 182) {
      this.tmp$28 = value$;
    } else if (this.pc === 175) {
      this.scrut$11 = value$;
    } else if (this.pc === 178) {
      this.tmp$22 = value$;
    } else if (this.pc === 179) {
      this.tmp$23 = value$;
    } else if (this.pc === 180) {
      this.tmp$24 = value$;
    } else if (this.pc === 181) {
      this.tmp$25 = value$;
    } else if (this.pc === 176) {
      this.tmp$20 = value$;
    } else if (this.pc === 177) {
      this.tmp$21 = value$;
    } else if (this.pc === 174) {
      this.tmp$19 = value$;
    } else if (this.pc === 173) {
      this.tmp$27 = value$;
    } else if (this.pc === 172) {
      this.tmp$18 = value$;
    } else if (this.pc === 169) {
      this.tmp$15 = value$;
    } else if (this.pc === 170) {
      this.tmp$16 = value$;
    } else if (this.pc === 171) {
      this.tmp$17 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 168) {
        if (this.xs$1 instanceof NofibPrelude.Nil.class) {
          this.xs$12 = this.xs$1;
          if (this.ys$2 instanceof NofibPrelude.Cons.class) {
            this.param0$7 = this.ys$2.head;
            this.param1$8 = this.ys$2.tail;
            this.y$13 = this.param0$7;
            this.ys_$14 = this.param1$8;
            this.pc = 188;
            continue contLoop;
          } else if (this.ys$2 instanceof NofibPrelude.Nil.class) {
            this.pc = 190;
            continue contLoop;
            this.pc = 184;
            continue contLoop;
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.tmp$27 = new globalThis.Error("match error");
            if (this.tmp$27 instanceof runtime.EffectSig.class) {
              this.pc = 173;
              this.tmp$27.contTrace.last.next = this;
              this.tmp$27.contTrace.last = this;
              return this.tmp$27
            }
            this.pc = 173;
            continue contLoop;
          }
          this.pc = 184;
          continue contLoop;
        } else {
          this.xs$12 = this.xs$1;
          if (this.ys$2 instanceof NofibPrelude.Nil.class) {
            this.pc = 192;
            continue contLoop;
          } else {
            if (this.xs$1 instanceof NofibPrelude.Cons.class) {
              this.param0$3 = this.xs$1.head;
              this.param1$4 = this.xs$1.tail;
              this.x$5 = this.param0$3;
              this.xs_$6 = this.param1$4;
              if (this.ys$2 instanceof NofibPrelude.Cons.class) {
                this.param0$7 = this.ys$2.head;
                this.param1$8 = this.ys$2.tail;
                this.y$9 = this.param0$7;
                this.ys_$10 = this.param1$8;
                this.pc = 201;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.tmp$28 = new globalThis.Error("match error");
                if (this.tmp$28 instanceof runtime.EffectSig.class) {
                  this.pc = 182;
                  this.tmp$28.contTrace.last.next = this;
                  this.tmp$28.contTrace.last = this;
                  return this.tmp$28
                }
                this.pc = 182;
                continue contLoop;
              }
              this.pc = 184;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.tmp$29 = new globalThis.Error("match error");
              if (this.tmp$29 instanceof runtime.EffectSig.class) {
                this.pc = 183;
                this.tmp$29.contTrace.last.next = this;
                this.tmp$29.contTrace.last = this;
                return this.tmp$29
              }
              this.pc = 183;
              continue contLoop;
            }
            this.pc = 184;
            continue contLoop;
          }
          this.pc = 184;
          continue contLoop;
        }
        this.pc = 184;
        continue contLoop;
      } else if (this.pc === 184) {
        break contLoop;
      } else if (this.pc === 183) {
        this.tmp$29 = runtime.resetDepth(this.tmp$29, this.curDepth$26);
        throw this.tmp$29;
      } else if (this.pc === 182) {
        this.tmp$28 = runtime.resetDepth(this.tmp$28, this.curDepth$26);
        throw this.tmp$28;
      } else if (this.pc === 201) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$11 = NofibPrelude.ltList(this.x$5, this.y$9);
        if (this.scrut$11 instanceof runtime.EffectSig.class) {
          this.pc = 175;
          this.scrut$11.contTrace.last.next = this;
          this.scrut$11.contTrace.last = this;
          return this.scrut$11
        }
        this.pc = 175;
        continue contLoop;
      } else if (this.pc === 175) {
        this.scrut$11 = runtime.resetDepth(this.scrut$11, this.curDepth$26);
        if (this.scrut$11 === true) {
          this.pc = 195;
          continue contLoop;
        } else {
          this.pc = 200;
          continue contLoop;
        }
        this.pc = 184;
        continue contLoop;
      } else if (this.pc === 196) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return trins(NofibPrelude.Nil, this.tmp$25, this.ys_$10)
      } else if (this.pc === 197) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$25 = NofibPrelude.append(this.tmp$22, this.tmp$24);
        if (this.tmp$25 instanceof runtime.EffectSig.class) {
          this.pc = 181;
          this.tmp$25.contTrace.last.next = this;
          this.tmp$25.contTrace.last = this;
          return this.tmp$25
        }
        this.pc = 181;
        continue contLoop;
      } else if (this.pc === 200) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$22 = NofibPrelude.reverse(this.rev$0);
        if (this.tmp$22 instanceof runtime.EffectSig.class) {
          this.pc = 178;
          this.tmp$22.contTrace.last.next = this;
          this.tmp$22.contTrace.last = this;
          return this.tmp$22
        }
        this.pc = 178;
        continue contLoop;
      } else if (this.pc === 178) {
        this.tmp$22 = runtime.resetDepth(this.tmp$22, this.curDepth$26);
        this.pc = 199;
        continue contLoop;
      } else if (this.pc === 198) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$24 = NofibPrelude.Cons(this.y$9, this.tmp$23);
        if (this.tmp$24 instanceof runtime.EffectSig.class) {
          this.pc = 180;
          this.tmp$24.contTrace.last.next = this;
          this.tmp$24.contTrace.last = this;
          return this.tmp$24
        }
        this.pc = 180;
        continue contLoop;
      } else if (this.pc === 199) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$23 = NofibPrelude.Cons(this.x$5, this.xs_$6);
        if (this.tmp$23 instanceof runtime.EffectSig.class) {
          this.pc = 179;
          this.tmp$23.contTrace.last.next = this;
          this.tmp$23.contTrace.last = this;
          return this.tmp$23
        }
        this.pc = 179;
        continue contLoop;
      } else if (this.pc === 179) {
        this.tmp$23 = runtime.resetDepth(this.tmp$23, this.curDepth$26);
        this.pc = 198;
        continue contLoop;
      } else if (this.pc === 180) {
        this.tmp$24 = runtime.resetDepth(this.tmp$24, this.curDepth$26);
        this.pc = 197;
        continue contLoop;
      } else if (this.pc === 181) {
        this.tmp$25 = runtime.resetDepth(this.tmp$25, this.curDepth$26);
        this.pc = 196;
        continue contLoop;
      } else if (this.pc === 193) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return trins(this.tmp$20, this.xs_$6, this.tmp$21)
      } else if (this.pc === 195) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$20 = NofibPrelude.Cons(this.x$5, this.rev$0);
        if (this.tmp$20 instanceof runtime.EffectSig.class) {
          this.pc = 176;
          this.tmp$20.contTrace.last.next = this;
          this.tmp$20.contTrace.last = this;
          return this.tmp$20
        }
        this.pc = 176;
        continue contLoop;
      } else if (this.pc === 176) {
        this.tmp$20 = runtime.resetDepth(this.tmp$20, this.curDepth$26);
        this.pc = 194;
        continue contLoop;
      } else if (this.pc === 194) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$21 = NofibPrelude.Cons(this.y$9, this.ys_$10);
        if (this.tmp$21 instanceof runtime.EffectSig.class) {
          this.pc = 177;
          this.tmp$21.contTrace.last.next = this;
          this.tmp$21.contTrace.last = this;
          return this.tmp$21
        }
        this.pc = 177;
        continue contLoop;
      } else if (this.pc === 177) {
        this.tmp$21 = runtime.resetDepth(this.tmp$21, this.curDepth$26);
        this.pc = 193;
        continue contLoop;
      } else if (this.pc === 191) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.append(this.tmp$19, this.xs$12)
      } else if (this.pc === 192) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$19 = NofibPrelude.reverse(this.rev$0);
        if (this.tmp$19 instanceof runtime.EffectSig.class) {
          this.pc = 174;
          this.tmp$19.contTrace.last.next = this;
          this.tmp$19.contTrace.last = this;
          return this.tmp$19
        }
        this.pc = 174;
        continue contLoop;
      } else if (this.pc === 174) {
        this.tmp$19 = runtime.resetDepth(this.tmp$19, this.curDepth$26);
        this.pc = 191;
        continue contLoop;
      } else if (this.pc === 173) {
        this.tmp$27 = runtime.resetDepth(this.tmp$27, this.curDepth$26);
        throw this.tmp$27;
      } else if (this.pc === 189) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.append(this.tmp$18, this.xs$12)
      } else if (this.pc === 190) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$18 = NofibPrelude.reverse(this.rev$0);
        if (this.tmp$18 instanceof runtime.EffectSig.class) {
          this.pc = 172;
          this.tmp$18.contTrace.last.next = this;
          this.tmp$18.contTrace.last = this;
          return this.tmp$18
        }
        this.pc = 172;
        continue contLoop;
      } else if (this.pc === 172) {
        this.tmp$18 = runtime.resetDepth(this.tmp$18, this.curDepth$26);
        this.pc = 189;
        continue contLoop;
      } else if (this.pc === 185) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return trins(NofibPrelude.Nil, this.tmp$17, this.ys_$14)
      } else if (this.pc === 186) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$17 = NofibPrelude.append(this.tmp$15, this.tmp$16);
        if (this.tmp$17 instanceof runtime.EffectSig.class) {
          this.pc = 171;
          this.tmp$17.contTrace.last.next = this;
          this.tmp$17.contTrace.last = this;
          return this.tmp$17
        }
        this.pc = 171;
        continue contLoop;
      } else if (this.pc === 188) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$15 = NofibPrelude.reverse(this.rev$0);
        if (this.tmp$15 instanceof runtime.EffectSig.class) {
          this.pc = 169;
          this.tmp$15.contTrace.last.next = this;
          this.tmp$15.contTrace.last = this;
          return this.tmp$15
        }
        this.pc = 169;
        continue contLoop;
      } else if (this.pc === 169) {
        this.tmp$15 = runtime.resetDepth(this.tmp$15, this.curDepth$26);
        this.pc = 187;
        continue contLoop;
      } else if (this.pc === 187) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$16 = NofibPrelude.Cons(this.y$13, NofibPrelude.Nil);
        if (this.tmp$16 instanceof runtime.EffectSig.class) {
          this.pc = 170;
          this.tmp$16.contTrace.last.next = this;
          this.tmp$16.contTrace.last = this;
          return this.tmp$16
        }
        this.pc = 170;
        continue contLoop;
      } else if (this.pc === 170) {
        this.tmp$16 = runtime.resetDepth(this.tmp$16, this.curDepth$26);
        this.pc = 186;
        continue contLoop;
      } else if (this.pc === 171) {
        this.tmp$17 = runtime.resetDepth(this.tmp$17, this.curDepth$26);
        this.pc = 185;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$trins$sorting$_mls_L0_2427_2738$(" + globalThis.Predef.render(this.pc) + ")"; }
};
trins = function trins(rev, xs, ys) {
  let param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 168);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (xs instanceof NofibPrelude.Nil.class) {
    xs1 = xs;
    if (ys instanceof NofibPrelude.Cons.class) {
      param01 = ys.head;
      param11 = ys.tail;
      y1 = param01;
      ys_1 = param11;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = NofibPrelude.reverse(rev);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 169);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = NofibPrelude.Cons(y1, NofibPrelude.Nil);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 170);
        tmp1.contTrace.last = tmp1.contTrace.last.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = NofibPrelude.append(tmp, tmp1);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 171);
        tmp2.contTrace.last = tmp2.contTrace.last.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return trins(NofibPrelude.Nil, tmp2, ys_1)
    } else if (ys instanceof NofibPrelude.Nil.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = NofibPrelude.reverse(rev);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 172);
        tmp3.contTrace.last = tmp3.contTrace.last.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.append(tmp3, xs1)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp11 = new globalThis.Error("match error");
      if (tmp11 instanceof runtime.EffectSig.class) {
        tmp11.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 173);
        tmp11.contTrace.last = tmp11.contTrace.last.next;
        return tmp11
      }
      tmp11 = runtime.resetDepth(tmp11, curDepth);
      throw tmp11;
    }
  } else {
    xs1 = xs;
    if (ys instanceof NofibPrelude.Nil.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp4 = NofibPrelude.reverse(rev);
      if (tmp4 instanceof runtime.EffectSig.class) {
        tmp4.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 174);
        tmp4.contTrace.last = tmp4.contTrace.last.next;
        return tmp4
      }
      tmp4 = runtime.resetDepth(tmp4, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.append(tmp4, xs1)
    } else {
      if (xs instanceof NofibPrelude.Cons.class) {
        param0 = xs.head;
        param1 = xs.tail;
        x = param0;
        xs_ = param1;
        if (ys instanceof NofibPrelude.Cons.class) {
          param01 = ys.head;
          param11 = ys.tail;
          y = param01;
          ys_ = param11;
          runtime.stackDepth = runtime.stackDepth + 1;
          scrut = NofibPrelude.ltList(x, y);
          if (scrut instanceof runtime.EffectSig.class) {
            scrut.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 175);
            scrut.contTrace.last = scrut.contTrace.last.next;
            return scrut
          }
          scrut = runtime.resetDepth(scrut, curDepth);
          if (scrut === true) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp5 = NofibPrelude.Cons(x, rev);
            if (tmp5 instanceof runtime.EffectSig.class) {
              tmp5.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 176);
              tmp5.contTrace.last = tmp5.contTrace.last.next;
              return tmp5
            }
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp6 = NofibPrelude.Cons(y, ys_);
            if (tmp6 instanceof runtime.EffectSig.class) {
              tmp6.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 177);
              tmp6.contTrace.last = tmp6.contTrace.last.next;
              return tmp6
            }
            tmp6 = runtime.resetDepth(tmp6, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            return trins(tmp5, xs_, tmp6)
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp7 = NofibPrelude.reverse(rev);
            if (tmp7 instanceof runtime.EffectSig.class) {
              tmp7.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 178);
              tmp7.contTrace.last = tmp7.contTrace.last.next;
              return tmp7
            }
            tmp7 = runtime.resetDepth(tmp7, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp8 = NofibPrelude.Cons(x, xs_);
            if (tmp8 instanceof runtime.EffectSig.class) {
              tmp8.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 179);
              tmp8.contTrace.last = tmp8.contTrace.last.next;
              return tmp8
            }
            tmp8 = runtime.resetDepth(tmp8, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp9 = NofibPrelude.Cons(y, tmp8);
            if (tmp9 instanceof runtime.EffectSig.class) {
              tmp9.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 180);
              tmp9.contTrace.last = tmp9.contTrace.last.next;
              return tmp9
            }
            tmp9 = runtime.resetDepth(tmp9, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp10 = NofibPrelude.append(tmp7, tmp9);
            if (tmp10 instanceof runtime.EffectSig.class) {
              tmp10.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 181);
              tmp10.contTrace.last = tmp10.contTrace.last.next;
              return tmp10
            }
            tmp10 = runtime.resetDepth(tmp10, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            return trins(NofibPrelude.Nil, tmp10, ys_)
          }
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp12 = new globalThis.Error("match error");
          if (tmp12 instanceof runtime.EffectSig.class) {
            tmp12.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 182);
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
          tmp13.contTrace.last.next = Cont$func$trins$sorting$_mls_L0_2427_2738$$(rev, xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, curDepth, tmp11, tmp12, tmp13, stackDelayRes, 183);
          tmp13.contTrace.last = tmp13.contTrace.last.next;
          return tmp13
        }
        tmp13 = runtime.resetDepth(tmp13, curDepth);
        throw tmp13;
      }
    }
  }
};
insertSort = function insertSort(xss) {
  let param0, param1, x, xs, tmp, curDepth, tmp1, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$insertSort$sorting$_mls_L0_2361_2767$$(xss, param0, param1, x, xs, tmp, curDepth, tmp1, stackDelayRes, 167);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (xss instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (xss instanceof NofibPrelude.Cons.class) {
    param0 = xss.head;
    param1 = xss.tail;
    x = param0;
    xs = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = NofibPrelude.Cons(x, NofibPrelude.Nil);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$insertSort$sorting$_mls_L0_2361_2767$$(xss, param0, param1, x, xs, tmp, curDepth, tmp1, stackDelayRes, 202);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return trins(NofibPrelude.Nil, tmp, xs)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = new globalThis.Error("match error");
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$insertSort$sorting$_mls_L0_2361_2767$$(xss, param0, param1, x, xs, tmp, curDepth, tmp1, stackDelayRes, 203);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    throw tmp1;
  }
};
Cont$func$treeSort$sorting$_mls_L0_2911_3309$$ = function Cont$func$treeSort$sorting$_mls_L0_2911_3309$$(param$0, tmp$1, curDepth$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$treeSort$sorting$_mls_L0_2911_3309$1.class(pc);
  return tmp(param$0, tmp$1, curDepth$2, stackDelayRes$3)
};
Cont$func$treeSort$sorting$_mls_L0_2911_3309$$ctor = function Cont$func$treeSort$sorting$_mls_L0_2911_3309$$ctor(param$0, tmp$1, curDepth$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$treeSort$sorting$_mls_L0_2911_3309$1.class(pc);
    return tmp(param$0, tmp$1, curDepth$2, stackDelayRes$3)
  }
};
Cont$func$treeSort$sorting$_mls_L0_2911_3309$1 = function Cont$func$treeSort$sorting$_mls_L0_2911_3309$(pc1) {
  return (param$01, tmp$11, curDepth$21, stackDelayRes$31) => {
    return new Cont$func$treeSort$sorting$_mls_L0_2911_3309$.class(pc1)(param$01, tmp$11, curDepth$21, stackDelayRes$31);
  }
};
Cont$func$treeSort$sorting$_mls_L0_2911_3309$1.class = class Cont$func$treeSort$sorting$_mls_L0_2911_3309$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (param$0, tmp$1, curDepth$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.param$0 = param$0;
      this.tmp$1 = tmp$1;
      this.curDepth$2 = curDepth$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 207) {
      this.stackDelayRes$3 = value$;
    } else if (this.pc === 232) {
      this.tmp$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 207) {
        this.pc = 234;
        continue contLoop;
      } else if (this.pc === 233) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return readTree(this.tmp$1)
      } else if (this.pc === 234) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = mkTree(this.param$0);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 232;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 232;
        continue contLoop;
      } else if (this.pc === 232) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$2);
        this.pc = 233;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$treeSort$sorting$_mls_L0_2911_3309$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$mkTree$sorting$_mls_L0_2935_3179$$ = function Cont$func$mkTree$sorting$_mls_L0_2935_3179$$(innerparam$0, stackDelayRes$1, pc) {
  let tmp;
  tmp = new Cont$func$mkTree$sorting$_mls_L0_2935_3179$1.class(pc);
  return tmp(innerparam$0, stackDelayRes$1)
};
Cont$func$mkTree$sorting$_mls_L0_2935_3179$$ctor = function Cont$func$mkTree$sorting$_mls_L0_2935_3179$$ctor(innerparam$0, stackDelayRes$1) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$mkTree$sorting$_mls_L0_2935_3179$1.class(pc);
    return tmp(innerparam$0, stackDelayRes$1)
  }
};
Cont$func$mkTree$sorting$_mls_L0_2935_3179$1 = function Cont$func$mkTree$sorting$_mls_L0_2935_3179$(pc1) {
  return (innerparam$01, stackDelayRes$11) => {
    return new Cont$func$mkTree$sorting$_mls_L0_2935_3179$.class(pc1)(innerparam$01, stackDelayRes$11);
  }
};
Cont$func$mkTree$sorting$_mls_L0_2935_3179$1.class = class Cont$func$mkTree$sorting$_mls_L0_2935_3179$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (innerparam$0, stackDelayRes$1) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.innerparam$0 = innerparam$0;
      this.stackDelayRes$1 = stackDelayRes$1;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 208) {
      this.stackDelayRes$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 208) {
        this.pc = 221;
        continue contLoop;
      } else if (this.pc === 221) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.foldr(to_tree, Tip1, this.innerparam$0)
      }
      break;
    }
  }
  toString() { return "Cont$func$mkTree$sorting$_mls_L0_2935_3179$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$to_tree$sorting$_mls_L0_2964_3143$$ = function Cont$func$to_tree$sorting$_mls_L0_2964_3143$$(x$0, t$1, param0$2, param1$3, param2$4, y$5, l$6, r$7, scrut$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13, pc) {
  let tmp;
  tmp = new Cont$func$to_tree$sorting$_mls_L0_2964_3143$1.class(pc);
  return tmp(x$0, t$1, param0$2, param1$3, param2$4, y$5, l$6, r$7, scrut$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13)
};
Cont$func$to_tree$sorting$_mls_L0_2964_3143$$ctor = function Cont$func$to_tree$sorting$_mls_L0_2964_3143$$ctor(x$0, t$1, param0$2, param1$3, param2$4, y$5, l$6, r$7, scrut$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$to_tree$sorting$_mls_L0_2964_3143$1.class(pc);
    return tmp(x$0, t$1, param0$2, param1$3, param2$4, y$5, l$6, r$7, scrut$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13)
  }
};
Cont$func$to_tree$sorting$_mls_L0_2964_3143$1 = function Cont$func$to_tree$sorting$_mls_L0_2964_3143$(pc1) {
  return (x$01, t$11, param0$21, param1$31, param2$41, y$51, l$61, r$71, scrut$81, tmp$91, tmp$101, curDepth$111, tmp$121, stackDelayRes$131) => {
    return new Cont$func$to_tree$sorting$_mls_L0_2964_3143$.class(pc1)(x$01, t$11, param0$21, param1$31, param2$41, y$51, l$61, r$71, scrut$81, tmp$91, tmp$101, curDepth$111, tmp$121, stackDelayRes$131);
  }
};
Cont$func$to_tree$sorting$_mls_L0_2964_3143$1.class = class Cont$func$to_tree$sorting$_mls_L0_2964_3143$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, t$1, param0$2, param1$3, param2$4, y$5, l$6, r$7, scrut$8, tmp$9, tmp$10, curDepth$11, tmp$12, stackDelayRes$13) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$0 = x$0;
      this.t$1 = t$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.param2$4 = param2$4;
      this.y$5 = y$5;
      this.l$6 = l$6;
      this.r$7 = r$7;
      this.scrut$8 = scrut$8;
      this.tmp$9 = tmp$9;
      this.tmp$10 = tmp$10;
      this.curDepth$11 = curDepth$11;
      this.tmp$12 = tmp$12;
      this.stackDelayRes$13 = stackDelayRes$13;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 209) {
      this.stackDelayRes$13 = value$;
    } else if (this.pc === 213) {
      this.tmp$12 = value$;
    } else if (this.pc === 210) {
      this.scrut$8 = value$;
    } else if (this.pc === 212) {
      this.tmp$10 = value$;
    } else if (this.pc === 211) {
      this.tmp$9 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 209) {
        if (this.t$1 instanceof Tip1.class) {
          this.pc = 215;
          continue contLoop;
        } else if (this.t$1 instanceof Branch1.class) {
          this.param0$2 = this.t$1.a;
          this.param1$3 = this.t$1.l;
          this.param2$4 = this.t$1.r;
          this.y$5 = this.param0$2;
          this.l$6 = this.param1$3;
          this.r$7 = this.param2$4;
          this.pc = 220;
          continue contLoop;
          this.pc = 214;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$12 = new globalThis.Error("match error");
          if (this.tmp$12 instanceof runtime.EffectSig.class) {
            this.pc = 213;
            this.tmp$12.contTrace.last.next = this;
            this.tmp$12.contTrace.last = this;
            return this.tmp$12
          }
          this.pc = 213;
          continue contLoop;
        }
        this.pc = 214;
        continue contLoop;
      } else if (this.pc === 214) {
        break contLoop;
      } else if (this.pc === 213) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$11);
        throw this.tmp$12;
      } else if (this.pc === 220) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$8 = leList(this.x$0, this.y$5);
        if (this.scrut$8 instanceof runtime.EffectSig.class) {
          this.pc = 210;
          this.scrut$8.contTrace.last.next = this;
          this.scrut$8.contTrace.last = this;
          return this.scrut$8
        }
        this.pc = 210;
        continue contLoop;
      } else if (this.pc === 210) {
        this.scrut$8 = runtime.resetDepth(this.scrut$8, this.curDepth$11);
        if (this.scrut$8 === true) {
          this.pc = 217;
          continue contLoop;
        } else {
          this.pc = 219;
          continue contLoop;
        }
        this.pc = 214;
        continue contLoop;
      } else if (this.pc === 218) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(this.y$5, this.l$6, this.tmp$10)
      } else if (this.pc === 219) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$10 = to_tree(this.x$0, this.r$7);
        if (this.tmp$10 instanceof runtime.EffectSig.class) {
          this.pc = 212;
          this.tmp$10.contTrace.last.next = this;
          this.tmp$10.contTrace.last = this;
          return this.tmp$10
        }
        this.pc = 212;
        continue contLoop;
      } else if (this.pc === 212) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$11);
        this.pc = 218;
        continue contLoop;
      } else if (this.pc === 216) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(this.y$5, this.tmp$9, this.r$7)
      } else if (this.pc === 217) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = to_tree(this.x$0, this.l$6);
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 211;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 211;
        continue contLoop;
      } else if (this.pc === 211) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$11);
        this.pc = 216;
        continue contLoop;
      } else if (this.pc === 215) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(this.x$0, Tip1, Tip1)
      }
      break;
    }
  }
  toString() { return "Cont$func$to_tree$sorting$_mls_L0_2964_3143$(" + globalThis.Predef.render(this.pc) + ")"; }
};
to_tree = function to_tree(x, t) {
  let param0, param1, param2, y, l, r, scrut, tmp, tmp1, curDepth, tmp2, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$to_tree$sorting$_mls_L0_2964_3143$$(x, t, param0, param1, param2, y, l, r, scrut, tmp, tmp1, curDepth, tmp2, stackDelayRes, 209);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (t instanceof Tip1.class) {
    runtime.stackDepth = runtime.stackDepth + 1;
    return Branch1(x, Tip1, Tip1)
  } else if (t instanceof Branch1.class) {
    param0 = t.a;
    param1 = t.l;
    param2 = t.r;
    y = param0;
    l = param1;
    r = param2;
    runtime.stackDepth = runtime.stackDepth + 1;
    scrut = leList(x, y);
    if (scrut instanceof runtime.EffectSig.class) {
      scrut.contTrace.last.next = Cont$func$to_tree$sorting$_mls_L0_2964_3143$$(x, t, param0, param1, param2, y, l, r, scrut, tmp, tmp1, curDepth, tmp2, stackDelayRes, 210);
      scrut.contTrace.last = scrut.contTrace.last.next;
      return scrut
    }
    scrut = runtime.resetDepth(scrut, curDepth);
    if (scrut === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = to_tree(x, l);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$to_tree$sorting$_mls_L0_2964_3143$$(x, t, param0, param1, param2, y, l, r, scrut, tmp, tmp1, curDepth, tmp2, stackDelayRes, 211);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return Branch1(y, tmp, r)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = to_tree(x, r);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = Cont$func$to_tree$sorting$_mls_L0_2964_3143$$(x, t, param0, param1, param2, y, l, r, scrut, tmp, tmp1, curDepth, tmp2, stackDelayRes, 212);
        tmp1.contTrace.last = tmp1.contTrace.last.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return Branch1(y, l, tmp1)
    }
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = new globalThis.Error("match error");
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$to_tree$sorting$_mls_L0_2964_3143$$(x, t, param0, param1, param2, y, l, r, scrut, tmp, tmp1, curDepth, tmp2, stackDelayRes, 213);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    throw tmp2;
  }
};
mkTree = function mkTree(innerparam) {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$mkTree$sorting$_mls_L0_2935_3179$$(innerparam, stackDelayRes, 208);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return NofibPrelude.foldr(to_tree, Tip1, innerparam)
};
Cont$func$readTree$sorting$_mls_L0_3186_3283$$ = function Cont$func$readTree$sorting$_mls_L0_3186_3283$$(t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, tmp$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12, pc) {
  let tmp;
  tmp = new Cont$func$readTree$sorting$_mls_L0_3186_3283$1.class(pc);
  return tmp(t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, tmp$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12)
};
Cont$func$readTree$sorting$_mls_L0_3186_3283$$ctor = function Cont$func$readTree$sorting$_mls_L0_3186_3283$$ctor(t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, tmp$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$readTree$sorting$_mls_L0_3186_3283$1.class(pc);
    return tmp(t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, tmp$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12)
  }
};
Cont$func$readTree$sorting$_mls_L0_3186_3283$1 = function Cont$func$readTree$sorting$_mls_L0_3186_3283$(pc1) {
  return (t$01, param0$11, param1$21, param2$31, x$41, l$51, r$61, tmp$71, tmp$81, tmp$91, curDepth$101, tmp$111, stackDelayRes$121) => {
    return new Cont$func$readTree$sorting$_mls_L0_3186_3283$.class(pc1)(t$01, param0$11, param1$21, param2$31, x$41, l$51, r$61, tmp$71, tmp$81, tmp$91, curDepth$101, tmp$111, stackDelayRes$121);
  }
};
Cont$func$readTree$sorting$_mls_L0_3186_3283$1.class = class Cont$func$readTree$sorting$_mls_L0_3186_3283$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, tmp$7, tmp$8, tmp$9, curDepth$10, tmp$11, stackDelayRes$12) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.t$0 = t$0;
      this.param0$1 = param0$1;
      this.param1$2 = param1$2;
      this.param2$3 = param2$3;
      this.x$4 = x$4;
      this.l$5 = l$5;
      this.r$6 = r$6;
      this.tmp$7 = tmp$7;
      this.tmp$8 = tmp$8;
      this.tmp$9 = tmp$9;
      this.curDepth$10 = curDepth$10;
      this.tmp$11 = tmp$11;
      this.stackDelayRes$12 = stackDelayRes$12;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 222) {
      this.stackDelayRes$12 = value$;
    } else if (this.pc === 226) {
      this.tmp$11 = value$;
    } else if (this.pc === 223) {
      this.tmp$7 = value$;
    } else if (this.pc === 224) {
      this.tmp$8 = value$;
    } else if (this.pc === 225) {
      this.tmp$9 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 222) {
        if (this.t$0 instanceof Tip1.class) {
          return NofibPrelude.Nil
        } else if (this.t$0 instanceof Branch1.class) {
          this.param0$1 = this.t$0.a;
          this.param1$2 = this.t$0.l;
          this.param2$3 = this.t$0.r;
          this.x$4 = this.param0$1;
          this.l$5 = this.param1$2;
          this.r$6 = this.param2$3;
          this.pc = 231;
          continue contLoop;
          this.pc = 227;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$11 = new globalThis.Error("match error");
          if (this.tmp$11 instanceof runtime.EffectSig.class) {
            this.pc = 226;
            this.tmp$11.contTrace.last.next = this;
            this.tmp$11.contTrace.last = this;
            return this.tmp$11
          }
          this.pc = 226;
          continue contLoop;
        }
        this.pc = 227;
        continue contLoop;
      } else if (this.pc === 227) {
        break contLoop;
      } else if (this.pc === 226) {
        this.tmp$11 = runtime.resetDepth(this.tmp$11, this.curDepth$10);
        throw this.tmp$11;
      } else if (this.pc === 228) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.append(this.tmp$7, this.tmp$9)
      } else if (this.pc === 231) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = readTree(this.l$5);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 223;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 223;
        continue contLoop;
      } else if (this.pc === 223) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$10);
        this.pc = 230;
        continue contLoop;
      } else if (this.pc === 229) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = NofibPrelude.Cons(this.x$4, this.tmp$8);
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 225;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 225;
        continue contLoop;
      } else if (this.pc === 230) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = readTree(this.r$6);
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 224;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 224;
        continue contLoop;
      } else if (this.pc === 224) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$10);
        this.pc = 229;
        continue contLoop;
      } else if (this.pc === 225) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$10);
        this.pc = 228;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$readTree$sorting$_mls_L0_3186_3283$(" + globalThis.Predef.render(this.pc) + ")"; }
};
readTree = function readTree(t) {
  let param0, param1, param2, x, l, r, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$readTree$sorting$_mls_L0_3186_3283$$(t, param0, param1, param2, x, l, r, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 222);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (t instanceof Tip1.class) {
    return NofibPrelude.Nil
  } else if (t instanceof Branch1.class) {
    param0 = t.a;
    param1 = t.l;
    param2 = t.r;
    x = param0;
    l = param1;
    r = param2;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = readTree(l);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$readTree$sorting$_mls_L0_3186_3283$$(t, param0, param1, param2, x, l, r, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 223);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = readTree(r);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$readTree$sorting$_mls_L0_3186_3283$$(t, param0, param1, param2, x, l, r, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 224);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = NofibPrelude.Cons(x, tmp1);
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$readTree$sorting$_mls_L0_3186_3283$$(t, param0, param1, param2, x, l, r, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 225);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.append(tmp, tmp2)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp3 = new globalThis.Error("match error");
    if (tmp3 instanceof runtime.EffectSig.class) {
      tmp3.contTrace.last.next = Cont$func$readTree$sorting$_mls_L0_3186_3283$$(t, param0, param1, param2, x, l, r, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 226);
      tmp3.contTrace.last = tmp3.contTrace.last.next;
      return tmp3
    }
    tmp3 = runtime.resetDepth(tmp3, curDepth);
    throw tmp3;
  }
};
treeSort = function treeSort(param) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$treeSort$sorting$_mls_L0_2911_3309$$(param, tmp, curDepth, stackDelayRes, 207);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = mkTree(param);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$treeSort$sorting$_mls_L0_2911_3309$$(param, tmp, curDepth, stackDelayRes, 232);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return readTree(tmp)
};
Cont$func$treeSort2$sorting$_mls_L0_3509_4043$$ = function Cont$func$treeSort2$sorting$_mls_L0_3509_4043$$(param$0, tmp$1, curDepth$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$treeSort2$sorting$_mls_L0_3509_4043$1.class(pc);
  return tmp(param$0, tmp$1, curDepth$2, stackDelayRes$3)
};
Cont$func$treeSort2$sorting$_mls_L0_3509_4043$$ctor = function Cont$func$treeSort2$sorting$_mls_L0_3509_4043$$ctor(param$0, tmp$1, curDepth$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$treeSort2$sorting$_mls_L0_3509_4043$1.class(pc);
    return tmp(param$0, tmp$1, curDepth$2, stackDelayRes$3)
  }
};
Cont$func$treeSort2$sorting$_mls_L0_3509_4043$1 = function Cont$func$treeSort2$sorting$_mls_L0_3509_4043$(pc1) {
  return (param$01, tmp$11, curDepth$21, stackDelayRes$31) => {
    return new Cont$func$treeSort2$sorting$_mls_L0_3509_4043$.class(pc1)(param$01, tmp$11, curDepth$21, stackDelayRes$31);
  }
};
Cont$func$treeSort2$sorting$_mls_L0_3509_4043$1.class = class Cont$func$treeSort2$sorting$_mls_L0_3509_4043$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (param$0, tmp$1, curDepth$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.param$0 = param$0;
      this.tmp$1 = tmp$1;
      this.curDepth$2 = curDepth$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 235) {
      this.stackDelayRes$3 = value$;
    } else if (this.pc === 269) {
      this.tmp$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 235) {
        this.pc = 271;
        continue contLoop;
      } else if (this.pc === 270) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return readTree1(this.tmp$1)
      } else if (this.pc === 271) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = mkTree1(this.param$0);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 269;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 269;
        continue contLoop;
      } else if (this.pc === 269) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$2);
        this.pc = 270;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$treeSort2$sorting$_mls_L0_3509_4043$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$mkTree$sorting$_mls_L0_3534_3884$$ = function Cont$func$mkTree$sorting$_mls_L0_3534_3884$$(innerparam$0, stackDelayRes$1, pc) {
  let tmp;
  tmp = new Cont$func$mkTree$sorting$_mls_L0_3534_3884$1.class(pc);
  return tmp(innerparam$0, stackDelayRes$1)
};
Cont$func$mkTree$sorting$_mls_L0_3534_3884$$ctor = function Cont$func$mkTree$sorting$_mls_L0_3534_3884$$ctor(innerparam$0, stackDelayRes$1) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$mkTree$sorting$_mls_L0_3534_3884$1.class(pc);
    return tmp(innerparam$0, stackDelayRes$1)
  }
};
Cont$func$mkTree$sorting$_mls_L0_3534_3884$1 = function Cont$func$mkTree$sorting$_mls_L0_3534_3884$(pc1) {
  return (innerparam$01, stackDelayRes$11) => {
    return new Cont$func$mkTree$sorting$_mls_L0_3534_3884$.class(pc1)(innerparam$01, stackDelayRes$11);
  }
};
Cont$func$mkTree$sorting$_mls_L0_3534_3884$1.class = class Cont$func$mkTree$sorting$_mls_L0_3534_3884$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (innerparam$0, stackDelayRes$1) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.innerparam$0 = innerparam$0;
      this.stackDelayRes$1 = stackDelayRes$1;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 236) {
      this.stackDelayRes$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 236) {
        this.pc = 257;
        continue contLoop;
      } else if (this.pc === 257) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.foldr(to_tree1, Tip21, this.innerparam$0)
      }
      break;
    }
  }
  toString() { return "Cont$func$mkTree$sorting$_mls_L0_3534_3884$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$to_tree$sorting$_mls_L0_3563_3847$$ = function Cont$func$to_tree$sorting$_mls_L0_3563_3847$$(x$0, t$1, param0$2, param1$3, param2$4, y$5, l$6, r$7, scrut$8, param0$9, y$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, tmp$17, stackDelayRes$18, pc) {
  let tmp;
  tmp = new Cont$func$to_tree$sorting$_mls_L0_3563_3847$1.class(pc);
  return tmp(x$0, t$1, param0$2, param1$3, param2$4, y$5, l$6, r$7, scrut$8, param0$9, y$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, tmp$17, stackDelayRes$18)
};
Cont$func$to_tree$sorting$_mls_L0_3563_3847$$ctor = function Cont$func$to_tree$sorting$_mls_L0_3563_3847$$ctor(x$0, t$1, param0$2, param1$3, param2$4, y$5, l$6, r$7, scrut$8, param0$9, y$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, tmp$17, stackDelayRes$18) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$to_tree$sorting$_mls_L0_3563_3847$1.class(pc);
    return tmp(x$0, t$1, param0$2, param1$3, param2$4, y$5, l$6, r$7, scrut$8, param0$9, y$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, tmp$17, stackDelayRes$18)
  }
};
Cont$func$to_tree$sorting$_mls_L0_3563_3847$1 = function Cont$func$to_tree$sorting$_mls_L0_3563_3847$(pc1) {
  return (x$01, t$11, param0$21, param1$31, param2$41, y$51, l$61, r$71, scrut$81, param0$91, y$101, scrut$111, tmp$121, tmp$131, tmp$141, tmp$151, curDepth$161, tmp$171, stackDelayRes$181) => {
    return new Cont$func$to_tree$sorting$_mls_L0_3563_3847$.class(pc1)(x$01, t$11, param0$21, param1$31, param2$41, y$51, l$61, r$71, scrut$81, param0$91, y$101, scrut$111, tmp$121, tmp$131, tmp$141, tmp$151, curDepth$161, tmp$171, stackDelayRes$181);
  }
};
Cont$func$to_tree$sorting$_mls_L0_3563_3847$1.class = class Cont$func$to_tree$sorting$_mls_L0_3563_3847$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (x$0, t$1, param0$2, param1$3, param2$4, y$5, l$6, r$7, scrut$8, param0$9, y$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, curDepth$16, tmp$17, stackDelayRes$18) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.x$0 = x$0;
      this.t$1 = t$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.param2$4 = param2$4;
      this.y$5 = y$5;
      this.l$6 = l$6;
      this.r$7 = r$7;
      this.scrut$8 = scrut$8;
      this.param0$9 = param0$9;
      this.y$10 = y$10;
      this.scrut$11 = scrut$11;
      this.tmp$12 = tmp$12;
      this.tmp$13 = tmp$13;
      this.tmp$14 = tmp$14;
      this.tmp$15 = tmp$15;
      this.curDepth$16 = curDepth$16;
      this.tmp$17 = tmp$17;
      this.stackDelayRes$18 = stackDelayRes$18;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 237) {
      this.stackDelayRes$18 = value$;
    } else if (this.pc === 244) {
      this.tmp$17 = value$;
    } else if (this.pc === 241) {
      this.scrut$8 = value$;
    } else if (this.pc === 243) {
      this.tmp$15 = value$;
    } else if (this.pc === 242) {
      this.tmp$14 = value$;
    } else if (this.pc === 238) {
      this.scrut$11 = value$;
    } else if (this.pc === 240) {
      this.tmp$13 = value$;
    } else if (this.pc === 239) {
      this.tmp$12 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 237) {
        if (this.t$1 instanceof Tip21.class) {
          this.pc = 246;
          continue contLoop;
        } else if (this.t$1 instanceof Twig21.class) {
          this.param0$9 = this.t$1.a;
          this.y$10 = this.param0$9;
          this.pc = 251;
          continue contLoop;
          this.pc = 245;
          continue contLoop;
        } else if (this.t$1 instanceof Branch21.class) {
          this.param0$2 = this.t$1.a;
          this.param1$3 = this.t$1.l;
          this.param2$4 = this.t$1.r;
          this.y$5 = this.param0$2;
          this.l$6 = this.param1$3;
          this.r$7 = this.param2$4;
          this.pc = 256;
          continue contLoop;
          this.pc = 245;
          continue contLoop;
          this.pc = 245;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$17 = new globalThis.Error("match error");
          if (this.tmp$17 instanceof runtime.EffectSig.class) {
            this.pc = 244;
            this.tmp$17.contTrace.last.next = this;
            this.tmp$17.contTrace.last = this;
            return this.tmp$17
          }
          this.pc = 244;
          continue contLoop;
        }
        this.pc = 245;
        continue contLoop;
      } else if (this.pc === 245) {
        break contLoop;
      } else if (this.pc === 244) {
        this.tmp$17 = runtime.resetDepth(this.tmp$17, this.curDepth$16);
        throw this.tmp$17;
      } else if (this.pc === 256) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$8 = leList(this.x$0, this.y$5);
        if (this.scrut$8 instanceof runtime.EffectSig.class) {
          this.pc = 241;
          this.scrut$8.contTrace.last.next = this;
          this.scrut$8.contTrace.last = this;
          return this.scrut$8
        }
        this.pc = 241;
        continue contLoop;
      } else if (this.pc === 241) {
        this.scrut$8 = runtime.resetDepth(this.scrut$8, this.curDepth$16);
        if (this.scrut$8 === true) {
          this.pc = 253;
          continue contLoop;
        } else {
          this.pc = 255;
          continue contLoop;
        }
        this.pc = 245;
        continue contLoop;
      } else if (this.pc === 254) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch21(this.y$5, this.l$6, this.tmp$15)
      } else if (this.pc === 255) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$15 = to_tree1(this.x$0, this.r$7);
        if (this.tmp$15 instanceof runtime.EffectSig.class) {
          this.pc = 243;
          this.tmp$15.contTrace.last.next = this;
          this.tmp$15.contTrace.last = this;
          return this.tmp$15
        }
        this.pc = 243;
        continue contLoop;
      } else if (this.pc === 243) {
        this.tmp$15 = runtime.resetDepth(this.tmp$15, this.curDepth$16);
        this.pc = 254;
        continue contLoop;
      } else if (this.pc === 252) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch21(this.y$5, this.tmp$14, this.r$7)
      } else if (this.pc === 253) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$14 = to_tree1(this.x$0, this.l$6);
        if (this.tmp$14 instanceof runtime.EffectSig.class) {
          this.pc = 242;
          this.tmp$14.contTrace.last.next = this;
          this.tmp$14.contTrace.last = this;
          return this.tmp$14
        }
        this.pc = 242;
        continue contLoop;
      } else if (this.pc === 242) {
        this.tmp$14 = runtime.resetDepth(this.tmp$14, this.curDepth$16);
        this.pc = 252;
        continue contLoop;
      } else if (this.pc === 251) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$11 = leList(this.x$0, this.y$10);
        if (this.scrut$11 instanceof runtime.EffectSig.class) {
          this.pc = 238;
          this.scrut$11.contTrace.last.next = this;
          this.scrut$11.contTrace.last = this;
          return this.scrut$11
        }
        this.pc = 238;
        continue contLoop;
      } else if (this.pc === 238) {
        this.scrut$11 = runtime.resetDepth(this.scrut$11, this.curDepth$16);
        if (this.scrut$11 === true) {
          this.pc = 248;
          continue contLoop;
        } else {
          this.pc = 250;
          continue contLoop;
        }
        this.pc = 245;
        continue contLoop;
      } else if (this.pc === 249) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch21(this.y$10, Tip21, this.tmp$13)
      } else if (this.pc === 250) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$13 = Twig21(this.x$0);
        if (this.tmp$13 instanceof runtime.EffectSig.class) {
          this.pc = 240;
          this.tmp$13.contTrace.last.next = this;
          this.tmp$13.contTrace.last = this;
          return this.tmp$13
        }
        this.pc = 240;
        continue contLoop;
      } else if (this.pc === 240) {
        this.tmp$13 = runtime.resetDepth(this.tmp$13, this.curDepth$16);
        this.pc = 249;
        continue contLoop;
      } else if (this.pc === 247) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch21(this.y$10, this.tmp$12, Tip21)
      } else if (this.pc === 248) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$12 = Twig21(this.x$0);
        if (this.tmp$12 instanceof runtime.EffectSig.class) {
          this.pc = 239;
          this.tmp$12.contTrace.last.next = this;
          this.tmp$12.contTrace.last = this;
          return this.tmp$12
        }
        this.pc = 239;
        continue contLoop;
      } else if (this.pc === 239) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$16);
        this.pc = 247;
        continue contLoop;
      } else if (this.pc === 246) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Twig21(this.x$0)
      }
      break;
    }
  }
  toString() { return "Cont$func$to_tree$sorting$_mls_L0_3563_3847$(" + globalThis.Predef.render(this.pc) + ")"; }
};
to_tree1 = function to_tree(x, t) {
  let param0, param1, param2, y, l, r, scrut, param01, y1, scrut1, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$to_tree$sorting$_mls_L0_3563_3847$$(x, t, param0, param1, param2, y, l, r, scrut, param01, y1, scrut1, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, stackDelayRes, 237);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (t instanceof Tip21.class) {
    runtime.stackDepth = runtime.stackDepth + 1;
    return Twig21(x)
  } else if (t instanceof Twig21.class) {
    param01 = t.a;
    y1 = param01;
    runtime.stackDepth = runtime.stackDepth + 1;
    scrut1 = leList(x, y1);
    if (scrut1 instanceof runtime.EffectSig.class) {
      scrut1.contTrace.last.next = Cont$func$to_tree$sorting$_mls_L0_3563_3847$$(x, t, param0, param1, param2, y, l, r, scrut, param01, y1, scrut1, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, stackDelayRes, 238);
      scrut1.contTrace.last = scrut1.contTrace.last.next;
      return scrut1
    }
    scrut1 = runtime.resetDepth(scrut1, curDepth);
    if (scrut1 === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = Twig21(x);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$to_tree$sorting$_mls_L0_3563_3847$$(x, t, param0, param1, param2, y, l, r, scrut, param01, y1, scrut1, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, stackDelayRes, 239);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return Branch21(y1, tmp, Tip21)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp1 = Twig21(x);
      if (tmp1 instanceof runtime.EffectSig.class) {
        tmp1.contTrace.last.next = Cont$func$to_tree$sorting$_mls_L0_3563_3847$$(x, t, param0, param1, param2, y, l, r, scrut, param01, y1, scrut1, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, stackDelayRes, 240);
        tmp1.contTrace.last = tmp1.contTrace.last.next;
        return tmp1
      }
      tmp1 = runtime.resetDepth(tmp1, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return Branch21(y1, Tip21, tmp1)
    }
  } else if (t instanceof Branch21.class) {
    param0 = t.a;
    param1 = t.l;
    param2 = t.r;
    y = param0;
    l = param1;
    r = param2;
    runtime.stackDepth = runtime.stackDepth + 1;
    scrut = leList(x, y);
    if (scrut instanceof runtime.EffectSig.class) {
      scrut.contTrace.last.next = Cont$func$to_tree$sorting$_mls_L0_3563_3847$$(x, t, param0, param1, param2, y, l, r, scrut, param01, y1, scrut1, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, stackDelayRes, 241);
      scrut.contTrace.last = scrut.contTrace.last.next;
      return scrut
    }
    scrut = runtime.resetDepth(scrut, curDepth);
    if (scrut === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp2 = to_tree1(x, l);
      if (tmp2 instanceof runtime.EffectSig.class) {
        tmp2.contTrace.last.next = Cont$func$to_tree$sorting$_mls_L0_3563_3847$$(x, t, param0, param1, param2, y, l, r, scrut, param01, y1, scrut1, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, stackDelayRes, 242);
        tmp2.contTrace.last = tmp2.contTrace.last.next;
        return tmp2
      }
      tmp2 = runtime.resetDepth(tmp2, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return Branch21(y, tmp2, r)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp3 = to_tree1(x, r);
      if (tmp3 instanceof runtime.EffectSig.class) {
        tmp3.contTrace.last.next = Cont$func$to_tree$sorting$_mls_L0_3563_3847$$(x, t, param0, param1, param2, y, l, r, scrut, param01, y1, scrut1, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, stackDelayRes, 243);
        tmp3.contTrace.last = tmp3.contTrace.last.next;
        return tmp3
      }
      tmp3 = runtime.resetDepth(tmp3, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return Branch21(y, l, tmp3)
    }
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp4 = new globalThis.Error("match error");
    if (tmp4 instanceof runtime.EffectSig.class) {
      tmp4.contTrace.last.next = Cont$func$to_tree$sorting$_mls_L0_3563_3847$$(x, t, param0, param1, param2, y, l, r, scrut, param01, y1, scrut1, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, stackDelayRes, 244);
      tmp4.contTrace.last = tmp4.contTrace.last.next;
      return tmp4
    }
    tmp4 = runtime.resetDepth(tmp4, curDepth);
    throw tmp4;
  }
};
mkTree1 = function mkTree(innerparam) {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$mkTree$sorting$_mls_L0_3534_3884$$(innerparam, stackDelayRes, 236);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return NofibPrelude.foldr(to_tree1, Tip21, innerparam)
};
Cont$func$readTree$sorting$_mls_L0_3891_4017$$ = function Cont$func$readTree$sorting$_mls_L0_3891_4017$$(t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, param0$7, x$8, tmp$9, tmp$10, tmp$11, curDepth$12, tmp$13, stackDelayRes$14, pc) {
  let tmp;
  tmp = new Cont$func$readTree$sorting$_mls_L0_3891_4017$1.class(pc);
  return tmp(t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, param0$7, x$8, tmp$9, tmp$10, tmp$11, curDepth$12, tmp$13, stackDelayRes$14)
};
Cont$func$readTree$sorting$_mls_L0_3891_4017$$ctor = function Cont$func$readTree$sorting$_mls_L0_3891_4017$$ctor(t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, param0$7, x$8, tmp$9, tmp$10, tmp$11, curDepth$12, tmp$13, stackDelayRes$14) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$readTree$sorting$_mls_L0_3891_4017$1.class(pc);
    return tmp(t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, param0$7, x$8, tmp$9, tmp$10, tmp$11, curDepth$12, tmp$13, stackDelayRes$14)
  }
};
Cont$func$readTree$sorting$_mls_L0_3891_4017$1 = function Cont$func$readTree$sorting$_mls_L0_3891_4017$(pc1) {
  return (t$01, param0$11, param1$21, param2$31, x$41, l$51, r$61, param0$71, x$81, tmp$91, tmp$101, tmp$111, curDepth$121, tmp$131, stackDelayRes$141) => {
    return new Cont$func$readTree$sorting$_mls_L0_3891_4017$.class(pc1)(t$01, param0$11, param1$21, param2$31, x$41, l$51, r$61, param0$71, x$81, tmp$91, tmp$101, tmp$111, curDepth$121, tmp$131, stackDelayRes$141);
  }
};
Cont$func$readTree$sorting$_mls_L0_3891_4017$1.class = class Cont$func$readTree$sorting$_mls_L0_3891_4017$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, param0$7, x$8, tmp$9, tmp$10, tmp$11, curDepth$12, tmp$13, stackDelayRes$14) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.t$0 = t$0;
      this.param0$1 = param0$1;
      this.param1$2 = param1$2;
      this.param2$3 = param2$3;
      this.x$4 = x$4;
      this.l$5 = l$5;
      this.r$6 = r$6;
      this.param0$7 = param0$7;
      this.x$8 = x$8;
      this.tmp$9 = tmp$9;
      this.tmp$10 = tmp$10;
      this.tmp$11 = tmp$11;
      this.curDepth$12 = curDepth$12;
      this.tmp$13 = tmp$13;
      this.stackDelayRes$14 = stackDelayRes$14;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 258) {
      this.stackDelayRes$14 = value$;
    } else if (this.pc === 262) {
      this.tmp$13 = value$;
    } else if (this.pc === 259) {
      this.tmp$9 = value$;
    } else if (this.pc === 260) {
      this.tmp$10 = value$;
    } else if (this.pc === 261) {
      this.tmp$11 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 258) {
        if (this.t$0 instanceof Tip21.class) {
          return NofibPrelude.Nil
        } else if (this.t$0 instanceof Twig21.class) {
          this.param0$7 = this.t$0.a;
          this.x$8 = this.param0$7;
          this.pc = 264;
          continue contLoop;
          this.pc = 263;
          continue contLoop;
        } else if (this.t$0 instanceof Branch21.class) {
          this.param0$1 = this.t$0.a;
          this.param1$2 = this.t$0.l;
          this.param2$3 = this.t$0.r;
          this.x$4 = this.param0$1;
          this.l$5 = this.param1$2;
          this.r$6 = this.param2$3;
          this.pc = 268;
          continue contLoop;
          this.pc = 263;
          continue contLoop;
          this.pc = 263;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$13 = new globalThis.Error("match error");
          if (this.tmp$13 instanceof runtime.EffectSig.class) {
            this.pc = 262;
            this.tmp$13.contTrace.last.next = this;
            this.tmp$13.contTrace.last = this;
            return this.tmp$13
          }
          this.pc = 262;
          continue contLoop;
        }
        this.pc = 263;
        continue contLoop;
      } else if (this.pc === 263) {
        break contLoop;
      } else if (this.pc === 262) {
        this.tmp$13 = runtime.resetDepth(this.tmp$13, this.curDepth$12);
        throw this.tmp$13;
      } else if (this.pc === 265) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.append(this.tmp$9, this.tmp$11)
      } else if (this.pc === 268) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = readTree1(this.l$5);
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 259;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 259;
        continue contLoop;
      } else if (this.pc === 259) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$12);
        this.pc = 267;
        continue contLoop;
      } else if (this.pc === 266) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$11 = NofibPrelude.Cons(this.x$4, this.tmp$10);
        if (this.tmp$11 instanceof runtime.EffectSig.class) {
          this.pc = 261;
          this.tmp$11.contTrace.last.next = this;
          this.tmp$11.contTrace.last = this;
          return this.tmp$11
        }
        this.pc = 261;
        continue contLoop;
      } else if (this.pc === 267) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$10 = readTree1(this.r$6);
        if (this.tmp$10 instanceof runtime.EffectSig.class) {
          this.pc = 260;
          this.tmp$10.contTrace.last.next = this;
          this.tmp$10.contTrace.last = this;
          return this.tmp$10
        }
        this.pc = 260;
        continue contLoop;
      } else if (this.pc === 260) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$12);
        this.pc = 266;
        continue contLoop;
      } else if (this.pc === 261) {
        this.tmp$11 = runtime.resetDepth(this.tmp$11, this.curDepth$12);
        this.pc = 265;
        continue contLoop;
      } else if (this.pc === 264) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.x$8, NofibPrelude.Nil)
      }
      break;
    }
  }
  toString() { return "Cont$func$readTree$sorting$_mls_L0_3891_4017$(" + globalThis.Predef.render(this.pc) + ")"; }
};
readTree1 = function readTree(t) {
  let param0, param1, param2, x, l, r, param01, x1, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$readTree$sorting$_mls_L0_3891_4017$$(t, param0, param1, param2, x, l, r, param01, x1, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 258);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (t instanceof Tip21.class) {
    return NofibPrelude.Nil
  } else if (t instanceof Twig21.class) {
    param01 = t.a;
    x1 = param01;
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.Cons(x1, NofibPrelude.Nil)
  } else if (t instanceof Branch21.class) {
    param0 = t.a;
    param1 = t.l;
    param2 = t.r;
    x = param0;
    l = param1;
    r = param2;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = readTree1(l);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$readTree$sorting$_mls_L0_3891_4017$$(t, param0, param1, param2, x, l, r, param01, x1, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 259);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = readTree1(r);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$readTree$sorting$_mls_L0_3891_4017$$(t, param0, param1, param2, x, l, r, param01, x1, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 260);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = NofibPrelude.Cons(x, tmp1);
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$readTree$sorting$_mls_L0_3891_4017$$(t, param0, param1, param2, x, l, r, param01, x1, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 261);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.append(tmp, tmp2)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp3 = new globalThis.Error("match error");
    if (tmp3 instanceof runtime.EffectSig.class) {
      tmp3.contTrace.last.next = Cont$func$readTree$sorting$_mls_L0_3891_4017$$(t, param0, param1, param2, x, l, r, param01, x1, tmp, tmp1, tmp2, curDepth, tmp3, stackDelayRes, 262);
      tmp3.contTrace.last = tmp3.contTrace.last.next;
      return tmp3
    }
    tmp3 = runtime.resetDepth(tmp3, curDepth);
    throw tmp3;
  }
};
treeSort2 = function treeSort2(param) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$treeSort2$sorting$_mls_L0_3509_4043$$(param, tmp, curDepth, stackDelayRes, 235);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = mkTree1(param);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$treeSort2$sorting$_mls_L0_3509_4043$$(param, tmp, curDepth, stackDelayRes, 269);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return readTree1(tmp)
};
Cont$func$heapSort$sorting$_mls_L0_4049_4853$$ = function Cont$func$heapSort$sorting$_mls_L0_4049_4853$$(xs$0, tmp$1, curDepth$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$heapSort$sorting$_mls_L0_4049_4853$1.class(pc);
  return tmp(xs$0, tmp$1, curDepth$2, stackDelayRes$3)
};
Cont$func$heapSort$sorting$_mls_L0_4049_4853$$ctor = function Cont$func$heapSort$sorting$_mls_L0_4049_4853$$ctor(xs$0, tmp$1, curDepth$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$heapSort$sorting$_mls_L0_4049_4853$1.class(pc);
    return tmp(xs$0, tmp$1, curDepth$2, stackDelayRes$3)
  }
};
Cont$func$heapSort$sorting$_mls_L0_4049_4853$1 = function Cont$func$heapSort$sorting$_mls_L0_4049_4853$(pc1) {
  return (xs$01, tmp$11, curDepth$21, stackDelayRes$31) => {
    return new Cont$func$heapSort$sorting$_mls_L0_4049_4853$.class(pc1)(xs$01, tmp$11, curDepth$21, stackDelayRes$31);
  }
};
Cont$func$heapSort$sorting$_mls_L0_4049_4853$1.class = class Cont$func$heapSort$sorting$_mls_L0_4049_4853$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (xs$0, tmp$1, curDepth$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.xs$0 = xs$0;
      this.tmp$1 = tmp$1;
      this.curDepth$2 = curDepth$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 272) {
      this.stackDelayRes$3 = value$;
    } else if (this.pc === 354) {
      this.tmp$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 272) {
        this.pc = 356;
        continue contLoop;
      } else if (this.pc === 355) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return clear(this.tmp$1)
      } else if (this.pc === 356) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = heap(0, this.xs$0);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 354;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 354;
        continue contLoop;
      } else if (this.pc === 354) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$2);
        this.pc = 355;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$heapSort$sorting$_mls_L0_4049_4853$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$heap$sorting$_mls_L0_4070_4159$$ = function Cont$func$heap$sorting$_mls_L0_4070_4159$$(k$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10, pc) {
  let tmp;
  tmp = new Cont$func$heap$sorting$_mls_L0_4070_4159$1.class(pc);
  return tmp(k$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
};
Cont$func$heap$sorting$_mls_L0_4070_4159$$ctor = function Cont$func$heap$sorting$_mls_L0_4070_4159$$ctor(k$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$heap$sorting$_mls_L0_4070_4159$1.class(pc);
    return tmp(k$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10)
  }
};
Cont$func$heap$sorting$_mls_L0_4070_4159$1 = function Cont$func$heap$sorting$_mls_L0_4070_4159$(pc1) {
  return (k$01, xs$11, param0$21, param1$31, x$41, xs_$51, tmp$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101) => {
    return new Cont$func$heap$sorting$_mls_L0_4070_4159$.class(pc1)(k$01, xs$11, param0$21, param1$31, x$41, xs_$51, tmp$61, tmp$71, curDepth$81, tmp$91, stackDelayRes$101);
  }
};
Cont$func$heap$sorting$_mls_L0_4070_4159$1.class = class Cont$func$heap$sorting$_mls_L0_4070_4159$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (k$0, xs$1, param0$2, param1$3, x$4, xs_$5, tmp$6, tmp$7, curDepth$8, tmp$9, stackDelayRes$10) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.k$0 = k$0;
      this.xs$1 = xs$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.x$4 = x$4;
      this.xs_$5 = xs_$5;
      this.tmp$6 = tmp$6;
      this.tmp$7 = tmp$7;
      this.curDepth$8 = curDepth$8;
      this.tmp$9 = tmp$9;
      this.stackDelayRes$10 = stackDelayRes$10;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 273) {
      this.stackDelayRes$10 = value$;
    } else if (this.pc === 275) {
      this.tmp$9 = value$;
    } else if (this.pc === 274) {
      this.tmp$7 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 273) {
        if (this.xs$1 instanceof NofibPrelude.Nil.class) {
          return Tip1
        } else if (this.xs$1 instanceof NofibPrelude.Cons.class) {
          this.param0$2 = this.xs$1.head;
          this.param1$3 = this.xs$1.tail;
          this.x$4 = this.param0$2;
          this.xs_$5 = this.param1$3;
          this.tmp$6 = this.k$0 + 1;
          this.pc = 278;
          continue contLoop;
          this.pc = 276;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$9 = new globalThis.Error("match error");
          if (this.tmp$9 instanceof runtime.EffectSig.class) {
            this.pc = 275;
            this.tmp$9.contTrace.last.next = this;
            this.tmp$9.contTrace.last = this;
            return this.tmp$9
          }
          this.pc = 275;
          continue contLoop;
        }
        this.pc = 276;
        continue contLoop;
      } else if (this.pc === 276) {
        break contLoop;
      } else if (this.pc === 275) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$8);
        throw this.tmp$9;
      } else if (this.pc === 277) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return to_heap(this.k$0, this.x$4, this.tmp$7)
      } else if (this.pc === 278) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = heap(this.tmp$6, this.xs_$5);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 274;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 274;
        continue contLoop;
      } else if (this.pc === 274) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$8);
        this.pc = 277;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$heap$sorting$_mls_L0_4070_4159$(" + globalThis.Predef.render(this.pc) + ")"; }
};
heap = function heap(k, xs) {
  let param0, param1, x, xs_, tmp, tmp1, curDepth, tmp2, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$heap$sorting$_mls_L0_4070_4159$$(k, xs, param0, param1, x, xs_, tmp, tmp1, curDepth, tmp2, stackDelayRes, 273);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (xs instanceof NofibPrelude.Nil.class) {
    return Tip1
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs_ = param1;
    tmp = k + 1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = heap(tmp, xs_);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$heap$sorting$_mls_L0_4070_4159$$(k, xs, param0, param1, x, xs_, tmp, tmp1, curDepth, tmp2, stackDelayRes, 274);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return to_heap(k, x, tmp1)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = new globalThis.Error("match error");
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$heap$sorting$_mls_L0_4070_4159$$(k, xs, param0, param1, x, xs_, tmp, tmp1, curDepth, tmp2, stackDelayRes, 275);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    throw tmp2;
  }
};
Cont$func$to_heap$sorting$_mls_L0_4166_4505$$ = function Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k$0, x$1, t$2, param0$3, param1$4, param2$5, y$6, l$7, r$8, scrut$9, scrut$10, scrut$11, scrut$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, curDepth$27, tmp$28, stackDelayRes$29, pc) {
  let tmp;
  tmp = new Cont$func$to_heap$sorting$_mls_L0_4166_4505$1.class(pc);
  return tmp(k$0, x$1, t$2, param0$3, param1$4, param2$5, y$6, l$7, r$8, scrut$9, scrut$10, scrut$11, scrut$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, curDepth$27, tmp$28, stackDelayRes$29)
};
Cont$func$to_heap$sorting$_mls_L0_4166_4505$$ctor = function Cont$func$to_heap$sorting$_mls_L0_4166_4505$$ctor(k$0, x$1, t$2, param0$3, param1$4, param2$5, y$6, l$7, r$8, scrut$9, scrut$10, scrut$11, scrut$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, curDepth$27, tmp$28, stackDelayRes$29) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$to_heap$sorting$_mls_L0_4166_4505$1.class(pc);
    return tmp(k$0, x$1, t$2, param0$3, param1$4, param2$5, y$6, l$7, r$8, scrut$9, scrut$10, scrut$11, scrut$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, curDepth$27, tmp$28, stackDelayRes$29)
  }
};
Cont$func$to_heap$sorting$_mls_L0_4166_4505$1 = function Cont$func$to_heap$sorting$_mls_L0_4166_4505$(pc1) {
  return (k$01, x$11, t$21, param0$31, param1$41, param2$51, y$61, l$71, r$81, scrut$91, scrut$101, scrut$111, scrut$121, tmp$131, tmp$141, tmp$151, tmp$161, tmp$171, tmp$181, tmp$191, tmp$201, tmp$211, tmp$221, tmp$231, tmp$241, tmp$251, tmp$261, curDepth$271, tmp$281, stackDelayRes$291) => {
    return new Cont$func$to_heap$sorting$_mls_L0_4166_4505$.class(pc1)(k$01, x$11, t$21, param0$31, param1$41, param2$51, y$61, l$71, r$81, scrut$91, scrut$101, scrut$111, scrut$121, tmp$131, tmp$141, tmp$151, tmp$161, tmp$171, tmp$181, tmp$191, tmp$201, tmp$211, tmp$221, tmp$231, tmp$241, tmp$251, tmp$261, curDepth$271, tmp$281, stackDelayRes$291);
  }
};
Cont$func$to_heap$sorting$_mls_L0_4166_4505$1.class = class Cont$func$to_heap$sorting$_mls_L0_4166_4505$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (k$0, x$1, t$2, param0$3, param1$4, param2$5, y$6, l$7, r$8, scrut$9, scrut$10, scrut$11, scrut$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, curDepth$27, tmp$28, stackDelayRes$29) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.k$0 = k$0;
      this.x$1 = x$1;
      this.t$2 = t$2;
      this.param0$3 = param0$3;
      this.param1$4 = param1$4;
      this.param2$5 = param2$5;
      this.y$6 = y$6;
      this.l$7 = l$7;
      this.r$8 = r$8;
      this.scrut$9 = scrut$9;
      this.scrut$10 = scrut$10;
      this.scrut$11 = scrut$11;
      this.scrut$12 = scrut$12;
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
      this.curDepth$27 = curDepth$27;
      this.tmp$28 = tmp$28;
      this.stackDelayRes$29 = stackDelayRes$29;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 279) {
      this.stackDelayRes$29 = value$;
    } else if (this.pc === 300) {
      this.tmp$28 = value$;
    } else if (this.pc === 280) {
      this.scrut$11 = value$;
    } else if (this.pc === 292) {
      this.scrut$10 = value$;
    } else if (this.pc === 295) {
      this.scrut$9 = value$;
    } else if (this.pc === 298) {
      this.tmp$25 = value$;
    } else if (this.pc === 299) {
      this.tmp$26 = value$;
    } else if (this.pc === 296) {
      this.tmp$23 = value$;
    } else if (this.pc === 297) {
      this.tmp$24 = value$;
    } else if (this.pc === 293) {
      this.tmp$21 = value$;
    } else if (this.pc === 294) {
      this.tmp$22 = value$;
    } else if (this.pc === 281) {
      this.scrut$12 = value$;
    } else if (this.pc === 284) {
      this.scrut$10 = value$;
    } else if (this.pc === 287) {
      this.scrut$9 = value$;
    } else if (this.pc === 290) {
      this.tmp$19 = value$;
    } else if (this.pc === 291) {
      this.tmp$20 = value$;
    } else if (this.pc === 288) {
      this.tmp$17 = value$;
    } else if (this.pc === 289) {
      this.tmp$18 = value$;
    } else if (this.pc === 285) {
      this.tmp$15 = value$;
    } else if (this.pc === 286) {
      this.tmp$16 = value$;
    } else if (this.pc === 282) {
      this.tmp$13 = value$;
    } else if (this.pc === 283) {
      this.tmp$14 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 279) {
        if (this.t$2 instanceof Tip1.class) {
          this.pc = 302;
          continue contLoop;
        } else if (this.t$2 instanceof Branch1.class) {
          this.param0$3 = this.t$2.a;
          this.param1$4 = this.t$2.l;
          this.param2$5 = this.t$2.r;
          this.y$6 = this.param0$3;
          this.l$7 = this.param1$4;
          this.r$8 = this.param2$5;
          this.pc = 329;
          continue contLoop;
          this.pc = 301;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$28 = new globalThis.Error("match error");
          if (this.tmp$28 instanceof runtime.EffectSig.class) {
            this.pc = 300;
            this.tmp$28.contTrace.last.next = this;
            this.tmp$28.contTrace.last = this;
            return this.tmp$28
          }
          this.pc = 300;
          continue contLoop;
        }
        this.pc = 301;
        continue contLoop;
      } else if (this.pc === 301) {
        break contLoop;
      } else if (this.pc === 300) {
        this.tmp$28 = runtime.resetDepth(this.tmp$28, this.curDepth$27);
        throw this.tmp$28;
      } else if (this.pc === 329) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$11 = leList(this.x$1, this.y$6);
        if (this.scrut$11 instanceof runtime.EffectSig.class) {
          this.pc = 280;
          this.scrut$11.contTrace.last.next = this;
          this.scrut$11.contTrace.last = this;
          return this.scrut$11
        }
        this.pc = 280;
        continue contLoop;
      } else if (this.pc === 280) {
        this.scrut$11 = runtime.resetDepth(this.scrut$11, this.curDepth$27);
        if (this.scrut$11 === true) {
          this.pc = 317;
          continue contLoop;
        } else {
          this.pc = 328;
          continue contLoop;
        }
        this.pc = 301;
        continue contLoop;
      } else if (this.pc === 328) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$10 = leList(this.x$1, this.y$6);
        if (this.scrut$10 instanceof runtime.EffectSig.class) {
          this.pc = 292;
          this.scrut$10.contTrace.last.next = this;
          this.scrut$10.contTrace.last = this;
          return this.scrut$10
        }
        this.pc = 292;
        continue contLoop;
      } else if (this.pc === 292) {
        this.scrut$10 = runtime.resetDepth(this.scrut$10, this.curDepth$27);
        if (this.scrut$10 === true) {
          this.pc = 320;
          continue contLoop;
        } else {
          this.pc = 327;
          continue contLoop;
        }
        this.pc = 301;
        continue contLoop;
      } else if (this.pc === 327) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$9 = odd(this.k$0);
        if (this.scrut$9 instanceof runtime.EffectSig.class) {
          this.pc = 295;
          this.scrut$9.contTrace.last.next = this;
          this.scrut$9.contTrace.last = this;
          return this.scrut$9
        }
        this.pc = 295;
        continue contLoop;
      } else if (this.pc === 295) {
        this.scrut$9 = runtime.resetDepth(this.scrut$9, this.curDepth$27);
        if (this.scrut$9 === true) {
          this.pc = 323;
          continue contLoop;
        } else {
          this.pc = 326;
          continue contLoop;
        }
        this.pc = 301;
        continue contLoop;
      } else if (this.pc === 324) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(this.y$6, this.l$7, this.tmp$26)
      } else if (this.pc === 325) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$26 = to_heap(this.tmp$25, this.x$1, this.r$8);
        if (this.tmp$26 instanceof runtime.EffectSig.class) {
          this.pc = 299;
          this.tmp$26.contTrace.last.next = this;
          this.tmp$26.contTrace.last = this;
          return this.tmp$26
        }
        this.pc = 299;
        continue contLoop;
      } else if (this.pc === 326) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$25 = NofibPrelude.intDiv(this.k$0, 2);
        if (this.tmp$25 instanceof runtime.EffectSig.class) {
          this.pc = 298;
          this.tmp$25.contTrace.last.next = this;
          this.tmp$25.contTrace.last = this;
          return this.tmp$25
        }
        this.pc = 298;
        continue contLoop;
      } else if (this.pc === 298) {
        this.tmp$25 = runtime.resetDepth(this.tmp$25, this.curDepth$27);
        this.pc = 325;
        continue contLoop;
      } else if (this.pc === 299) {
        this.tmp$26 = runtime.resetDepth(this.tmp$26, this.curDepth$27);
        this.pc = 324;
        continue contLoop;
      } else if (this.pc === 321) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(this.y$6, this.tmp$24, this.r$8)
      } else if (this.pc === 322) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$24 = to_heap(this.tmp$23, this.x$1, this.l$7);
        if (this.tmp$24 instanceof runtime.EffectSig.class) {
          this.pc = 297;
          this.tmp$24.contTrace.last.next = this;
          this.tmp$24.contTrace.last = this;
          return this.tmp$24
        }
        this.pc = 297;
        continue contLoop;
      } else if (this.pc === 323) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$23 = NofibPrelude.intDiv(this.k$0, 2);
        if (this.tmp$23 instanceof runtime.EffectSig.class) {
          this.pc = 296;
          this.tmp$23.contTrace.last.next = this;
          this.tmp$23.contTrace.last = this;
          return this.tmp$23
        }
        this.pc = 296;
        continue contLoop;
      } else if (this.pc === 296) {
        this.tmp$23 = runtime.resetDepth(this.tmp$23, this.curDepth$27);
        this.pc = 322;
        continue contLoop;
      } else if (this.pc === 297) {
        this.tmp$24 = runtime.resetDepth(this.tmp$24, this.curDepth$27);
        this.pc = 321;
        continue contLoop;
      } else if (this.pc === 318) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(this.x$1, this.l$7, this.tmp$22)
      } else if (this.pc === 319) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$22 = to_heap(this.tmp$21, this.y$6, this.r$8);
        if (this.tmp$22 instanceof runtime.EffectSig.class) {
          this.pc = 294;
          this.tmp$22.contTrace.last.next = this;
          this.tmp$22.contTrace.last = this;
          return this.tmp$22
        }
        this.pc = 294;
        continue contLoop;
      } else if (this.pc === 320) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$21 = NofibPrelude.intDiv(this.k$0, 2);
        if (this.tmp$21 instanceof runtime.EffectSig.class) {
          this.pc = 293;
          this.tmp$21.contTrace.last.next = this;
          this.tmp$21.contTrace.last = this;
          return this.tmp$21
        }
        this.pc = 293;
        continue contLoop;
      } else if (this.pc === 293) {
        this.tmp$21 = runtime.resetDepth(this.tmp$21, this.curDepth$27);
        this.pc = 319;
        continue contLoop;
      } else if (this.pc === 294) {
        this.tmp$22 = runtime.resetDepth(this.tmp$22, this.curDepth$27);
        this.pc = 318;
        continue contLoop;
      } else if (this.pc === 317) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$12 = odd(this.k$0);
        if (this.scrut$12 instanceof runtime.EffectSig.class) {
          this.pc = 281;
          this.scrut$12.contTrace.last.next = this;
          this.scrut$12.contTrace.last = this;
          return this.scrut$12
        }
        this.pc = 281;
        continue contLoop;
      } else if (this.pc === 281) {
        this.scrut$12 = runtime.resetDepth(this.scrut$12, this.curDepth$27);
        if (this.scrut$12 === true) {
          this.pc = 305;
          continue contLoop;
        } else {
          this.pc = 316;
          continue contLoop;
        }
        this.pc = 301;
        continue contLoop;
      } else if (this.pc === 316) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$10 = leList(this.x$1, this.y$6);
        if (this.scrut$10 instanceof runtime.EffectSig.class) {
          this.pc = 284;
          this.scrut$10.contTrace.last.next = this;
          this.scrut$10.contTrace.last = this;
          return this.scrut$10
        }
        this.pc = 284;
        continue contLoop;
      } else if (this.pc === 284) {
        this.scrut$10 = runtime.resetDepth(this.scrut$10, this.curDepth$27);
        if (this.scrut$10 === true) {
          this.pc = 308;
          continue contLoop;
        } else {
          this.pc = 315;
          continue contLoop;
        }
        this.pc = 301;
        continue contLoop;
      } else if (this.pc === 315) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$9 = odd(this.k$0);
        if (this.scrut$9 instanceof runtime.EffectSig.class) {
          this.pc = 287;
          this.scrut$9.contTrace.last.next = this;
          this.scrut$9.contTrace.last = this;
          return this.scrut$9
        }
        this.pc = 287;
        continue contLoop;
      } else if (this.pc === 287) {
        this.scrut$9 = runtime.resetDepth(this.scrut$9, this.curDepth$27);
        if (this.scrut$9 === true) {
          this.pc = 311;
          continue contLoop;
        } else {
          this.pc = 314;
          continue contLoop;
        }
        this.pc = 301;
        continue contLoop;
      } else if (this.pc === 312) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(this.y$6, this.l$7, this.tmp$20)
      } else if (this.pc === 313) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$20 = to_heap(this.tmp$19, this.x$1, this.r$8);
        if (this.tmp$20 instanceof runtime.EffectSig.class) {
          this.pc = 291;
          this.tmp$20.contTrace.last.next = this;
          this.tmp$20.contTrace.last = this;
          return this.tmp$20
        }
        this.pc = 291;
        continue contLoop;
      } else if (this.pc === 314) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$19 = NofibPrelude.intDiv(this.k$0, 2);
        if (this.tmp$19 instanceof runtime.EffectSig.class) {
          this.pc = 290;
          this.tmp$19.contTrace.last.next = this;
          this.tmp$19.contTrace.last = this;
          return this.tmp$19
        }
        this.pc = 290;
        continue contLoop;
      } else if (this.pc === 290) {
        this.tmp$19 = runtime.resetDepth(this.tmp$19, this.curDepth$27);
        this.pc = 313;
        continue contLoop;
      } else if (this.pc === 291) {
        this.tmp$20 = runtime.resetDepth(this.tmp$20, this.curDepth$27);
        this.pc = 312;
        continue contLoop;
      } else if (this.pc === 309) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(this.y$6, this.tmp$18, this.r$8)
      } else if (this.pc === 310) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$18 = to_heap(this.tmp$17, this.x$1, this.l$7);
        if (this.tmp$18 instanceof runtime.EffectSig.class) {
          this.pc = 289;
          this.tmp$18.contTrace.last.next = this;
          this.tmp$18.contTrace.last = this;
          return this.tmp$18
        }
        this.pc = 289;
        continue contLoop;
      } else if (this.pc === 311) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$17 = NofibPrelude.intDiv(this.k$0, 2);
        if (this.tmp$17 instanceof runtime.EffectSig.class) {
          this.pc = 288;
          this.tmp$17.contTrace.last.next = this;
          this.tmp$17.contTrace.last = this;
          return this.tmp$17
        }
        this.pc = 288;
        continue contLoop;
      } else if (this.pc === 288) {
        this.tmp$17 = runtime.resetDepth(this.tmp$17, this.curDepth$27);
        this.pc = 310;
        continue contLoop;
      } else if (this.pc === 289) {
        this.tmp$18 = runtime.resetDepth(this.tmp$18, this.curDepth$27);
        this.pc = 309;
        continue contLoop;
      } else if (this.pc === 306) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(this.x$1, this.l$7, this.tmp$16)
      } else if (this.pc === 307) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$16 = to_heap(this.tmp$15, this.y$6, this.r$8);
        if (this.tmp$16 instanceof runtime.EffectSig.class) {
          this.pc = 286;
          this.tmp$16.contTrace.last.next = this;
          this.tmp$16.contTrace.last = this;
          return this.tmp$16
        }
        this.pc = 286;
        continue contLoop;
      } else if (this.pc === 308) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$15 = NofibPrelude.intDiv(this.k$0, 2);
        if (this.tmp$15 instanceof runtime.EffectSig.class) {
          this.pc = 285;
          this.tmp$15.contTrace.last.next = this;
          this.tmp$15.contTrace.last = this;
          return this.tmp$15
        }
        this.pc = 285;
        continue contLoop;
      } else if (this.pc === 285) {
        this.tmp$15 = runtime.resetDepth(this.tmp$15, this.curDepth$27);
        this.pc = 307;
        continue contLoop;
      } else if (this.pc === 286) {
        this.tmp$16 = runtime.resetDepth(this.tmp$16, this.curDepth$27);
        this.pc = 306;
        continue contLoop;
      } else if (this.pc === 303) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(this.x$1, this.tmp$14, this.r$8)
      } else if (this.pc === 304) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$14 = to_heap(this.tmp$13, this.y$6, this.l$7);
        if (this.tmp$14 instanceof runtime.EffectSig.class) {
          this.pc = 283;
          this.tmp$14.contTrace.last.next = this;
          this.tmp$14.contTrace.last = this;
          return this.tmp$14
        }
        this.pc = 283;
        continue contLoop;
      } else if (this.pc === 305) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$13 = NofibPrelude.intDiv(this.k$0, 2);
        if (this.tmp$13 instanceof runtime.EffectSig.class) {
          this.pc = 282;
          this.tmp$13.contTrace.last.next = this;
          this.tmp$13.contTrace.last = this;
          return this.tmp$13
        }
        this.pc = 282;
        continue contLoop;
      } else if (this.pc === 282) {
        this.tmp$13 = runtime.resetDepth(this.tmp$13, this.curDepth$27);
        this.pc = 304;
        continue contLoop;
      } else if (this.pc === 283) {
        this.tmp$14 = runtime.resetDepth(this.tmp$14, this.curDepth$27);
        this.pc = 303;
        continue contLoop;
      } else if (this.pc === 302) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(this.x$1, Tip1, Tip1)
      }
      break;
    }
  }
  toString() { return "Cont$func$to_heap$sorting$_mls_L0_4166_4505$(" + globalThis.Predef.render(this.pc) + ")"; }
};
to_heap = function to_heap(k, x, t) {
  let param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 279);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (t instanceof Tip1.class) {
    runtime.stackDepth = runtime.stackDepth + 1;
    return Branch1(x, Tip1, Tip1)
  } else if (t instanceof Branch1.class) {
    param0 = t.a;
    param1 = t.l;
    param2 = t.r;
    y = param0;
    l = param1;
    r = param2;
    runtime.stackDepth = runtime.stackDepth + 1;
    scrut2 = leList(x, y);
    if (scrut2 instanceof runtime.EffectSig.class) {
      scrut2.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 280);
      scrut2.contTrace.last = scrut2.contTrace.last.next;
      return scrut2
    }
    scrut2 = runtime.resetDepth(scrut2, curDepth);
    if (scrut2 === true) {
      runtime.stackDepth = runtime.stackDepth + 1;
      scrut3 = odd(k);
      if (scrut3 instanceof runtime.EffectSig.class) {
        scrut3.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 281);
        scrut3.contTrace.last = scrut3.contTrace.last.next;
        return scrut3
      }
      scrut3 = runtime.resetDepth(scrut3, curDepth);
      if (scrut3 === true) {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp = NofibPrelude.intDiv(k, 2);
        if (tmp instanceof runtime.EffectSig.class) {
          tmp.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 282);
          tmp.contTrace.last = tmp.contTrace.last.next;
          return tmp
        }
        tmp = runtime.resetDepth(tmp, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp1 = to_heap(tmp, y, l);
        if (tmp1 instanceof runtime.EffectSig.class) {
          tmp1.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 283);
          tmp1.contTrace.last = tmp1.contTrace.last.next;
          return tmp1
        }
        tmp1 = runtime.resetDepth(tmp1, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(x, tmp1, r)
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        scrut1 = leList(x, y);
        if (scrut1 instanceof runtime.EffectSig.class) {
          scrut1.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 284);
          scrut1.contTrace.last = scrut1.contTrace.last.next;
          return scrut1
        }
        scrut1 = runtime.resetDepth(scrut1, curDepth);
        if (scrut1 === true) {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp2 = NofibPrelude.intDiv(k, 2);
          if (tmp2 instanceof runtime.EffectSig.class) {
            tmp2.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 285);
            tmp2.contTrace.last = tmp2.contTrace.last.next;
            return tmp2
          }
          tmp2 = runtime.resetDepth(tmp2, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp3 = to_heap(tmp2, y, r);
          if (tmp3 instanceof runtime.EffectSig.class) {
            tmp3.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 286);
            tmp3.contTrace.last = tmp3.contTrace.last.next;
            return tmp3
          }
          tmp3 = runtime.resetDepth(tmp3, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          return Branch1(x, l, tmp3)
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          scrut = odd(k);
          if (scrut instanceof runtime.EffectSig.class) {
            scrut.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 287);
            scrut.contTrace.last = scrut.contTrace.last.next;
            return scrut
          }
          scrut = runtime.resetDepth(scrut, curDepth);
          if (scrut === true) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp4 = NofibPrelude.intDiv(k, 2);
            if (tmp4 instanceof runtime.EffectSig.class) {
              tmp4.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 288);
              tmp4.contTrace.last = tmp4.contTrace.last.next;
              return tmp4
            }
            tmp4 = runtime.resetDepth(tmp4, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp5 = to_heap(tmp4, x, l);
            if (tmp5 instanceof runtime.EffectSig.class) {
              tmp5.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 289);
              tmp5.contTrace.last = tmp5.contTrace.last.next;
              return tmp5
            }
            tmp5 = runtime.resetDepth(tmp5, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            return Branch1(y, tmp5, r)
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp6 = NofibPrelude.intDiv(k, 2);
            if (tmp6 instanceof runtime.EffectSig.class) {
              tmp6.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 290);
              tmp6.contTrace.last = tmp6.contTrace.last.next;
              return tmp6
            }
            tmp6 = runtime.resetDepth(tmp6, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp7 = to_heap(tmp6, x, r);
            if (tmp7 instanceof runtime.EffectSig.class) {
              tmp7.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 291);
              tmp7.contTrace.last = tmp7.contTrace.last.next;
              return tmp7
            }
            tmp7 = runtime.resetDepth(tmp7, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            return Branch1(y, l, tmp7)
          }
        }
      }
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      scrut1 = leList(x, y);
      if (scrut1 instanceof runtime.EffectSig.class) {
        scrut1.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 292);
        scrut1.contTrace.last = scrut1.contTrace.last.next;
        return scrut1
      }
      scrut1 = runtime.resetDepth(scrut1, curDepth);
      if (scrut1 === true) {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp8 = NofibPrelude.intDiv(k, 2);
        if (tmp8 instanceof runtime.EffectSig.class) {
          tmp8.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 293);
          tmp8.contTrace.last = tmp8.contTrace.last.next;
          return tmp8
        }
        tmp8 = runtime.resetDepth(tmp8, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp9 = to_heap(tmp8, y, r);
        if (tmp9 instanceof runtime.EffectSig.class) {
          tmp9.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 294);
          tmp9.contTrace.last = tmp9.contTrace.last.next;
          return tmp9
        }
        tmp9 = runtime.resetDepth(tmp9, curDepth);
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(x, l, tmp9)
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        scrut = odd(k);
        if (scrut instanceof runtime.EffectSig.class) {
          scrut.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 295);
          scrut.contTrace.last = scrut.contTrace.last.next;
          return scrut
        }
        scrut = runtime.resetDepth(scrut, curDepth);
        if (scrut === true) {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp10 = NofibPrelude.intDiv(k, 2);
          if (tmp10 instanceof runtime.EffectSig.class) {
            tmp10.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 296);
            tmp10.contTrace.last = tmp10.contTrace.last.next;
            return tmp10
          }
          tmp10 = runtime.resetDepth(tmp10, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp11 = to_heap(tmp10, x, l);
          if (tmp11 instanceof runtime.EffectSig.class) {
            tmp11.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 297);
            tmp11.contTrace.last = tmp11.contTrace.last.next;
            return tmp11
          }
          tmp11 = runtime.resetDepth(tmp11, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          return Branch1(y, tmp11, r)
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp12 = NofibPrelude.intDiv(k, 2);
          if (tmp12 instanceof runtime.EffectSig.class) {
            tmp12.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 298);
            tmp12.contTrace.last = tmp12.contTrace.last.next;
            return tmp12
          }
          tmp12 = runtime.resetDepth(tmp12, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp13 = to_heap(tmp12, x, r);
          if (tmp13 instanceof runtime.EffectSig.class) {
            tmp13.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 299);
            tmp13.contTrace.last = tmp13.contTrace.last.next;
            return tmp13
          }
          tmp13 = runtime.resetDepth(tmp13, curDepth);
          runtime.stackDepth = runtime.stackDepth + 1;
          return Branch1(y, l, tmp13)
        }
      }
    }
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp14 = new globalThis.Error("match error");
    if (tmp14 instanceof runtime.EffectSig.class) {
      tmp14.contTrace.last.next = Cont$func$to_heap$sorting$_mls_L0_4166_4505$$(k, x, t, param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, curDepth, tmp14, stackDelayRes, 300);
      tmp14.contTrace.last = tmp14.contTrace.last.next;
      return tmp14
    }
    tmp14 = runtime.resetDepth(tmp14, curDepth);
    throw tmp14;
  }
};
Cont$func$clear$sorting$_mls_L0_4512_4594$$ = function Cont$func$clear$sorting$_mls_L0_4512_4594$$(t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, tmp$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11, pc) {
  let tmp;
  tmp = new Cont$func$clear$sorting$_mls_L0_4512_4594$1.class(pc);
  return tmp(t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, tmp$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11)
};
Cont$func$clear$sorting$_mls_L0_4512_4594$$ctor = function Cont$func$clear$sorting$_mls_L0_4512_4594$$ctor(t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, tmp$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$clear$sorting$_mls_L0_4512_4594$1.class(pc);
    return tmp(t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, tmp$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11)
  }
};
Cont$func$clear$sorting$_mls_L0_4512_4594$1 = function Cont$func$clear$sorting$_mls_L0_4512_4594$(pc1) {
  return (t$01, param0$11, param1$21, param2$31, x$41, l$51, r$61, tmp$71, tmp$81, curDepth$91, tmp$101, stackDelayRes$111) => {
    return new Cont$func$clear$sorting$_mls_L0_4512_4594$.class(pc1)(t$01, param0$11, param1$21, param2$31, x$41, l$51, r$61, tmp$71, tmp$81, curDepth$91, tmp$101, stackDelayRes$111);
  }
};
Cont$func$clear$sorting$_mls_L0_4512_4594$1.class = class Cont$func$clear$sorting$_mls_L0_4512_4594$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (t$0, param0$1, param1$2, param2$3, x$4, l$5, r$6, tmp$7, tmp$8, curDepth$9, tmp$10, stackDelayRes$11) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.t$0 = t$0;
      this.param0$1 = param0$1;
      this.param1$2 = param1$2;
      this.param2$3 = param2$3;
      this.x$4 = x$4;
      this.l$5 = l$5;
      this.r$6 = r$6;
      this.tmp$7 = tmp$7;
      this.tmp$8 = tmp$8;
      this.curDepth$9 = curDepth$9;
      this.tmp$10 = tmp$10;
      this.stackDelayRes$11 = stackDelayRes$11;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 330) {
      this.stackDelayRes$11 = value$;
    } else if (this.pc === 333) {
      this.tmp$10 = value$;
    } else if (this.pc === 331) {
      this.tmp$7 = value$;
    } else if (this.pc === 332) {
      this.tmp$8 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 330) {
        if (this.t$0 instanceof Tip1.class) {
          return NofibPrelude.Nil
        } else if (this.t$0 instanceof Branch1.class) {
          this.param0$1 = this.t$0.a;
          this.param1$2 = this.t$0.l;
          this.param2$3 = this.t$0.r;
          this.x$4 = this.param0$1;
          this.l$5 = this.param1$2;
          this.r$6 = this.param2$3;
          this.pc = 337;
          continue contLoop;
          this.pc = 334;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$10 = new globalThis.Error("match error");
          if (this.tmp$10 instanceof runtime.EffectSig.class) {
            this.pc = 333;
            this.tmp$10.contTrace.last.next = this;
            this.tmp$10.contTrace.last = this;
            return this.tmp$10
          }
          this.pc = 333;
          continue contLoop;
        }
        this.pc = 334;
        continue contLoop;
      } else if (this.pc === 334) {
        break contLoop;
      } else if (this.pc === 333) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$9);
        throw this.tmp$10;
      } else if (this.pc === 335) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.x$4, this.tmp$8)
      } else if (this.pc === 336) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = clear(this.tmp$7);
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 332;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 332;
        continue contLoop;
      } else if (this.pc === 337) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = mix(this.l$5, this.r$6);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 331;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 331;
        continue contLoop;
      } else if (this.pc === 331) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$9);
        this.pc = 336;
        continue contLoop;
      } else if (this.pc === 332) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$9);
        this.pc = 335;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$clear$sorting$_mls_L0_4512_4594$(" + globalThis.Predef.render(this.pc) + ")"; }
};
clear = function clear(t) {
  let param0, param1, param2, x, l, r, tmp, tmp1, curDepth, tmp2, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$clear$sorting$_mls_L0_4512_4594$$(t, param0, param1, param2, x, l, r, tmp, tmp1, curDepth, tmp2, stackDelayRes, 330);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (t instanceof Tip1.class) {
    return NofibPrelude.Nil
  } else if (t instanceof Branch1.class) {
    param0 = t.a;
    param1 = t.l;
    param2 = t.r;
    x = param0;
    l = param1;
    r = param2;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = mix(l, r);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$clear$sorting$_mls_L0_4512_4594$$(t, param0, param1, param2, x, l, r, tmp, tmp1, curDepth, tmp2, stackDelayRes, 331);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = clear(tmp);
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$clear$sorting$_mls_L0_4512_4594$$(t, param0, param1, param2, x, l, r, tmp, tmp1, curDepth, tmp2, stackDelayRes, 332);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return NofibPrelude.Cons(x, tmp1)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp2 = new globalThis.Error("match error");
    if (tmp2 instanceof runtime.EffectSig.class) {
      tmp2.contTrace.last.next = Cont$func$clear$sorting$_mls_L0_4512_4594$$(t, param0, param1, param2, x, l, r, tmp, tmp1, curDepth, tmp2, stackDelayRes, 333);
      tmp2.contTrace.last = tmp2.contTrace.last.next;
      return tmp2
    }
    tmp2 = runtime.resetDepth(tmp2, curDepth);
    throw tmp2;
  }
};
Cont$func$mix$sorting$_mls_L0_4601_4832$$ = function Cont$func$mix$sorting$_mls_L0_4601_4832$$(l$0, r$1, param0$2, param1$3, param2$4, x$5, l1$6, r1$7, param0$8, param1$9, param2$10, y$11, l2$12, r2$13, scrut$14, tmp$15, tmp$16, tmp$17, tmp$18, curDepth$19, tmp$20, tmp$21, stackDelayRes$22, pc) {
  let tmp;
  tmp = new Cont$func$mix$sorting$_mls_L0_4601_4832$1.class(pc);
  return tmp(l$0, r$1, param0$2, param1$3, param2$4, x$5, l1$6, r1$7, param0$8, param1$9, param2$10, y$11, l2$12, r2$13, scrut$14, tmp$15, tmp$16, tmp$17, tmp$18, curDepth$19, tmp$20, tmp$21, stackDelayRes$22)
};
Cont$func$mix$sorting$_mls_L0_4601_4832$$ctor = function Cont$func$mix$sorting$_mls_L0_4601_4832$$ctor(l$0, r$1, param0$2, param1$3, param2$4, x$5, l1$6, r1$7, param0$8, param1$9, param2$10, y$11, l2$12, r2$13, scrut$14, tmp$15, tmp$16, tmp$17, tmp$18, curDepth$19, tmp$20, tmp$21, stackDelayRes$22) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$mix$sorting$_mls_L0_4601_4832$1.class(pc);
    return tmp(l$0, r$1, param0$2, param1$3, param2$4, x$5, l1$6, r1$7, param0$8, param1$9, param2$10, y$11, l2$12, r2$13, scrut$14, tmp$15, tmp$16, tmp$17, tmp$18, curDepth$19, tmp$20, tmp$21, stackDelayRes$22)
  }
};
Cont$func$mix$sorting$_mls_L0_4601_4832$1 = function Cont$func$mix$sorting$_mls_L0_4601_4832$(pc1) {
  return (l$01, r$11, param0$21, param1$31, param2$41, x$51, l1$61, r1$71, param0$81, param1$91, param2$101, y$111, l2$121, r2$131, scrut$141, tmp$151, tmp$161, tmp$171, tmp$181, curDepth$191, tmp$201, tmp$211, stackDelayRes$221) => {
    return new Cont$func$mix$sorting$_mls_L0_4601_4832$.class(pc1)(l$01, r$11, param0$21, param1$31, param2$41, x$51, l1$61, r1$71, param0$81, param1$91, param2$101, y$111, l2$121, r2$131, scrut$141, tmp$151, tmp$161, tmp$171, tmp$181, curDepth$191, tmp$201, tmp$211, stackDelayRes$221);
  }
};
Cont$func$mix$sorting$_mls_L0_4601_4832$1.class = class Cont$func$mix$sorting$_mls_L0_4601_4832$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (l$0, r$1, param0$2, param1$3, param2$4, x$5, l1$6, r1$7, param0$8, param1$9, param2$10, y$11, l2$12, r2$13, scrut$14, tmp$15, tmp$16, tmp$17, tmp$18, curDepth$19, tmp$20, tmp$21, stackDelayRes$22) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.l$0 = l$0;
      this.r$1 = r$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.param2$4 = param2$4;
      this.x$5 = x$5;
      this.l1$6 = l1$6;
      this.r1$7 = r1$7;
      this.param0$8 = param0$8;
      this.param1$9 = param1$9;
      this.param2$10 = param2$10;
      this.y$11 = y$11;
      this.l2$12 = l2$12;
      this.r2$13 = r2$13;
      this.scrut$14 = scrut$14;
      this.tmp$15 = tmp$15;
      this.tmp$16 = tmp$16;
      this.tmp$17 = tmp$17;
      this.tmp$18 = tmp$18;
      this.curDepth$19 = curDepth$19;
      this.tmp$20 = tmp$20;
      this.tmp$21 = tmp$21;
      this.stackDelayRes$22 = stackDelayRes$22;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 338) {
      this.stackDelayRes$22 = value$;
    } else if (this.pc === 345) {
      this.tmp$21 = value$;
    } else if (this.pc === 344) {
      this.tmp$20 = value$;
    } else if (this.pc === 339) {
      this.scrut$14 = value$;
    } else if (this.pc === 342) {
      this.tmp$17 = value$;
    } else if (this.pc === 343) {
      this.tmp$18 = value$;
    } else if (this.pc === 340) {
      this.tmp$15 = value$;
    } else if (this.pc === 341) {
      this.tmp$16 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 338) {
        if (this.l$0 instanceof Tip1.class) {
          return this.r$1
        } else {
          if (this.r$1 instanceof Tip1.class) {
            return this.l$0
          } else {
            if (this.l$0 instanceof Branch1.class) {
              this.param0$2 = this.l$0.a;
              this.param1$3 = this.l$0.l;
              this.param2$4 = this.l$0.r;
              this.x$5 = this.param0$2;
              this.l1$6 = this.param1$3;
              this.r1$7 = this.param2$4;
              if (this.r$1 instanceof Branch1.class) {
                this.param0$8 = this.r$1.a;
                this.param1$9 = this.r$1.l;
                this.param2$10 = this.r$1.r;
                this.y$11 = this.param0$8;
                this.l2$12 = this.param1$9;
                this.r2$13 = this.param2$10;
                this.pc = 353;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.tmp$20 = new globalThis.Error("match error");
                if (this.tmp$20 instanceof runtime.EffectSig.class) {
                  this.pc = 344;
                  this.tmp$20.contTrace.last.next = this;
                  this.tmp$20.contTrace.last = this;
                  return this.tmp$20
                }
                this.pc = 344;
                continue contLoop;
              }
              this.pc = 346;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.tmp$21 = new globalThis.Error("match error");
              if (this.tmp$21 instanceof runtime.EffectSig.class) {
                this.pc = 345;
                this.tmp$21.contTrace.last.next = this;
                this.tmp$21.contTrace.last = this;
                return this.tmp$21
              }
              this.pc = 345;
              continue contLoop;
            }
            this.pc = 346;
            continue contLoop;
          }
          this.pc = 346;
          continue contLoop;
        }
        this.pc = 346;
        continue contLoop;
      } else if (this.pc === 346) {
        break contLoop;
      } else if (this.pc === 345) {
        this.tmp$21 = runtime.resetDepth(this.tmp$21, this.curDepth$19);
        throw this.tmp$21;
      } else if (this.pc === 344) {
        this.tmp$20 = runtime.resetDepth(this.tmp$20, this.curDepth$19);
        throw this.tmp$20;
      } else if (this.pc === 353) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$14 = leList(this.x$5, this.y$11);
        if (this.scrut$14 instanceof runtime.EffectSig.class) {
          this.pc = 339;
          this.scrut$14.contTrace.last.next = this;
          this.scrut$14.contTrace.last = this;
          return this.scrut$14
        }
        this.pc = 339;
        continue contLoop;
      } else if (this.pc === 339) {
        this.scrut$14 = runtime.resetDepth(this.scrut$14, this.curDepth$19);
        if (this.scrut$14 === true) {
          this.pc = 349;
          continue contLoop;
        } else {
          this.pc = 352;
          continue contLoop;
        }
        this.pc = 346;
        continue contLoop;
      } else if (this.pc === 350) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(this.y$11, this.tmp$17, this.tmp$18)
      } else if (this.pc === 352) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$17 = Branch1(this.x$5, this.l1$6, this.r1$7);
        if (this.tmp$17 instanceof runtime.EffectSig.class) {
          this.pc = 342;
          this.tmp$17.contTrace.last.next = this;
          this.tmp$17.contTrace.last = this;
          return this.tmp$17
        }
        this.pc = 342;
        continue contLoop;
      } else if (this.pc === 342) {
        this.tmp$17 = runtime.resetDepth(this.tmp$17, this.curDepth$19);
        this.pc = 351;
        continue contLoop;
      } else if (this.pc === 351) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$18 = mix(this.l2$12, this.r2$13);
        if (this.tmp$18 instanceof runtime.EffectSig.class) {
          this.pc = 343;
          this.tmp$18.contTrace.last.next = this;
          this.tmp$18.contTrace.last = this;
          return this.tmp$18
        }
        this.pc = 343;
        continue contLoop;
      } else if (this.pc === 343) {
        this.tmp$18 = runtime.resetDepth(this.tmp$18, this.curDepth$19);
        this.pc = 350;
        continue contLoop;
      } else if (this.pc === 347) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return Branch1(this.x$5, this.tmp$15, this.tmp$16)
      } else if (this.pc === 349) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$15 = mix(this.l1$6, this.r1$7);
        if (this.tmp$15 instanceof runtime.EffectSig.class) {
          this.pc = 340;
          this.tmp$15.contTrace.last.next = this;
          this.tmp$15.contTrace.last = this;
          return this.tmp$15
        }
        this.pc = 340;
        continue contLoop;
      } else if (this.pc === 340) {
        this.tmp$15 = runtime.resetDepth(this.tmp$15, this.curDepth$19);
        this.pc = 348;
        continue contLoop;
      } else if (this.pc === 348) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$16 = Branch1(this.y$11, this.l2$12, this.r2$13);
        if (this.tmp$16 instanceof runtime.EffectSig.class) {
          this.pc = 341;
          this.tmp$16.contTrace.last.next = this;
          this.tmp$16.contTrace.last = this;
          return this.tmp$16
        }
        this.pc = 341;
        continue contLoop;
      } else if (this.pc === 341) {
        this.tmp$16 = runtime.resetDepth(this.tmp$16, this.curDepth$19);
        this.pc = 347;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$mix$sorting$_mls_L0_4601_4832$(" + globalThis.Predef.render(this.pc) + ")"; }
};
mix = function mix(l, r) {
  let param0, param1, param2, x, l1, r1, param01, param11, param21, y, l2, r2, scrut, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, tmp5, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$mix$sorting$_mls_L0_4601_4832$$(l, r, param0, param1, param2, x, l1, r1, param01, param11, param21, y, l2, r2, scrut, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, tmp5, stackDelayRes, 338);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (l instanceof Tip1.class) {
    return r
  } else {
    if (r instanceof Tip1.class) {
      return l
    } else {
      if (l instanceof Branch1.class) {
        param0 = l.a;
        param1 = l.l;
        param2 = l.r;
        x = param0;
        l1 = param1;
        r1 = param2;
        if (r instanceof Branch1.class) {
          param01 = r.a;
          param11 = r.l;
          param21 = r.r;
          y = param01;
          l2 = param11;
          r2 = param21;
          runtime.stackDepth = runtime.stackDepth + 1;
          scrut = leList(x, y);
          if (scrut instanceof runtime.EffectSig.class) {
            scrut.contTrace.last.next = Cont$func$mix$sorting$_mls_L0_4601_4832$$(l, r, param0, param1, param2, x, l1, r1, param01, param11, param21, y, l2, r2, scrut, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, tmp5, stackDelayRes, 339);
            scrut.contTrace.last = scrut.contTrace.last.next;
            return scrut
          }
          scrut = runtime.resetDepth(scrut, curDepth);
          if (scrut === true) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = mix(l1, r1);
            if (tmp instanceof runtime.EffectSig.class) {
              tmp.contTrace.last.next = Cont$func$mix$sorting$_mls_L0_4601_4832$$(l, r, param0, param1, param2, x, l1, r1, param01, param11, param21, y, l2, r2, scrut, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, tmp5, stackDelayRes, 340);
              tmp.contTrace.last = tmp.contTrace.last.next;
              return tmp
            }
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = Branch1(y, l2, r2);
            if (tmp1 instanceof runtime.EffectSig.class) {
              tmp1.contTrace.last.next = Cont$func$mix$sorting$_mls_L0_4601_4832$$(l, r, param0, param1, param2, x, l1, r1, param01, param11, param21, y, l2, r2, scrut, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, tmp5, stackDelayRes, 341);
              tmp1.contTrace.last = tmp1.contTrace.last.next;
              return tmp1
            }
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            return Branch1(x, tmp, tmp1)
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp2 = Branch1(x, l1, r1);
            if (tmp2 instanceof runtime.EffectSig.class) {
              tmp2.contTrace.last.next = Cont$func$mix$sorting$_mls_L0_4601_4832$$(l, r, param0, param1, param2, x, l1, r1, param01, param11, param21, y, l2, r2, scrut, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, tmp5, stackDelayRes, 342);
              tmp2.contTrace.last = tmp2.contTrace.last.next;
              return tmp2
            }
            tmp2 = runtime.resetDepth(tmp2, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp3 = mix(l2, r2);
            if (tmp3 instanceof runtime.EffectSig.class) {
              tmp3.contTrace.last.next = Cont$func$mix$sorting$_mls_L0_4601_4832$$(l, r, param0, param1, param2, x, l1, r1, param01, param11, param21, y, l2, r2, scrut, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, tmp5, stackDelayRes, 343);
              tmp3.contTrace.last = tmp3.contTrace.last.next;
              return tmp3
            }
            tmp3 = runtime.resetDepth(tmp3, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            return Branch1(y, tmp2, tmp3)
          }
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp4 = new globalThis.Error("match error");
          if (tmp4 instanceof runtime.EffectSig.class) {
            tmp4.contTrace.last.next = Cont$func$mix$sorting$_mls_L0_4601_4832$$(l, r, param0, param1, param2, x, l1, r1, param01, param11, param21, y, l2, r2, scrut, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, tmp5, stackDelayRes, 344);
            tmp4.contTrace.last = tmp4.contTrace.last.next;
            return tmp4
          }
          tmp4 = runtime.resetDepth(tmp4, curDepth);
          throw tmp4;
        }
      } else {
        runtime.stackDepth = runtime.stackDepth + 1;
        tmp5 = new globalThis.Error("match error");
        if (tmp5 instanceof runtime.EffectSig.class) {
          tmp5.contTrace.last.next = Cont$func$mix$sorting$_mls_L0_4601_4832$$(l, r, param0, param1, param2, x, l1, r1, param01, param11, param21, y, l2, r2, scrut, tmp, tmp1, tmp2, tmp3, curDepth, tmp4, tmp5, stackDelayRes, 345);
          tmp5.contTrace.last = tmp5.contTrace.last.next;
          return tmp5
        }
        tmp5 = runtime.resetDepth(tmp5, curDepth);
        throw tmp5;
      }
    }
  }
};
heapSort = function heapSort(xs) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$heapSort$sorting$_mls_L0_4049_4853$$(xs, tmp, curDepth, stackDelayRes, 272);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = heap(0, xs);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$heapSort$sorting$_mls_L0_4049_4853$$(xs, tmp, curDepth, stackDelayRes, 354);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return clear(tmp)
};
Cont$func$mergeSort$sorting$_mls_L0_4859_5754$$ = function Cont$func$mergeSort$sorting$_mls_L0_4859_5754$$(param$0, tmp$1, curDepth$2, stackDelayRes$3, pc) {
  let tmp;
  tmp = new Cont$func$mergeSort$sorting$_mls_L0_4859_5754$1.class(pc);
  return tmp(param$0, tmp$1, curDepth$2, stackDelayRes$3)
};
Cont$func$mergeSort$sorting$_mls_L0_4859_5754$$ctor = function Cont$func$mergeSort$sorting$_mls_L0_4859_5754$$ctor(param$0, tmp$1, curDepth$2, stackDelayRes$3) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$mergeSort$sorting$_mls_L0_4859_5754$1.class(pc);
    return tmp(param$0, tmp$1, curDepth$2, stackDelayRes$3)
  }
};
Cont$func$mergeSort$sorting$_mls_L0_4859_5754$1 = function Cont$func$mergeSort$sorting$_mls_L0_4859_5754$(pc1) {
  return (param$01, tmp$11, curDepth$21, stackDelayRes$31) => {
    return new Cont$func$mergeSort$sorting$_mls_L0_4859_5754$.class(pc1)(param$01, tmp$11, curDepth$21, stackDelayRes$31);
  }
};
Cont$func$mergeSort$sorting$_mls_L0_4859_5754$1.class = class Cont$func$mergeSort$sorting$_mls_L0_4859_5754$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (param$0, tmp$1, curDepth$2, stackDelayRes$3) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.param$0 = param$0;
      this.tmp$1 = tmp$1;
      this.curDepth$2 = curDepth$2;
      this.stackDelayRes$3 = stackDelayRes$3;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 357) {
      this.stackDelayRes$3 = value$;
    } else if (this.pc === 431) {
      this.tmp$1 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 357) {
        this.pc = 433;
        continue contLoop;
      } else if (this.pc === 432) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return merge_lists(this.tmp$1)
      } else if (this.pc === 433) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = runsplit(NofibPrelude.Nil, this.param$0);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 431;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 431;
        continue contLoop;
      } else if (this.pc === 431) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$2);
        this.pc = 432;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$mergeSort$sorting$_mls_L0_4859_5754$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$runsplit$sorting$_mls_L0_4884_5375$$ = function Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run$0, xs$1, param0$2, param1$3, r$4, rs$5, param0$6, param1$7, x$8, xs_$9, rs$10, scrut$11, scrut$12, scrut$13, x$14, xs_$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, tmp$27, tmp$28, curDepth$29, tmp$30, tmp$31, tmp$32, stackDelayRes$33, pc) {
  let tmp;
  tmp = new Cont$func$runsplit$sorting$_mls_L0_4884_5375$1.class(pc);
  return tmp(run$0, xs$1, param0$2, param1$3, r$4, rs$5, param0$6, param1$7, x$8, xs_$9, rs$10, scrut$11, scrut$12, scrut$13, x$14, xs_$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, tmp$27, tmp$28, curDepth$29, tmp$30, tmp$31, tmp$32, stackDelayRes$33)
};
Cont$func$runsplit$sorting$_mls_L0_4884_5375$$ctor = function Cont$func$runsplit$sorting$_mls_L0_4884_5375$$ctor(run$0, xs$1, param0$2, param1$3, r$4, rs$5, param0$6, param1$7, x$8, xs_$9, rs$10, scrut$11, scrut$12, scrut$13, x$14, xs_$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, tmp$27, tmp$28, curDepth$29, tmp$30, tmp$31, tmp$32, stackDelayRes$33) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$runsplit$sorting$_mls_L0_4884_5375$1.class(pc);
    return tmp(run$0, xs$1, param0$2, param1$3, r$4, rs$5, param0$6, param1$7, x$8, xs_$9, rs$10, scrut$11, scrut$12, scrut$13, x$14, xs_$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, tmp$27, tmp$28, curDepth$29, tmp$30, tmp$31, tmp$32, stackDelayRes$33)
  }
};
Cont$func$runsplit$sorting$_mls_L0_4884_5375$1 = function Cont$func$runsplit$sorting$_mls_L0_4884_5375$(pc1) {
  return (run$01, xs$11, param0$21, param1$31, r$41, rs$51, param0$61, param1$71, x$81, xs_$91, rs$101, scrut$111, scrut$121, scrut$131, x$141, xs_$151, tmp$161, tmp$171, tmp$181, tmp$191, tmp$201, tmp$211, tmp$221, tmp$231, tmp$241, tmp$251, tmp$261, tmp$271, tmp$281, curDepth$291, tmp$301, tmp$311, tmp$321, stackDelayRes$331) => {
    return new Cont$func$runsplit$sorting$_mls_L0_4884_5375$.class(pc1)(run$01, xs$11, param0$21, param1$31, r$41, rs$51, param0$61, param1$71, x$81, xs_$91, rs$101, scrut$111, scrut$121, scrut$131, x$141, xs_$151, tmp$161, tmp$171, tmp$181, tmp$191, tmp$201, tmp$211, tmp$221, tmp$231, tmp$241, tmp$251, tmp$261, tmp$271, tmp$281, curDepth$291, tmp$301, tmp$311, tmp$321, stackDelayRes$331);
  }
};
Cont$func$runsplit$sorting$_mls_L0_4884_5375$1.class = class Cont$func$runsplit$sorting$_mls_L0_4884_5375$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (run$0, xs$1, param0$2, param1$3, r$4, rs$5, param0$6, param1$7, x$8, xs_$9, rs$10, scrut$11, scrut$12, scrut$13, x$14, xs_$15, tmp$16, tmp$17, tmp$18, tmp$19, tmp$20, tmp$21, tmp$22, tmp$23, tmp$24, tmp$25, tmp$26, tmp$27, tmp$28, curDepth$29, tmp$30, tmp$31, tmp$32, stackDelayRes$33) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.run$0 = run$0;
      this.xs$1 = xs$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.r$4 = r$4;
      this.rs$5 = rs$5;
      this.param0$6 = param0$6;
      this.param1$7 = param1$7;
      this.x$8 = x$8;
      this.xs_$9 = xs_$9;
      this.rs$10 = rs$10;
      this.scrut$11 = scrut$11;
      this.scrut$12 = scrut$12;
      this.scrut$13 = scrut$13;
      this.x$14 = x$14;
      this.xs_$15 = xs_$15;
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
      this.curDepth$29 = curDepth$29;
      this.tmp$30 = tmp$30;
      this.tmp$31 = tmp$31;
      this.tmp$32 = tmp$32;
      this.stackDelayRes$33 = stackDelayRes$33;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 358) {
      this.stackDelayRes$33 = value$;
    } else if (this.pc === 377) {
      this.tmp$32 = value$;
    } else if (this.pc === 376) {
      this.tmp$31 = value$;
    } else if (this.pc === 370) {
      this.scrut$11 = value$;
    } else if (this.pc === 373) {
      this.tmp$26 = value$;
    } else if (this.pc === 374) {
      this.tmp$27 = value$;
    } else if (this.pc === 375) {
      this.tmp$28 = value$;
    } else if (this.pc === 371) {
      this.tmp$24 = value$;
    } else if (this.pc === 372) {
      this.tmp$25 = value$;
    } else if (this.pc === 361) {
      this.scrut$13 = value$;
    } else if (this.pc === 364) {
      this.scrut$12 = value$;
    } else if (this.pc === 367) {
      this.tmp$21 = value$;
    } else if (this.pc === 368) {
      this.tmp$22 = value$;
    } else if (this.pc === 369) {
      this.tmp$23 = value$;
    } else if (this.pc === 365) {
      this.tmp$19 = value$;
    } else if (this.pc === 366) {
      this.tmp$20 = value$;
    } else if (this.pc === 362) {
      this.tmp$17 = value$;
    } else if (this.pc === 363) {
      this.tmp$18 = value$;
    } else if (this.pc === 360) {
      this.tmp$30 = value$;
    } else if (this.pc === 359) {
      this.tmp$16 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 358) {
        if (this.run$0 instanceof NofibPrelude.Nil.class) {
          if (this.xs$1 instanceof NofibPrelude.Nil.class) {
            return NofibPrelude.Nil
          } else if (this.xs$1 instanceof NofibPrelude.Cons.class) {
            this.param0$6 = this.xs$1.head;
            this.param1$7 = this.xs$1.tail;
            this.x$14 = this.param0$6;
            this.xs_$15 = this.param1$7;
            this.pc = 380;
            continue contLoop;
            this.pc = 378;
            continue contLoop;
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            this.tmp$30 = new globalThis.Error("match error");
            if (this.tmp$30 instanceof runtime.EffectSig.class) {
              this.pc = 360;
              this.tmp$30.contTrace.last.next = this;
              this.tmp$30.contTrace.last = this;
              return this.tmp$30
            }
            this.pc = 360;
            continue contLoop;
          }
          this.pc = 378;
          continue contLoop;
        } else {
          if (this.xs$1 instanceof NofibPrelude.Nil.class) {
            this.pc = 381;
            continue contLoop;
          } else {
            if (this.run$0 instanceof NofibPrelude.Cons.class) {
              this.param0$2 = this.run$0.head;
              this.param1$3 = this.run$0.tail;
              this.r$4 = this.param0$2;
              this.rs$5 = this.param1$3;
              if (this.xs$1 instanceof NofibPrelude.Cons.class) {
                this.param0$6 = this.xs$1.head;
                this.param1$7 = this.xs$1.tail;
                this.x$8 = this.param0$6;
                this.xs_$9 = this.param1$7;
                if (this.rs$5 instanceof NofibPrelude.Nil.class) {
                  this.pc = 393;
                  continue contLoop;
                } else {
                  this.rs$10 = this.rs$5;
                  this.pc = 401;
                  continue contLoop;
                }
                this.pc = 378;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.tmp$31 = new globalThis.Error("match error");
                if (this.tmp$31 instanceof runtime.EffectSig.class) {
                  this.pc = 376;
                  this.tmp$31.contTrace.last.next = this;
                  this.tmp$31.contTrace.last = this;
                  return this.tmp$31
                }
                this.pc = 376;
                continue contLoop;
              }
              this.pc = 378;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.tmp$32 = new globalThis.Error("match error");
              if (this.tmp$32 instanceof runtime.EffectSig.class) {
                this.pc = 377;
                this.tmp$32.contTrace.last.next = this;
                this.tmp$32.contTrace.last = this;
                return this.tmp$32
              }
              this.pc = 377;
              continue contLoop;
            }
            this.pc = 378;
            continue contLoop;
          }
          this.pc = 378;
          continue contLoop;
        }
        this.pc = 378;
        continue contLoop;
      } else if (this.pc === 378) {
        break contLoop;
      } else if (this.pc === 377) {
        this.tmp$32 = runtime.resetDepth(this.tmp$32, this.curDepth$29);
        throw this.tmp$32;
      } else if (this.pc === 376) {
        this.tmp$31 = runtime.resetDepth(this.tmp$31, this.curDepth$29);
        throw this.tmp$31;
      } else if (this.pc === 401) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$11 = leList(this.x$8, this.r$4);
        if (this.scrut$11 instanceof runtime.EffectSig.class) {
          this.pc = 370;
          this.scrut$11.contTrace.last.next = this;
          this.scrut$11.contTrace.last = this;
          return this.scrut$11
        }
        this.pc = 370;
        continue contLoop;
      } else if (this.pc === 370) {
        this.scrut$11 = runtime.resetDepth(this.scrut$11, this.curDepth$29);
        if (this.scrut$11 === true) {
          this.pc = 396;
          continue contLoop;
        } else {
          this.pc = 400;
          continue contLoop;
        }
        this.pc = 378;
        continue contLoop;
      } else if (this.pc === 397) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.tmp$26, this.tmp$28)
      } else if (this.pc === 400) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$26 = NofibPrelude.Cons(this.r$4, this.rs$10);
        if (this.tmp$26 instanceof runtime.EffectSig.class) {
          this.pc = 373;
          this.tmp$26.contTrace.last.next = this;
          this.tmp$26.contTrace.last = this;
          return this.tmp$26
        }
        this.pc = 373;
        continue contLoop;
      } else if (this.pc === 373) {
        this.tmp$26 = runtime.resetDepth(this.tmp$26, this.curDepth$29);
        this.pc = 399;
        continue contLoop;
      } else if (this.pc === 398) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$28 = runsplit(this.tmp$27, this.xs_$9);
        if (this.tmp$28 instanceof runtime.EffectSig.class) {
          this.pc = 375;
          this.tmp$28.contTrace.last.next = this;
          this.tmp$28.contTrace.last = this;
          return this.tmp$28
        }
        this.pc = 375;
        continue contLoop;
      } else if (this.pc === 399) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$27 = NofibPrelude.Cons(this.x$8, NofibPrelude.Nil);
        if (this.tmp$27 instanceof runtime.EffectSig.class) {
          this.pc = 374;
          this.tmp$27.contTrace.last.next = this;
          this.tmp$27.contTrace.last = this;
          return this.tmp$27
        }
        this.pc = 374;
        continue contLoop;
      } else if (this.pc === 374) {
        this.tmp$27 = runtime.resetDepth(this.tmp$27, this.curDepth$29);
        this.pc = 398;
        continue contLoop;
      } else if (this.pc === 375) {
        this.tmp$28 = runtime.resetDepth(this.tmp$28, this.curDepth$29);
        this.pc = 397;
        continue contLoop;
      } else if (this.pc === 394) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runsplit(this.tmp$25, this.xs_$9)
      } else if (this.pc === 395) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$25 = NofibPrelude.Cons(this.x$8, this.tmp$24);
        if (this.tmp$25 instanceof runtime.EffectSig.class) {
          this.pc = 372;
          this.tmp$25.contTrace.last.next = this;
          this.tmp$25.contTrace.last = this;
          return this.tmp$25
        }
        this.pc = 372;
        continue contLoop;
      } else if (this.pc === 396) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$24 = NofibPrelude.Cons(this.r$4, this.rs$10);
        if (this.tmp$24 instanceof runtime.EffectSig.class) {
          this.pc = 371;
          this.tmp$24.contTrace.last.next = this;
          this.tmp$24.contTrace.last = this;
          return this.tmp$24
        }
        this.pc = 371;
        continue contLoop;
      } else if (this.pc === 371) {
        this.tmp$24 = runtime.resetDepth(this.tmp$24, this.curDepth$29);
        this.pc = 395;
        continue contLoop;
      } else if (this.pc === 372) {
        this.tmp$25 = runtime.resetDepth(this.tmp$25, this.curDepth$29);
        this.pc = 394;
        continue contLoop;
      } else if (this.pc === 393) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$13 = gtList(this.x$8, this.r$4);
        if (this.scrut$13 instanceof runtime.EffectSig.class) {
          this.pc = 361;
          this.scrut$13.contTrace.last.next = this;
          this.scrut$13.contTrace.last = this;
          return this.scrut$13
        }
        this.pc = 361;
        continue contLoop;
      } else if (this.pc === 361) {
        this.scrut$13 = runtime.resetDepth(this.scrut$13, this.curDepth$29);
        if (this.scrut$13 === true) {
          this.pc = 384;
          continue contLoop;
        } else {
          this.pc = 392;
          continue contLoop;
        }
        this.pc = 378;
        continue contLoop;
      } else if (this.pc === 392) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$12 = leList(this.x$8, this.r$4);
        if (this.scrut$12 instanceof runtime.EffectSig.class) {
          this.pc = 364;
          this.scrut$12.contTrace.last.next = this;
          this.scrut$12.contTrace.last = this;
          return this.scrut$12
        }
        this.pc = 364;
        continue contLoop;
      } else if (this.pc === 364) {
        this.scrut$12 = runtime.resetDepth(this.scrut$12, this.curDepth$29);
        if (this.scrut$12 === true) {
          this.pc = 387;
          continue contLoop;
        } else {
          this.pc = 391;
          continue contLoop;
        }
        this.pc = 378;
        continue contLoop;
      } else if (this.pc === 388) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.tmp$21, this.tmp$23)
      } else if (this.pc === 391) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$21 = NofibPrelude.Cons(this.r$4, this.rs$5);
        if (this.tmp$21 instanceof runtime.EffectSig.class) {
          this.pc = 367;
          this.tmp$21.contTrace.last.next = this;
          this.tmp$21.contTrace.last = this;
          return this.tmp$21
        }
        this.pc = 367;
        continue contLoop;
      } else if (this.pc === 367) {
        this.tmp$21 = runtime.resetDepth(this.tmp$21, this.curDepth$29);
        this.pc = 390;
        continue contLoop;
      } else if (this.pc === 389) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$23 = runsplit(this.tmp$22, this.xs_$9);
        if (this.tmp$23 instanceof runtime.EffectSig.class) {
          this.pc = 369;
          this.tmp$23.contTrace.last.next = this;
          this.tmp$23.contTrace.last = this;
          return this.tmp$23
        }
        this.pc = 369;
        continue contLoop;
      } else if (this.pc === 390) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$22 = NofibPrelude.Cons(this.x$8, NofibPrelude.Nil);
        if (this.tmp$22 instanceof runtime.EffectSig.class) {
          this.pc = 368;
          this.tmp$22.contTrace.last.next = this;
          this.tmp$22.contTrace.last = this;
          return this.tmp$22
        }
        this.pc = 368;
        continue contLoop;
      } else if (this.pc === 368) {
        this.tmp$22 = runtime.resetDepth(this.tmp$22, this.curDepth$29);
        this.pc = 389;
        continue contLoop;
      } else if (this.pc === 369) {
        this.tmp$23 = runtime.resetDepth(this.tmp$23, this.curDepth$29);
        this.pc = 388;
        continue contLoop;
      } else if (this.pc === 385) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runsplit(this.tmp$20, this.xs_$9)
      } else if (this.pc === 386) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$20 = NofibPrelude.Cons(this.x$8, this.tmp$19);
        if (this.tmp$20 instanceof runtime.EffectSig.class) {
          this.pc = 366;
          this.tmp$20.contTrace.last.next = this;
          this.tmp$20.contTrace.last = this;
          return this.tmp$20
        }
        this.pc = 366;
        continue contLoop;
      } else if (this.pc === 387) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$19 = NofibPrelude.Cons(this.r$4, this.rs$5);
        if (this.tmp$19 instanceof runtime.EffectSig.class) {
          this.pc = 365;
          this.tmp$19.contTrace.last.next = this;
          this.tmp$19.contTrace.last = this;
          return this.tmp$19
        }
        this.pc = 365;
        continue contLoop;
      } else if (this.pc === 365) {
        this.tmp$19 = runtime.resetDepth(this.tmp$19, this.curDepth$29);
        this.pc = 386;
        continue contLoop;
      } else if (this.pc === 366) {
        this.tmp$20 = runtime.resetDepth(this.tmp$20, this.curDepth$29);
        this.pc = 385;
        continue contLoop;
      } else if (this.pc === 382) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runsplit(this.tmp$18, this.xs_$9)
      } else if (this.pc === 383) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$18 = NofibPrelude.Cons(this.r$4, this.tmp$17);
        if (this.tmp$18 instanceof runtime.EffectSig.class) {
          this.pc = 363;
          this.tmp$18.contTrace.last.next = this;
          this.tmp$18.contTrace.last = this;
          return this.tmp$18
        }
        this.pc = 363;
        continue contLoop;
      } else if (this.pc === 384) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$17 = NofibPrelude.Cons(this.x$8, NofibPrelude.Nil);
        if (this.tmp$17 instanceof runtime.EffectSig.class) {
          this.pc = 362;
          this.tmp$17.contTrace.last.next = this;
          this.tmp$17.contTrace.last = this;
          return this.tmp$17
        }
        this.pc = 362;
        continue contLoop;
      } else if (this.pc === 362) {
        this.tmp$17 = runtime.resetDepth(this.tmp$17, this.curDepth$29);
        this.pc = 383;
        continue contLoop;
      } else if (this.pc === 363) {
        this.tmp$18 = runtime.resetDepth(this.tmp$18, this.curDepth$29);
        this.pc = 382;
        continue contLoop;
      } else if (this.pc === 381) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.run$0, NofibPrelude.Nil)
      } else if (this.pc === 360) {
        this.tmp$30 = runtime.resetDepth(this.tmp$30, this.curDepth$29);
        throw this.tmp$30;
      } else if (this.pc === 379) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runsplit(this.tmp$16, this.xs_$15)
      } else if (this.pc === 380) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$16 = NofibPrelude.Cons(this.x$14, NofibPrelude.Nil);
        if (this.tmp$16 instanceof runtime.EffectSig.class) {
          this.pc = 359;
          this.tmp$16.contTrace.last.next = this;
          this.tmp$16.contTrace.last = this;
          return this.tmp$16
        }
        this.pc = 359;
        continue contLoop;
      } else if (this.pc === 359) {
        this.tmp$16 = runtime.resetDepth(this.tmp$16, this.curDepth$29);
        this.pc = 379;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$runsplit$sorting$_mls_L0_4884_5375$(" + globalThis.Predef.render(this.pc) + ")"; }
};
runsplit = function runsplit(run, xs) {
  let param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 358);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (run instanceof NofibPrelude.Nil.class) {
    if (xs instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param01 = xs.head;
      param11 = xs.tail;
      x1 = param01;
      xs_1 = param11;
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp = NofibPrelude.Cons(x1, NofibPrelude.Nil);
      if (tmp instanceof runtime.EffectSig.class) {
        tmp.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 359);
        tmp.contTrace.last = tmp.contTrace.last.next;
        return tmp
      }
      tmp = runtime.resetDepth(tmp, curDepth);
      runtime.stackDepth = runtime.stackDepth + 1;
      return runsplit(tmp, xs_1)
    } else {
      runtime.stackDepth = runtime.stackDepth + 1;
      tmp13 = new globalThis.Error("match error");
      if (tmp13 instanceof runtime.EffectSig.class) {
        tmp13.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 360);
        tmp13.contTrace.last = tmp13.contTrace.last.next;
        return tmp13
      }
      tmp13 = runtime.resetDepth(tmp13, curDepth);
      throw tmp13;
    }
  } else {
    if (xs instanceof NofibPrelude.Nil.class) {
      runtime.stackDepth = runtime.stackDepth + 1;
      return NofibPrelude.Cons(run, NofibPrelude.Nil)
    } else {
      if (run instanceof NofibPrelude.Cons.class) {
        param0 = run.head;
        param1 = run.tail;
        r = param0;
        rs = param1;
        if (xs instanceof NofibPrelude.Cons.class) {
          param01 = xs.head;
          param11 = xs.tail;
          x = param01;
          xs_ = param11;
          if (rs instanceof NofibPrelude.Nil.class) {
            runtime.stackDepth = runtime.stackDepth + 1;
            scrut2 = gtList(x, r);
            if (scrut2 instanceof runtime.EffectSig.class) {
              scrut2.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 361);
              scrut2.contTrace.last = scrut2.contTrace.last.next;
              return scrut2
            }
            scrut2 = runtime.resetDepth(scrut2, curDepth);
            if (scrut2 === true) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp1 = NofibPrelude.Cons(x, NofibPrelude.Nil);
              if (tmp1 instanceof runtime.EffectSig.class) {
                tmp1.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 362);
                tmp1.contTrace.last = tmp1.contTrace.last.next;
                return tmp1
              }
              tmp1 = runtime.resetDepth(tmp1, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp2 = NofibPrelude.Cons(r, tmp1);
              if (tmp2 instanceof runtime.EffectSig.class) {
                tmp2.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 363);
                tmp2.contTrace.last = tmp2.contTrace.last.next;
                return tmp2
              }
              tmp2 = runtime.resetDepth(tmp2, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              return runsplit(tmp2, xs_)
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              scrut1 = leList(x, r);
              if (scrut1 instanceof runtime.EffectSig.class) {
                scrut1.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 364);
                scrut1.contTrace.last = scrut1.contTrace.last.next;
                return scrut1
              }
              scrut1 = runtime.resetDepth(scrut1, curDepth);
              if (scrut1 === true) {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp3 = NofibPrelude.Cons(r, rs);
                if (tmp3 instanceof runtime.EffectSig.class) {
                  tmp3.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 365);
                  tmp3.contTrace.last = tmp3.contTrace.last.next;
                  return tmp3
                }
                tmp3 = runtime.resetDepth(tmp3, curDepth);
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp4 = NofibPrelude.Cons(x, tmp3);
                if (tmp4 instanceof runtime.EffectSig.class) {
                  tmp4.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 366);
                  tmp4.contTrace.last = tmp4.contTrace.last.next;
                  return tmp4
                }
                tmp4 = runtime.resetDepth(tmp4, curDepth);
                runtime.stackDepth = runtime.stackDepth + 1;
                return runsplit(tmp4, xs_)
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp5 = NofibPrelude.Cons(r, rs);
                if (tmp5 instanceof runtime.EffectSig.class) {
                  tmp5.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 367);
                  tmp5.contTrace.last = tmp5.contTrace.last.next;
                  return tmp5
                }
                tmp5 = runtime.resetDepth(tmp5, curDepth);
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp6 = NofibPrelude.Cons(x, NofibPrelude.Nil);
                if (tmp6 instanceof runtime.EffectSig.class) {
                  tmp6.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 368);
                  tmp6.contTrace.last = tmp6.contTrace.last.next;
                  return tmp6
                }
                tmp6 = runtime.resetDepth(tmp6, curDepth);
                runtime.stackDepth = runtime.stackDepth + 1;
                tmp7 = runsplit(tmp6, xs_);
                if (tmp7 instanceof runtime.EffectSig.class) {
                  tmp7.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 369);
                  tmp7.contTrace.last = tmp7.contTrace.last.next;
                  return tmp7
                }
                tmp7 = runtime.resetDepth(tmp7, curDepth);
                runtime.stackDepth = runtime.stackDepth + 1;
                return NofibPrelude.Cons(tmp5, tmp7)
              }
            }
          } else {
            rs1 = rs;
            runtime.stackDepth = runtime.stackDepth + 1;
            scrut = leList(x, r);
            if (scrut instanceof runtime.EffectSig.class) {
              scrut.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 370);
              scrut.contTrace.last = scrut.contTrace.last.next;
              return scrut
            }
            scrut = runtime.resetDepth(scrut, curDepth);
            if (scrut === true) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp8 = NofibPrelude.Cons(r, rs1);
              if (tmp8 instanceof runtime.EffectSig.class) {
                tmp8.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 371);
                tmp8.contTrace.last = tmp8.contTrace.last.next;
                return tmp8
              }
              tmp8 = runtime.resetDepth(tmp8, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp9 = NofibPrelude.Cons(x, tmp8);
              if (tmp9 instanceof runtime.EffectSig.class) {
                tmp9.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 372);
                tmp9.contTrace.last = tmp9.contTrace.last.next;
                return tmp9
              }
              tmp9 = runtime.resetDepth(tmp9, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              return runsplit(tmp9, xs_)
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp10 = NofibPrelude.Cons(r, rs1);
              if (tmp10 instanceof runtime.EffectSig.class) {
                tmp10.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 373);
                tmp10.contTrace.last = tmp10.contTrace.last.next;
                return tmp10
              }
              tmp10 = runtime.resetDepth(tmp10, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp11 = NofibPrelude.Cons(x, NofibPrelude.Nil);
              if (tmp11 instanceof runtime.EffectSig.class) {
                tmp11.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 374);
                tmp11.contTrace.last = tmp11.contTrace.last.next;
                return tmp11
              }
              tmp11 = runtime.resetDepth(tmp11, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp12 = runsplit(tmp11, xs_);
              if (tmp12 instanceof runtime.EffectSig.class) {
                tmp12.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 375);
                tmp12.contTrace.last = tmp12.contTrace.last.next;
                return tmp12
              }
              tmp12 = runtime.resetDepth(tmp12, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              return NofibPrelude.Cons(tmp10, tmp12)
            }
          }
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp14 = new globalThis.Error("match error");
          if (tmp14 instanceof runtime.EffectSig.class) {
            tmp14.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 376);
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
          tmp15.contTrace.last.next = Cont$func$runsplit$sorting$_mls_L0_4884_5375$$(run, xs, param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, curDepth, tmp13, tmp14, tmp15, stackDelayRes, 377);
          tmp15.contTrace.last = tmp15.contTrace.last.next;
          return tmp15
        }
        tmp15 = runtime.resetDepth(tmp15, curDepth);
        throw tmp15;
      }
    }
  }
};
Cont$func$merge_lists$sorting$_mls_L0_5382_5470$$ = function Cont$func$merge_lists$sorting$_mls_L0_5382_5470$$(xs$0, param0$1, param1$2, x$3, xs_$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8, pc) {
  let tmp;
  tmp = new Cont$func$merge_lists$sorting$_mls_L0_5382_5470$1.class(pc);
  return tmp(xs$0, param0$1, param1$2, x$3, xs_$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8)
};
Cont$func$merge_lists$sorting$_mls_L0_5382_5470$$ctor = function Cont$func$merge_lists$sorting$_mls_L0_5382_5470$$ctor(xs$0, param0$1, param1$2, x$3, xs_$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$merge_lists$sorting$_mls_L0_5382_5470$1.class(pc);
    return tmp(xs$0, param0$1, param1$2, x$3, xs_$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8)
  }
};
Cont$func$merge_lists$sorting$_mls_L0_5382_5470$1 = function Cont$func$merge_lists$sorting$_mls_L0_5382_5470$(pc1) {
  return (xs$01, param0$11, param1$21, x$31, xs_$41, tmp$51, curDepth$61, tmp$71, stackDelayRes$81) => {
    return new Cont$func$merge_lists$sorting$_mls_L0_5382_5470$.class(pc1)(xs$01, param0$11, param1$21, x$31, xs_$41, tmp$51, curDepth$61, tmp$71, stackDelayRes$81);
  }
};
Cont$func$merge_lists$sorting$_mls_L0_5382_5470$1.class = class Cont$func$merge_lists$sorting$_mls_L0_5382_5470$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (xs$0, param0$1, param1$2, x$3, xs_$4, tmp$5, curDepth$6, tmp$7, stackDelayRes$8) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.xs$0 = xs$0;
      this.param0$1 = param0$1;
      this.param1$2 = param1$2;
      this.x$3 = x$3;
      this.xs_$4 = xs_$4;
      this.tmp$5 = tmp$5;
      this.curDepth$6 = curDepth$6;
      this.tmp$7 = tmp$7;
      this.stackDelayRes$8 = stackDelayRes$8;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 402) {
      this.stackDelayRes$8 = value$;
    } else if (this.pc === 404) {
      this.tmp$7 = value$;
    } else if (this.pc === 403) {
      this.tmp$5 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 402) {
        if (this.xs$0 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (this.xs$0 instanceof NofibPrelude.Cons.class) {
          this.param0$1 = this.xs$0.head;
          this.param1$2 = this.xs$0.tail;
          this.x$3 = this.param0$1;
          this.xs_$4 = this.param1$2;
          this.pc = 407;
          continue contLoop;
          this.pc = 405;
          continue contLoop;
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          this.tmp$7 = new globalThis.Error("match error");
          if (this.tmp$7 instanceof runtime.EffectSig.class) {
            this.pc = 404;
            this.tmp$7.contTrace.last.next = this;
            this.tmp$7.contTrace.last = this;
            return this.tmp$7
          }
          this.pc = 404;
          continue contLoop;
        }
        this.pc = 405;
        continue contLoop;
      } else if (this.pc === 405) {
        break contLoop;
      } else if (this.pc === 404) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$6);
        throw this.tmp$7;
      } else if (this.pc === 406) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return merge(this.x$3, this.tmp$5)
      } else if (this.pc === 407) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = merge_lists(this.xs_$4);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 403;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 403;
        continue contLoop;
      } else if (this.pc === 403) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$6);
        this.pc = 406;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$merge_lists$sorting$_mls_L0_5382_5470$(" + globalThis.Predef.render(this.pc) + ")"; }
};
merge_lists = function merge_lists(xs) {
  let param0, param1, x, xs_, tmp, curDepth, tmp1, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$merge_lists$sorting$_mls_L0_5382_5470$$(xs, param0, param1, x, xs_, tmp, curDepth, tmp1, stackDelayRes, 402);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (xs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs_ = param1;
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp = merge_lists(xs_);
    if (tmp instanceof runtime.EffectSig.class) {
      tmp.contTrace.last.next = Cont$func$merge_lists$sorting$_mls_L0_5382_5470$$(xs, param0, param1, x, xs_, tmp, curDepth, tmp1, stackDelayRes, 403);
      tmp.contTrace.last = tmp.contTrace.last.next;
      return tmp
    }
    tmp = runtime.resetDepth(tmp, curDepth);
    runtime.stackDepth = runtime.stackDepth + 1;
    return merge(x, tmp)
  } else {
    runtime.stackDepth = runtime.stackDepth + 1;
    tmp1 = new globalThis.Error("match error");
    if (tmp1 instanceof runtime.EffectSig.class) {
      tmp1.contTrace.last.next = Cont$func$merge_lists$sorting$_mls_L0_5382_5470$$(xs, param0, param1, x, xs_, tmp, curDepth, tmp1, stackDelayRes, 404);
      tmp1.contTrace.last = tmp1.contTrace.last.next;
      return tmp1
    }
    tmp1 = runtime.resetDepth(tmp1, curDepth);
    throw tmp1;
  }
};
Cont$func$merge$sorting$_mls_L0_5477_5718$$ = function Cont$func$merge$sorting$_mls_L0_5477_5718$$(xs$0, ys$1, param0$2, param1$3, x$4, xs_$5, param0$6, param1$7, y$8, ys_$9, scrut$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, curDepth$18, tmp$19, tmp$20, stackDelayRes$21, pc) {
  let tmp;
  tmp = new Cont$func$merge$sorting$_mls_L0_5477_5718$1.class(pc);
  return tmp(xs$0, ys$1, param0$2, param1$3, x$4, xs_$5, param0$6, param1$7, y$8, ys_$9, scrut$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, curDepth$18, tmp$19, tmp$20, stackDelayRes$21)
};
Cont$func$merge$sorting$_mls_L0_5477_5718$$ctor = function Cont$func$merge$sorting$_mls_L0_5477_5718$$ctor(xs$0, ys$1, param0$2, param1$3, x$4, xs_$5, param0$6, param1$7, y$8, ys_$9, scrut$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, curDepth$18, tmp$19, tmp$20, stackDelayRes$21) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$merge$sorting$_mls_L0_5477_5718$1.class(pc);
    return tmp(xs$0, ys$1, param0$2, param1$3, x$4, xs_$5, param0$6, param1$7, y$8, ys_$9, scrut$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, curDepth$18, tmp$19, tmp$20, stackDelayRes$21)
  }
};
Cont$func$merge$sorting$_mls_L0_5477_5718$1 = function Cont$func$merge$sorting$_mls_L0_5477_5718$(pc1) {
  return (xs$01, ys$11, param0$21, param1$31, x$41, xs_$51, param0$61, param1$71, y$81, ys_$91, scrut$101, scrut$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, tmp$171, curDepth$181, tmp$191, tmp$201, stackDelayRes$211) => {
    return new Cont$func$merge$sorting$_mls_L0_5477_5718$.class(pc1)(xs$01, ys$11, param0$21, param1$31, x$41, xs_$51, param0$61, param1$71, y$81, ys_$91, scrut$101, scrut$111, tmp$121, tmp$131, tmp$141, tmp$151, tmp$161, tmp$171, curDepth$181, tmp$191, tmp$201, stackDelayRes$211);
  }
};
Cont$func$merge$sorting$_mls_L0_5477_5718$1.class = class Cont$func$merge$sorting$_mls_L0_5477_5718$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (xs$0, ys$1, param0$2, param1$3, x$4, xs_$5, param0$6, param1$7, y$8, ys_$9, scrut$10, scrut$11, tmp$12, tmp$13, tmp$14, tmp$15, tmp$16, tmp$17, curDepth$18, tmp$19, tmp$20, stackDelayRes$21) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.xs$0 = xs$0;
      this.ys$1 = ys$1;
      this.param0$2 = param0$2;
      this.param1$3 = param1$3;
      this.x$4 = x$4;
      this.xs_$5 = xs_$5;
      this.param0$6 = param0$6;
      this.param1$7 = param1$7;
      this.y$8 = y$8;
      this.ys_$9 = ys_$9;
      this.scrut$10 = scrut$10;
      this.scrut$11 = scrut$11;
      this.tmp$12 = tmp$12;
      this.tmp$13 = tmp$13;
      this.tmp$14 = tmp$14;
      this.tmp$15 = tmp$15;
      this.tmp$16 = tmp$16;
      this.tmp$17 = tmp$17;
      this.curDepth$18 = curDepth$18;
      this.tmp$19 = tmp$19;
      this.tmp$20 = tmp$20;
      this.stackDelayRes$21 = stackDelayRes$21;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 408) {
      this.stackDelayRes$21 = value$;
    } else if (this.pc === 418) {
      this.tmp$20 = value$;
    } else if (this.pc === 417) {
      this.tmp$19 = value$;
    } else if (this.pc === 409) {
      this.scrut$11 = value$;
    } else if (this.pc === 412) {
      this.scrut$10 = value$;
    } else if (this.pc === 415) {
      this.tmp$16 = value$;
    } else if (this.pc === 416) {
      this.tmp$17 = value$;
    } else if (this.pc === 413) {
      this.tmp$14 = value$;
    } else if (this.pc === 414) {
      this.tmp$15 = value$;
    } else if (this.pc === 410) {
      this.tmp$12 = value$;
    } else if (this.pc === 411) {
      this.tmp$13 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 408) {
        if (this.xs$0 instanceof NofibPrelude.Nil.class) {
          return this.ys$1
        } else {
          if (this.ys$1 instanceof NofibPrelude.Nil.class) {
            return this.xs$0
          } else {
            if (this.xs$0 instanceof NofibPrelude.Cons.class) {
              this.param0$2 = this.xs$0.head;
              this.param1$3 = this.xs$0.tail;
              this.x$4 = this.param0$2;
              this.xs_$5 = this.param1$3;
              if (this.ys$1 instanceof NofibPrelude.Cons.class) {
                this.param0$6 = this.ys$1.head;
                this.param1$7 = this.ys$1.tail;
                this.y$8 = this.param0$6;
                this.ys_$9 = this.param1$7;
                this.pc = 430;
                continue contLoop;
              } else {
                runtime.stackDepth = runtime.stackDepth + 1;
                this.tmp$19 = new globalThis.Error("match error");
                if (this.tmp$19 instanceof runtime.EffectSig.class) {
                  this.pc = 417;
                  this.tmp$19.contTrace.last.next = this;
                  this.tmp$19.contTrace.last = this;
                  return this.tmp$19
                }
                this.pc = 417;
                continue contLoop;
              }
              this.pc = 419;
              continue contLoop;
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              this.tmp$20 = new globalThis.Error("match error");
              if (this.tmp$20 instanceof runtime.EffectSig.class) {
                this.pc = 418;
                this.tmp$20.contTrace.last.next = this;
                this.tmp$20.contTrace.last = this;
                return this.tmp$20
              }
              this.pc = 418;
              continue contLoop;
            }
            this.pc = 419;
            continue contLoop;
          }
          this.pc = 419;
          continue contLoop;
        }
        this.pc = 419;
        continue contLoop;
      } else if (this.pc === 419) {
        break contLoop;
      } else if (this.pc === 418) {
        this.tmp$20 = runtime.resetDepth(this.tmp$20, this.curDepth$18);
        throw this.tmp$20;
      } else if (this.pc === 417) {
        this.tmp$19 = runtime.resetDepth(this.tmp$19, this.curDepth$18);
        throw this.tmp$19;
      } else if (this.pc === 430) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$11 = eqList(this.x$4, this.y$8);
        if (this.scrut$11 instanceof runtime.EffectSig.class) {
          this.pc = 409;
          this.scrut$11.contTrace.last.next = this;
          this.scrut$11.contTrace.last = this;
          return this.scrut$11
        }
        this.pc = 409;
        continue contLoop;
      } else if (this.pc === 409) {
        this.scrut$11 = runtime.resetDepth(this.scrut$11, this.curDepth$18);
        if (this.scrut$11 === true) {
          this.pc = 422;
          continue contLoop;
        } else {
          this.pc = 429;
          continue contLoop;
        }
        this.pc = 419;
        continue contLoop;
      } else if (this.pc === 429) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.scrut$10 = NofibPrelude.ltList(this.x$4, this.y$8);
        if (this.scrut$10 instanceof runtime.EffectSig.class) {
          this.pc = 412;
          this.scrut$10.contTrace.last.next = this;
          this.scrut$10.contTrace.last = this;
          return this.scrut$10
        }
        this.pc = 412;
        continue contLoop;
      } else if (this.pc === 412) {
        this.scrut$10 = runtime.resetDepth(this.scrut$10, this.curDepth$18);
        if (this.scrut$10 === true) {
          this.pc = 425;
          continue contLoop;
        } else {
          this.pc = 428;
          continue contLoop;
        }
        this.pc = 419;
        continue contLoop;
      } else if (this.pc === 426) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.y$8, this.tmp$17)
      } else if (this.pc === 427) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$17 = merge(this.tmp$16, this.ys_$9);
        if (this.tmp$17 instanceof runtime.EffectSig.class) {
          this.pc = 416;
          this.tmp$17.contTrace.last.next = this;
          this.tmp$17.contTrace.last = this;
          return this.tmp$17
        }
        this.pc = 416;
        continue contLoop;
      } else if (this.pc === 428) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$16 = NofibPrelude.Cons(this.x$4, this.xs_$5);
        if (this.tmp$16 instanceof runtime.EffectSig.class) {
          this.pc = 415;
          this.tmp$16.contTrace.last.next = this;
          this.tmp$16.contTrace.last = this;
          return this.tmp$16
        }
        this.pc = 415;
        continue contLoop;
      } else if (this.pc === 415) {
        this.tmp$16 = runtime.resetDepth(this.tmp$16, this.curDepth$18);
        this.pc = 427;
        continue contLoop;
      } else if (this.pc === 416) {
        this.tmp$17 = runtime.resetDepth(this.tmp$17, this.curDepth$18);
        this.pc = 426;
        continue contLoop;
      } else if (this.pc === 423) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.x$4, this.tmp$15)
      } else if (this.pc === 424) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$15 = merge(this.xs_$5, this.tmp$14);
        if (this.tmp$15 instanceof runtime.EffectSig.class) {
          this.pc = 414;
          this.tmp$15.contTrace.last.next = this;
          this.tmp$15.contTrace.last = this;
          return this.tmp$15
        }
        this.pc = 414;
        continue contLoop;
      } else if (this.pc === 425) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$14 = NofibPrelude.Cons(this.y$8, this.ys_$9);
        if (this.tmp$14 instanceof runtime.EffectSig.class) {
          this.pc = 413;
          this.tmp$14.contTrace.last.next = this;
          this.tmp$14.contTrace.last = this;
          return this.tmp$14
        }
        this.pc = 413;
        continue contLoop;
      } else if (this.pc === 413) {
        this.tmp$14 = runtime.resetDepth(this.tmp$14, this.curDepth$18);
        this.pc = 424;
        continue contLoop;
      } else if (this.pc === 414) {
        this.tmp$15 = runtime.resetDepth(this.tmp$15, this.curDepth$18);
        this.pc = 423;
        continue contLoop;
      } else if (this.pc === 420) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return NofibPrelude.Cons(this.x$4, this.tmp$13)
      } else if (this.pc === 421) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$13 = NofibPrelude.Cons(this.y$8, this.tmp$12);
        if (this.tmp$13 instanceof runtime.EffectSig.class) {
          this.pc = 411;
          this.tmp$13.contTrace.last.next = this;
          this.tmp$13.contTrace.last = this;
          return this.tmp$13
        }
        this.pc = 411;
        continue contLoop;
      } else if (this.pc === 422) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$12 = merge(this.xs_$5, this.ys_$9);
        if (this.tmp$12 instanceof runtime.EffectSig.class) {
          this.pc = 410;
          this.tmp$12.contTrace.last.next = this;
          this.tmp$12.contTrace.last = this;
          return this.tmp$12
        }
        this.pc = 410;
        continue contLoop;
      } else if (this.pc === 410) {
        this.tmp$12 = runtime.resetDepth(this.tmp$12, this.curDepth$18);
        this.pc = 421;
        continue contLoop;
      } else if (this.pc === 411) {
        this.tmp$13 = runtime.resetDepth(this.tmp$13, this.curDepth$18);
        this.pc = 420;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$merge$sorting$_mls_L0_5477_5718$(" + globalThis.Predef.render(this.pc) + ")"; }
};
merge = function merge(xs, ys) {
  let param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, tmp6, tmp7, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$merge$sorting$_mls_L0_5477_5718$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, tmp6, tmp7, stackDelayRes, 408);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  if (xs instanceof NofibPrelude.Nil.class) {
    return ys
  } else {
    if (ys instanceof NofibPrelude.Nil.class) {
      return xs
    } else {
      if (xs instanceof NofibPrelude.Cons.class) {
        param0 = xs.head;
        param1 = xs.tail;
        x = param0;
        xs_ = param1;
        if (ys instanceof NofibPrelude.Cons.class) {
          param01 = ys.head;
          param11 = ys.tail;
          y = param01;
          ys_ = param11;
          runtime.stackDepth = runtime.stackDepth + 1;
          scrut1 = eqList(x, y);
          if (scrut1 instanceof runtime.EffectSig.class) {
            scrut1.contTrace.last.next = Cont$func$merge$sorting$_mls_L0_5477_5718$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, tmp6, tmp7, stackDelayRes, 409);
            scrut1.contTrace.last = scrut1.contTrace.last.next;
            return scrut1
          }
          scrut1 = runtime.resetDepth(scrut1, curDepth);
          if (scrut1 === true) {
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp = merge(xs_, ys_);
            if (tmp instanceof runtime.EffectSig.class) {
              tmp.contTrace.last.next = Cont$func$merge$sorting$_mls_L0_5477_5718$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, tmp6, tmp7, stackDelayRes, 410);
              tmp.contTrace.last = tmp.contTrace.last.next;
              return tmp
            }
            tmp = runtime.resetDepth(tmp, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            tmp1 = NofibPrelude.Cons(y, tmp);
            if (tmp1 instanceof runtime.EffectSig.class) {
              tmp1.contTrace.last.next = Cont$func$merge$sorting$_mls_L0_5477_5718$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, tmp6, tmp7, stackDelayRes, 411);
              tmp1.contTrace.last = tmp1.contTrace.last.next;
              return tmp1
            }
            tmp1 = runtime.resetDepth(tmp1, curDepth);
            runtime.stackDepth = runtime.stackDepth + 1;
            return NofibPrelude.Cons(x, tmp1)
          } else {
            runtime.stackDepth = runtime.stackDepth + 1;
            scrut = NofibPrelude.ltList(x, y);
            if (scrut instanceof runtime.EffectSig.class) {
              scrut.contTrace.last.next = Cont$func$merge$sorting$_mls_L0_5477_5718$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, tmp6, tmp7, stackDelayRes, 412);
              scrut.contTrace.last = scrut.contTrace.last.next;
              return scrut
            }
            scrut = runtime.resetDepth(scrut, curDepth);
            if (scrut === true) {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp2 = NofibPrelude.Cons(y, ys_);
              if (tmp2 instanceof runtime.EffectSig.class) {
                tmp2.contTrace.last.next = Cont$func$merge$sorting$_mls_L0_5477_5718$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, tmp6, tmp7, stackDelayRes, 413);
                tmp2.contTrace.last = tmp2.contTrace.last.next;
                return tmp2
              }
              tmp2 = runtime.resetDepth(tmp2, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp3 = merge(xs_, tmp2);
              if (tmp3 instanceof runtime.EffectSig.class) {
                tmp3.contTrace.last.next = Cont$func$merge$sorting$_mls_L0_5477_5718$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, tmp6, tmp7, stackDelayRes, 414);
                tmp3.contTrace.last = tmp3.contTrace.last.next;
                return tmp3
              }
              tmp3 = runtime.resetDepth(tmp3, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              return NofibPrelude.Cons(x, tmp3)
            } else {
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp4 = NofibPrelude.Cons(x, xs_);
              if (tmp4 instanceof runtime.EffectSig.class) {
                tmp4.contTrace.last.next = Cont$func$merge$sorting$_mls_L0_5477_5718$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, tmp6, tmp7, stackDelayRes, 415);
                tmp4.contTrace.last = tmp4.contTrace.last.next;
                return tmp4
              }
              tmp4 = runtime.resetDepth(tmp4, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              tmp5 = merge(tmp4, ys_);
              if (tmp5 instanceof runtime.EffectSig.class) {
                tmp5.contTrace.last.next = Cont$func$merge$sorting$_mls_L0_5477_5718$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, tmp6, tmp7, stackDelayRes, 416);
                tmp5.contTrace.last = tmp5.contTrace.last.next;
                return tmp5
              }
              tmp5 = runtime.resetDepth(tmp5, curDepth);
              runtime.stackDepth = runtime.stackDepth + 1;
              return NofibPrelude.Cons(y, tmp5)
            }
          }
        } else {
          runtime.stackDepth = runtime.stackDepth + 1;
          tmp6 = new globalThis.Error("match error");
          if (tmp6 instanceof runtime.EffectSig.class) {
            tmp6.contTrace.last.next = Cont$func$merge$sorting$_mls_L0_5477_5718$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, tmp6, tmp7, stackDelayRes, 417);
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
          tmp7.contTrace.last.next = Cont$func$merge$sorting$_mls_L0_5477_5718$$(xs, ys, param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, curDepth, tmp6, tmp7, stackDelayRes, 418);
          tmp7.contTrace.last = tmp7.contTrace.last.next;
          return tmp7
        }
        tmp7 = runtime.resetDepth(tmp7, curDepth);
        throw tmp7;
      }
    }
  }
};
mergeSort = function mergeSort(param) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$mergeSort$sorting$_mls_L0_4859_5754$$(param, tmp, curDepth, stackDelayRes, 357);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = runsplit(NofibPrelude.Nil, param);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$mergeSort$sorting$_mls_L0_4859_5754$$(param, tmp, curDepth, stackDelayRes, 431);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return merge_lists(tmp)
};
Cont$func$mangle$sorting$_mls_L0_5760_6032$$ = function Cont$func$mangle$sorting$_mls_L0_5760_6032$$(inpt$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4, pc) {
  let tmp;
  tmp = new Cont$func$mangle$sorting$_mls_L0_5760_6032$1.class(pc);
  return tmp(inpt$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
};
Cont$func$mangle$sorting$_mls_L0_5760_6032$$ctor = function Cont$func$mangle$sorting$_mls_L0_5760_6032$$ctor(inpt$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$mangle$sorting$_mls_L0_5760_6032$1.class(pc);
    return tmp(inpt$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4)
  }
};
Cont$func$mangle$sorting$_mls_L0_5760_6032$1 = function Cont$func$mangle$sorting$_mls_L0_5760_6032$(pc1) {
  return (inpt$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41) => {
    return new Cont$func$mangle$sorting$_mls_L0_5760_6032$.class(pc1)(inpt$01, tmp$11, tmp$21, curDepth$31, stackDelayRes$41);
  }
};
Cont$func$mangle$sorting$_mls_L0_5760_6032$1.class = class Cont$func$mangle$sorting$_mls_L0_5760_6032$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (inpt$0, tmp$1, tmp$2, curDepth$3, stackDelayRes$4) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.inpt$0 = inpt$0;
      this.tmp$1 = tmp$1;
      this.tmp$2 = tmp$2;
      this.curDepth$3 = curDepth$3;
      this.stackDelayRes$4 = stackDelayRes$4;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 434) {
      this.stackDelayRes$4 = value$;
    } else if (this.pc === 461) {
      this.tmp$1 = value$;
    } else if (this.pc === 462) {
      this.tmp$2 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 434) {
        this.pc = 465;
        continue contLoop;
      } else if (this.pc === 463) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return unlines(this.tmp$2)
      } else if (this.pc === 464) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = sort(this.tmp$1);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 462;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 462;
        continue contLoop;
      } else if (this.pc === 465) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = lines(this.inpt$0);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 461;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 461;
        continue contLoop;
      } else if (this.pc === 461) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$3);
        this.pc = 464;
        continue contLoop;
      } else if (this.pc === 462) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$3);
        this.pc = 463;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$mangle$sorting$_mls_L0_5760_6032$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$sort$sorting$_mls_L0_5781_6003$$ = function Cont$func$sort$sorting$_mls_L0_5781_6003$$(param$0, tmp$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12, pc) {
  let tmp;
  tmp = new Cont$func$sort$sorting$_mls_L0_5781_6003$1.class(pc);
  return tmp(param$0, tmp$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12)
};
Cont$func$sort$sorting$_mls_L0_5781_6003$$ctor = function Cont$func$sort$sorting$_mls_L0_5781_6003$$ctor(param$0, tmp$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$sort$sorting$_mls_L0_5781_6003$1.class(pc);
    return tmp(param$0, tmp$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12)
  }
};
Cont$func$sort$sorting$_mls_L0_5781_6003$1 = function Cont$func$sort$sorting$_mls_L0_5781_6003$(pc1) {
  return (param$01, tmp$11, tmp$21, tmp$31, tmp$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, curDepth$111, stackDelayRes$121) => {
    return new Cont$func$sort$sorting$_mls_L0_5781_6003$.class(pc1)(param$01, tmp$11, tmp$21, tmp$31, tmp$41, tmp$51, tmp$61, tmp$71, tmp$81, tmp$91, tmp$101, curDepth$111, stackDelayRes$121);
  }
};
Cont$func$sort$sorting$_mls_L0_5781_6003$1.class = class Cont$func$sort$sorting$_mls_L0_5781_6003$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (param$0, tmp$1, tmp$2, tmp$3, tmp$4, tmp$5, tmp$6, tmp$7, tmp$8, tmp$9, tmp$10, curDepth$11, stackDelayRes$12) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.param$0 = param$0;
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
      this.curDepth$11 = curDepth$11;
      this.stackDelayRes$12 = stackDelayRes$12;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 435) {
      this.stackDelayRes$12 = value$;
    } else if (this.pc === 436) {
      this.tmp$1 = value$;
    } else if (this.pc === 437) {
      this.tmp$2 = value$;
    } else if (this.pc === 438) {
      this.tmp$3 = value$;
    } else if (this.pc === 439) {
      this.tmp$4 = value$;
    } else if (this.pc === 440) {
      this.tmp$5 = value$;
    } else if (this.pc === 441) {
      this.tmp$6 = value$;
    } else if (this.pc === 442) {
      this.tmp$7 = value$;
    } else if (this.pc === 443) {
      this.tmp$8 = value$;
    } else if (this.pc === 444) {
      this.tmp$9 = value$;
    } else if (this.pc === 449) {
      this.tmp$10 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 435) {
        this.pc = 460;
        continue contLoop;
      } else if (this.pc === 451) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$10 = NofibPrelude.foldr(lambda5, lambda6, this.tmp$9);
        if (this.tmp$10 instanceof runtime.EffectSig.class) {
          this.pc = 449;
          this.tmp$10.contTrace.last.next = this;
          this.tmp$10.contTrace.last = this;
          return this.tmp$10
        }
        this.pc = 449;
        continue contLoop;
      } else if (this.pc === 452) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$9 = intersperse(NofibPrelude.reverse, this.tmp$8);
        if (this.tmp$9 instanceof runtime.EffectSig.class) {
          this.pc = 444;
          this.tmp$9.contTrace.last.next = this;
          this.tmp$9.contTrace.last = this;
          return this.tmp$9
        }
        this.pc = 444;
        continue contLoop;
      } else if (this.pc === 453) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$8 = NofibPrelude.Cons(heapSort, this.tmp$7);
        if (this.tmp$8 instanceof runtime.EffectSig.class) {
          this.pc = 443;
          this.tmp$8.contTrace.last.next = this;
          this.tmp$8.contTrace.last = this;
          return this.tmp$8
        }
        this.pc = 443;
        continue contLoop;
      } else if (this.pc === 454) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$7 = NofibPrelude.Cons(insertSort, this.tmp$6);
        if (this.tmp$7 instanceof runtime.EffectSig.class) {
          this.pc = 442;
          this.tmp$7.contTrace.last.next = this;
          this.tmp$7.contTrace.last = this;
          return this.tmp$7
        }
        this.pc = 442;
        continue contLoop;
      } else if (this.pc === 455) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$6 = NofibPrelude.Cons(mergeSort, this.tmp$5);
        if (this.tmp$6 instanceof runtime.EffectSig.class) {
          this.pc = 441;
          this.tmp$6.contTrace.last.next = this;
          this.tmp$6.contTrace.last = this;
          return this.tmp$6
        }
        this.pc = 441;
        continue contLoop;
      } else if (this.pc === 456) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$5 = NofibPrelude.Cons(quickSort, this.tmp$4);
        if (this.tmp$5 instanceof runtime.EffectSig.class) {
          this.pc = 440;
          this.tmp$5.contTrace.last.next = this;
          this.tmp$5.contTrace.last = this;
          return this.tmp$5
        }
        this.pc = 440;
        continue contLoop;
      } else if (this.pc === 457) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$4 = NofibPrelude.Cons(quickSort2, this.tmp$3);
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 439;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 439;
        continue contLoop;
      } else if (this.pc === 458) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = NofibPrelude.Cons(quickerSort, this.tmp$2);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 438;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 438;
        continue contLoop;
      } else if (this.pc === 459) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = NofibPrelude.Cons(treeSort, this.tmp$1);
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 437;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 437;
        continue contLoop;
      } else if (this.pc === 460) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = NofibPrelude.Cons(treeSort2, NofibPrelude.Nil);
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 436;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 436;
        continue contLoop;
      } else if (this.pc === 436) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$11);
        this.pc = 459;
        continue contLoop;
      } else if (this.pc === 437) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$11);
        this.pc = 458;
        continue contLoop;
      } else if (this.pc === 438) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$11);
        this.pc = 457;
        continue contLoop;
      } else if (this.pc === 439) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$11);
        this.pc = 456;
        continue contLoop;
      } else if (this.pc === 440) {
        this.tmp$5 = runtime.resetDepth(this.tmp$5, this.curDepth$11);
        this.pc = 455;
        continue contLoop;
      } else if (this.pc === 441) {
        this.tmp$6 = runtime.resetDepth(this.tmp$6, this.curDepth$11);
        this.pc = 454;
        continue contLoop;
      } else if (this.pc === 442) {
        this.tmp$7 = runtime.resetDepth(this.tmp$7, this.curDepth$11);
        this.pc = 453;
        continue contLoop;
      } else if (this.pc === 443) {
        this.tmp$8 = runtime.resetDepth(this.tmp$8, this.curDepth$11);
        this.pc = 452;
        continue contLoop;
      } else if (this.pc === 444) {
        this.tmp$9 = runtime.resetDepth(this.tmp$9, this.curDepth$11);
        this.pc = 451;
        continue contLoop;
      } else if (this.pc === 449) {
        this.tmp$10 = runtime.resetDepth(this.tmp$10, this.curDepth$11);
        this.pc = 450;
        continue contLoop;
      } else if (this.pc === 450) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.tmp$10(this.param$0))
      }
      break;
    }
  }
  toString() { return "Cont$func$sort$sorting$_mls_L0_5781_6003$(" + globalThis.Predef.render(this.pc) + ")"; }
};
Cont$func$lambda$$$4 = function Cont$func$lambda$$$(f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$10.class(pc);
  return tmp(f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5)
};
Cont$func$lambda$$$ctor4 = function Cont$func$lambda$$$ctor(f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$10.class(pc);
    return tmp(f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5)
  }
};
Cont$func$lambda$$10 = function Cont$func$lambda$$(pc1) {
  return (f$01, g$11, x$21, tmp$31, curDepth$41, stackDelayRes$51) => {
    return new Cont$func$lambda$$.class(pc1)(f$01, g$11, x$21, tmp$31, curDepth$41, stackDelayRes$51);
  }
};
Cont$func$lambda$$10.class = class Cont$func$lambda$$4 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, g$1, x$2, tmp$3, curDepth$4, stackDelayRes$5) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.f$0 = f$0;
      this.g$1 = g$1;
      this.x$2 = x$2;
      this.tmp$3 = tmp$3;
      this.curDepth$4 = curDepth$4;
      this.stackDelayRes$5 = stackDelayRes$5;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 445) {
      this.stackDelayRes$5 = value$;
    } else if (this.pc === 446) {
      this.tmp$3 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 445) {
        this.pc = 448;
        continue contLoop;
      } else if (this.pc === 447) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return runtime.safeCall(this.f$0(this.tmp$3))
      } else if (this.pc === 448) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = runtime.safeCall(this.g$1(this.x$2));
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 446;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 446;
        continue contLoop;
      } else if (this.pc === 446) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$4);
        this.pc = 447;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda$2 = function lambda$(f, g, x) {
  let tmp, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$4(f, g, x, tmp, curDepth, stackDelayRes, 445);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = runtime.safeCall(g(x));
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$lambda$$$4(f, g, x, tmp, curDepth, stackDelayRes, 446);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return runtime.safeCall(f(tmp))
};
lambda7 = (undefined, function (f, g) {
  return (x) => {
    return lambda$2(f, g, x)
  }
});
lambda5 = (undefined, function (f, g) {
  return runtime.safeCall(lambda7(f, g))
});
lambda6 = (undefined, function (x) {
  return x
});
sort = function sort(param) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$sort$sorting$_mls_L0_5781_6003$$(param, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 435);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = NofibPrelude.Cons(treeSort2, NofibPrelude.Nil);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$sort$sorting$_mls_L0_5781_6003$$(param, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 436);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = NofibPrelude.Cons(treeSort, tmp);
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$sort$sorting$_mls_L0_5781_6003$$(param, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 437);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp2 = NofibPrelude.Cons(quickerSort, tmp1);
  if (tmp2 instanceof runtime.EffectSig.class) {
    tmp2.contTrace.last.next = Cont$func$sort$sorting$_mls_L0_5781_6003$$(param, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 438);
    tmp2.contTrace.last = tmp2.contTrace.last.next;
    return tmp2
  }
  tmp2 = runtime.resetDepth(tmp2, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp3 = NofibPrelude.Cons(quickSort2, tmp2);
  if (tmp3 instanceof runtime.EffectSig.class) {
    tmp3.contTrace.last.next = Cont$func$sort$sorting$_mls_L0_5781_6003$$(param, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 439);
    tmp3.contTrace.last = tmp3.contTrace.last.next;
    return tmp3
  }
  tmp3 = runtime.resetDepth(tmp3, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp4 = NofibPrelude.Cons(quickSort, tmp3);
  if (tmp4 instanceof runtime.EffectSig.class) {
    tmp4.contTrace.last.next = Cont$func$sort$sorting$_mls_L0_5781_6003$$(param, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 440);
    tmp4.contTrace.last = tmp4.contTrace.last.next;
    return tmp4
  }
  tmp4 = runtime.resetDepth(tmp4, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp5 = NofibPrelude.Cons(mergeSort, tmp4);
  if (tmp5 instanceof runtime.EffectSig.class) {
    tmp5.contTrace.last.next = Cont$func$sort$sorting$_mls_L0_5781_6003$$(param, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 441);
    tmp5.contTrace.last = tmp5.contTrace.last.next;
    return tmp5
  }
  tmp5 = runtime.resetDepth(tmp5, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp6 = NofibPrelude.Cons(insertSort, tmp5);
  if (tmp6 instanceof runtime.EffectSig.class) {
    tmp6.contTrace.last.next = Cont$func$sort$sorting$_mls_L0_5781_6003$$(param, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 442);
    tmp6.contTrace.last = tmp6.contTrace.last.next;
    return tmp6
  }
  tmp6 = runtime.resetDepth(tmp6, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp7 = NofibPrelude.Cons(heapSort, tmp6);
  if (tmp7 instanceof runtime.EffectSig.class) {
    tmp7.contTrace.last.next = Cont$func$sort$sorting$_mls_L0_5781_6003$$(param, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 443);
    tmp7.contTrace.last = tmp7.contTrace.last.next;
    return tmp7
  }
  tmp7 = runtime.resetDepth(tmp7, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp8 = intersperse(NofibPrelude.reverse, tmp7);
  if (tmp8 instanceof runtime.EffectSig.class) {
    tmp8.contTrace.last.next = Cont$func$sort$sorting$_mls_L0_5781_6003$$(param, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 444);
    tmp8.contTrace.last = tmp8.contTrace.last.next;
    return tmp8
  }
  tmp8 = runtime.resetDepth(tmp8, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp9 = NofibPrelude.foldr(lambda5, lambda6, tmp8);
  if (tmp9 instanceof runtime.EffectSig.class) {
    tmp9.contTrace.last.next = Cont$func$sort$sorting$_mls_L0_5781_6003$$(param, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, curDepth, stackDelayRes, 449);
    tmp9.contTrace.last = tmp9.contTrace.last.next;
    return tmp9
  }
  tmp9 = runtime.resetDepth(tmp9, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return runtime.safeCall(tmp9(param))
};
mangle = function mangle(inpt) {
  let tmp, tmp1, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$mangle$sorting$_mls_L0_5760_6032$$(inpt, tmp, tmp1, curDepth, stackDelayRes, 434);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = lines(inpt);
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$mangle$sorting$_mls_L0_5760_6032$$(inpt, tmp, tmp1, curDepth, stackDelayRes, 461);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = sort(tmp);
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$mangle$sorting$_mls_L0_5760_6032$$(inpt, tmp, tmp1, curDepth, stackDelayRes, 462);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return unlines(tmp1)
};
Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$$ = function Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$$(f$0, tmp$1, tmp$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6, pc) {
  let tmp;
  tmp = new Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$1.class(pc);
  return tmp(f$0, tmp$1, tmp$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6)
};
Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$$ctor = function Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$$ctor(f$0, tmp$1, tmp$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$1.class(pc);
    return tmp(f$0, tmp$1, tmp$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6)
  }
};
Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$1 = function Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$(pc1) {
  return (f$01, tmp$11, tmp$21, tmp$31, tmp$41, curDepth$51, stackDelayRes$61) => {
    return new Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$.class(pc1)(f$01, tmp$11, tmp$21, tmp$31, tmp$41, curDepth$51, stackDelayRes$61);
  }
};
Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$1.class = class Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$ extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (f$0, tmp$1, tmp$2, tmp$3, tmp$4, curDepth$5, stackDelayRes$6) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.f$0 = f$0;
      this.tmp$1 = tmp$1;
      this.tmp$2 = tmp$2;
      this.tmp$3 = tmp$3;
      this.tmp$4 = tmp$4;
      this.curDepth$5 = curDepth$5;
      this.stackDelayRes$6 = stackDelayRes$6;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 466) {
      this.stackDelayRes$6 = value$;
    } else if (this.pc === 467) {
      this.tmp$1 = value$;
    } else if (this.pc === 468) {
      this.tmp$2 = value$;
    } else if (this.pc === 469) {
      this.tmp$3 = value$;
    } else if (this.pc === 470) {
      this.tmp$4 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 466) {
        this.pc = 475;
        continue contLoop;
      } else if (this.pc === 473) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$3 = NofibPrelude.nofibStringToList(this.tmp$2);
        if (this.tmp$3 instanceof runtime.EffectSig.class) {
          this.pc = 469;
          this.tmp$3.contTrace.last.next = this;
          this.tmp$3.contTrace.last = this;
          return this.tmp$3
        }
        this.pc = 469;
        continue contLoop;
      } else if (this.pc === 475) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$1 = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/Main.hs"));
        if (this.tmp$1 instanceof runtime.EffectSig.class) {
          this.pc = 467;
          this.tmp$1.contTrace.last.next = this;
          this.tmp$1.contTrace.last = this;
          return this.tmp$1
        }
        this.pc = 467;
        continue contLoop;
      } else if (this.pc === 467) {
        this.tmp$1 = runtime.resetDepth(this.tmp$1, this.curDepth$5);
        this.pc = 474;
        continue contLoop;
      } else if (this.pc === 474) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$2 = runtime.safeCall(this.tmp$1.toString());
        if (this.tmp$2 instanceof runtime.EffectSig.class) {
          this.pc = 468;
          this.tmp$2.contTrace.last.next = this;
          this.tmp$2.contTrace.last = this;
          return this.tmp$2
        }
        this.pc = 468;
        continue contLoop;
      } else if (this.pc === 468) {
        this.tmp$2 = runtime.resetDepth(this.tmp$2, this.curDepth$5);
        this.pc = 473;
        continue contLoop;
      } else if (this.pc === 469) {
        this.tmp$3 = runtime.resetDepth(this.tmp$3, this.curDepth$5);
        this.f$0 = this.tmp$3;
        this.pc = 472;
        continue contLoop;
      } else if (this.pc === 471) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return hash(this.tmp$4)
      } else if (this.pc === 472) {
        runtime.stackDepth = runtime.stackDepth + 1;
        this.tmp$4 = mangle(this.f$0);
        if (this.tmp$4 instanceof runtime.EffectSig.class) {
          this.pc = 470;
          this.tmp$4.contTrace.last.next = this;
          this.tmp$4.contTrace.last = this;
          return this.tmp$4
        }
        this.pc = 470;
        continue contLoop;
      } else if (this.pc === 470) {
        this.tmp$4 = runtime.resetDepth(this.tmp$4, this.curDepth$5);
        this.pc = 471;
        continue contLoop;
      }
      break;
    }
  }
  toString() { return "Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$(" + globalThis.Predef.render(this.pc) + ")"; }
};
testSorting_nofib = function testSorting_nofib(d) {
  let f, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes;
  curDepth = runtime.stackDepth;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$$(f, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 466);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/Main.hs"));
  if (tmp instanceof runtime.EffectSig.class) {
    tmp.contTrace.last.next = Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$$(f, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 467);
    tmp.contTrace.last = tmp.contTrace.last.next;
    return tmp
  }
  tmp = runtime.resetDepth(tmp, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp1 = runtime.safeCall(tmp.toString());
  if (tmp1 instanceof runtime.EffectSig.class) {
    tmp1.contTrace.last.next = Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$$(f, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 468);
    tmp1.contTrace.last = tmp1.contTrace.last.next;
    return tmp1
  }
  tmp1 = runtime.resetDepth(tmp1, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp2 = NofibPrelude.nofibStringToList(tmp1);
  if (tmp2 instanceof runtime.EffectSig.class) {
    tmp2.contTrace.last.next = Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$$(f, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 469);
    tmp2.contTrace.last = tmp2.contTrace.last.next;
    return tmp2
  }
  tmp2 = runtime.resetDepth(tmp2, curDepth);
  f = tmp2;
  runtime.stackDepth = runtime.stackDepth + 1;
  tmp3 = mangle(f);
  if (tmp3 instanceof runtime.EffectSig.class) {
    tmp3.contTrace.last.next = Cont$func$testSorting_nofib$sorting$_mls_L0_6038_6190$$(f, tmp, tmp1, tmp2, tmp3, curDepth, stackDelayRes, 470);
    tmp3.contTrace.last = tmp3.contTrace.last.next;
    return tmp3
  }
  tmp3 = runtime.resetDepth(tmp3, curDepth);
  runtime.stackDepth = runtime.stackDepth + 1;
  return hash(tmp3)
};
const EQ$class = class EQ {
  constructor() {}
  toString() { return "EQ"; }
}; EQ1 = new EQ$class;
EQ1.class = EQ$class;
const GT$class = class GT {
  constructor() {}
  toString() { return "GT"; }
}; GT1 = new GT$class;
GT1.class = GT$class;
const LT$class = class LT {
  constructor() {}
  toString() { return "LT"; }
}; LT1 = new LT$class;
LT1.class = LT$class;
Tree1 = class Tree {
  constructor() {}
  toString() { return "Tree"; }
};
const Tip$class = class Tip extends Tree1 {
  constructor() {
    super();
  }
  toString() { return "Tip"; }
}; Tip1 = new Tip$class;
Tip1.class = Tip$class;
Branch1 = function Branch(a1, l1, r1) {
  return new Branch.class(a1, l1, r1);
};
Branch1.class = class Branch extends Tree1 {
  constructor(a, l, r) {
    super();
    this.a = a;
    this.l = l;
    this.r = r;
  }
  toString() { return "Branch(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.l) + ", " + globalThis.Predef.render(this.r) + ")"; }
};
Tree21 = class Tree2 {
  constructor() {}
  toString() { return "Tree2"; }
};
const Tip2$class = class Tip2 extends Tree21 {
  constructor() {
    super();
  }
  toString() { return "Tip2"; }
}; Tip21 = new Tip2$class;
Tip21.class = Tip2$class;
Twig21 = function Twig2(a1) {
  return new Twig2.class(a1);
};
Twig21.class = class Twig2 extends Tree21 {
  constructor(a) {
    super();
    this.a = a;
  }
  toString() { return "Twig2(" + globalThis.Predef.render(this.a) + ")"; }
};
Branch21 = function Branch2(a1, l1, r1) {
  return new Branch2.class(a1, l1, r1);
};
Branch21.class = class Branch2 extends Tree21 {
  constructor(a, l, r) {
    super();
    this.a = a;
    this.l = l;
    this.r = r;
  }
  toString() { return "Branch2(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.l) + ", " + globalThis.Predef.render(this.r) + ")"; }
};
Cont$func$lambda$$$5 = function Cont$func$lambda$$$(stackDelayRes$0, pc) {
  let tmp;
  tmp = new Cont$func$lambda$$11.class(pc);
  return tmp(stackDelayRes$0)
};
Cont$func$lambda$$$ctor5 = function Cont$func$lambda$$$ctor(stackDelayRes$0) {
  return (pc) => {
    let tmp;
    tmp = new Cont$func$lambda$$11.class(pc);
    return tmp(stackDelayRes$0)
  }
};
Cont$func$lambda$$11 = function Cont$func$lambda$$(pc1) {
  return (stackDelayRes$01) => {
    return new Cont$func$lambda$$.class(pc1)(stackDelayRes$01);
  }
};
Cont$func$lambda$$11.class = class Cont$func$lambda$$5 extends runtime.FunctionContFrame.class {
  constructor(pc) {
    return (stackDelayRes$0) => {
      let tmp;
      tmp = super(null);
      this.pc = pc;
      this.stackDelayRes$0 = stackDelayRes$0;
      return this;
    }
  }
  resume(value$) {
    if (this.pc === 476) {
      this.stackDelayRes$0 = value$;
    }
    contLoop: while (true) {
      if (this.pc === 476) {
        this.pc = 477;
        continue contLoop;
      } else if (this.pc === 477) {
        runtime.stackDepth = runtime.stackDepth + 1;
        return testSorting_nofib(0)
      }
      break;
    }
  }
  toString() { return "Cont$func$lambda$$(" + globalThis.Predef.render(this.pc) + ")"; }
};
lambda8 = (undefined, function () {
  let stackDelayRes;
  stackDelayRes = runtime.checkDepth();
  if (stackDelayRes instanceof runtime.EffectSig.class) {
    stackDelayRes.contTrace.last.next = Cont$func$lambda$$$5(stackDelayRes, 476);
    stackDelayRes.contTrace.last = stackDelayRes.contTrace.last.next;
    return stackDelayRes
  }
  runtime.stackDepth = runtime.stackDepth + 1;
  return testSorting_nofib(0)
});
lambda9 = (undefined, function () {
  return BenchmarkPrelude.benchmark(lambda8)
});
res = runtime.runStackSafe(500, lambda9);
if (res instanceof runtime.EffectSig.class) {
  throw new this.Error("Unhandled effects");
}
res