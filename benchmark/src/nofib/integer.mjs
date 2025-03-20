import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let integer1;
integer1 = class integer {
  static {
    let lambda;
    lambda = (undefined, function () {
      let tmp;
      tmp = integer.testInteger_nofib(700000001);
      return runtime.safeCall(tmp.toString())
    });
    BenchmarkPrelude.benchmark(lambda)
  }
  static integerbench(op, astart, astep, alim, bstart, bstep, blim) {
    let lscomp1, tmp, tmp1;
    lscomp1 = function lscomp1(ls) {
      let lscomp2, param0, param1, a, t1, tmp2, tmp3;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        a = param0;
        t1 = param1;
        lscomp2 = function lscomp2(ls1) {
          let param01, param11, b, t2, tmp4, tmp5;
          if (ls1 instanceof NofibPrelude.Nil.class) {
            return lscomp1(t1)
          } else if (ls1 instanceof NofibPrelude.Cons.class) {
            param01 = ls1.head;
            param11 = ls1.tail;
            b = param01;
            t2 = param11;
            tmp4 = runtime.safeCall(op(a, b));
            tmp5 = lscomp2(t2);
            return NofibPrelude.Cons(tmp4, tmp5)
          } else {
            throw new globalThis.Error("match error");
          }
        };
        tmp2 = bstart + bstep;
        tmp3 = NofibPrelude.enumFromThenTo(bstart, tmp2, blim);
        return lscomp2(tmp3)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = astart + astep;
    tmp1 = NofibPrelude.enumFromThenTo(astart, tmp, alim);
    return lscomp1(tmp1)
  } 
  static intbench(op1, astart1, astep1, alim1, bstart1, bstep1, blim1) {
    let lscomp1, tmp, tmp1;
    lscomp1 = function lscomp1(ls) {
      let lscomp2, param0, param1, a, t1, tmp2, tmp3;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        a = param0;
        t1 = param1;
        lscomp2 = function lscomp2(ls1) {
          let param01, param11, b, t2, tmp4, tmp5;
          if (ls1 instanceof NofibPrelude.Nil.class) {
            return lscomp1(t1)
          } else if (ls1 instanceof NofibPrelude.Cons.class) {
            param01 = ls1.head;
            param11 = ls1.tail;
            b = param01;
            t2 = param11;
            tmp4 = runtime.safeCall(op1(a, b));
            tmp5 = lscomp2(t2);
            return NofibPrelude.Cons(tmp4, tmp5)
          } else {
            throw new globalThis.Error("match error");
          }
        };
        tmp2 = bstart1 + bstep1;
        tmp3 = NofibPrelude.enumFromThenTo(bstart1, tmp2, blim1);
        return lscomp2(tmp3)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = astart1 + astep1;
    tmp1 = NofibPrelude.enumFromThenTo(astart1, tmp, alim1);
    return lscomp1(tmp1)
  } 
  static runbench(jop, iop, opstr, astart2, astep2, alim2, bstart2, bstep2, blim2) {
    let tmp, tmp1;
    tmp = integer.intbench(iop, astart2, astep2, alim2, astart2, astep2, alim2);
    tmp1 = integer.integerbench(jop, astart2, astep2, alim2, astart2, astep2, alim2);
    return (tmp , tmp1)
  } 
  static runalltests(astart3, astep3, alim3, bstart3, bstep3, blim3) {
    let z_lt, z_add, z_leq, z_mod, z_gt, z_geq, z_mul, z_equal, z_sub, z_div, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda14, lambda15, lambda16, lambda17, lambda18, lambda19;
    z_add = function z_add(a, b) {
      return a + b
    };
    z_sub = function z_sub(a, b) {
      return a - b
    };
    z_mul = function z_mul(a, b) {
      return a * b
    };
    z_div = function z_div(a, b) {
      return NofibPrelude.intDiv(a, b)
    };
    z_mod = function z_mod(a, b) {
      return NofibPrelude.intMod(a, b)
    };
    z_equal = function z_equal(a, b) {
      return a == b
    };
    z_lt = function z_lt(a, b) {
      return a < b
    };
    z_leq = function z_leq(a, b) {
      return a <= b
    };
    z_gt = function z_gt(a, b) {
      return a > b
    };
    z_geq = function z_geq(a, b) {
      return a >= b
    };
    lambda = (undefined, function (a, b) {
      return z_add(a, b)
    });
    lambda1 = (undefined, function (a, b) {
      return a + b
    });
    tmp = integer.runbench(lambda, lambda1, "(+)", astart3, astep3, alim3, astart3, astep3, alim3);
    lambda2 = (undefined, function (a, b) {
      return z_sub(a, b)
    });
    lambda3 = (undefined, function (a, b) {
      return a - b
    });
    tmp1 = integer.runbench(lambda2, lambda3, "(-)", astart3, astep3, alim3, astart3, astep3, alim3);
    tmp2 = (tmp , tmp1);
    lambda4 = (undefined, function (a, b) {
      return z_mul(a, b)
    });
    lambda5 = (undefined, function (a, b) {
      return a * b
    });
    tmp3 = integer.runbench(lambda4, lambda5, "(*)", astart3, astep3, alim3, astart3, astep3, alim3);
    tmp4 = (tmp2 , tmp3);
    lambda6 = (undefined, function (a, b) {
      return z_div(a, b)
    });
    lambda7 = (undefined, function (a, b) {
      return NofibPrelude.intDiv(a, b)
    });
    tmp5 = integer.runbench(lambda6, lambda7, "div", astart3, astep3, alim3, astart3, astep3, alim3);
    tmp6 = (tmp4 , tmp5);
    lambda8 = (undefined, function (a, b) {
      return z_mod(a, b)
    });
    lambda9 = (undefined, function (a, b) {
      return NofibPrelude.intMod(a, b)
    });
    tmp7 = integer.runbench(lambda8, lambda9, "mod", astart3, astep3, alim3, astart3, astep3, alim3);
    tmp8 = (tmp6 , tmp7);
    lambda10 = (undefined, function (a, b) {
      return z_equal(a, b)
    });
    lambda11 = (undefined, function (a, b) {
      return a == b
    });
    tmp9 = integer.runbench(lambda10, lambda11, "(==)", astart3, astep3, alim3, astart3, astep3, alim3);
    tmp10 = (tmp8 , tmp9);
    lambda12 = (undefined, function (a, b) {
      return z_lt(a, b)
    });
    lambda13 = (undefined, function (a, b) {
      return a < b
    });
    tmp11 = integer.runbench(lambda12, lambda13, "(<)", astart3, astep3, alim3, astart3, astep3, alim3);
    tmp12 = (tmp10 , tmp11);
    lambda14 = (undefined, function (a, b) {
      return z_leq(a, b)
    });
    lambda15 = (undefined, function (a, b) {
      return a <= b
    });
    tmp13 = integer.runbench(lambda14, lambda15, "(<=)", astart3, astep3, alim3, astart3, astep3, alim3);
    tmp14 = (tmp12 , tmp13);
    lambda16 = (undefined, function (a, b) {
      return z_gt(a, b)
    });
    lambda17 = (undefined, function (a, b) {
      return a > b
    });
    tmp15 = integer.runbench(lambda16, lambda17, "(>)", astart3, astep3, alim3, astart3, astep3, alim3);
    tmp16 = (tmp14 , tmp15);
    lambda18 = (undefined, function (a, b) {
      return z_geq(a, b)
    });
    lambda19 = (undefined, function (a, b) {
      return a >= b
    });
    tmp17 = integer.runbench(lambda18, lambda19, "(>=)", astart3, astep3, alim3, astart3, astep3, alim3);
    return (tmp16 , tmp17)
  } 
  static testInteger_nofib(n) {
    let tmp, tmp1, tmp2;
    tmp = - 2100000000;
    tmp1 = - 2100000000;
    tmp2 = - 2100000000;
    return integer.runalltests(tmp, n, 2100000000, tmp1, n, tmp2)
  }
  static toString() { return "integer"; }
};
let integer = integer1; export default integer;
