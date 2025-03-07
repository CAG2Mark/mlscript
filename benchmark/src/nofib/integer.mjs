import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let testInteger_nofib, intbench, runalltests, integerbench, runbench, lambda;
integerbench = function integerbench(op, astart, astep, alim, bstart, bstep, blim) {
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
};
intbench = function intbench(op, astart, astep, alim, bstart, bstep, blim) {
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
};
runbench = function runbench(jop, iop, opstr, astart, astep, alim, bstart, bstep, blim) {
  let tmp, tmp1;
  tmp = intbench(iop, astart, astep, alim, astart, astep, alim);
  tmp1 = integerbench(jop, astart, astep, alim, astart, astep, alim);
  return (tmp , tmp1)
};
runalltests = function runalltests(astart, astep, alim, bstart, bstep, blim) {
  let z_lt, z_add, z_leq, z_mod, z_gt, z_geq, z_mul, z_equal, z_sub, z_div, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda14, lambda15, lambda16, lambda17, lambda18, lambda19, lambda20;
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
  lambda1 = (undefined, function (a, b) {
    return z_add(a, b)
  });
  lambda2 = (undefined, function (a, b) {
    return a + b
  });
  tmp = runbench(lambda1, lambda2, "(+)", astart, astep, alim, astart, astep, alim);
  lambda3 = (undefined, function (a, b) {
    return z_sub(a, b)
  });
  lambda4 = (undefined, function (a, b) {
    return a - b
  });
  tmp1 = runbench(lambda3, lambda4, "(-)", astart, astep, alim, astart, astep, alim);
  tmp2 = (tmp , tmp1);
  lambda5 = (undefined, function (a, b) {
    return z_mul(a, b)
  });
  lambda6 = (undefined, function (a, b) {
    return a * b
  });
  tmp3 = runbench(lambda5, lambda6, "(*)", astart, astep, alim, astart, astep, alim);
  tmp4 = (tmp2 , tmp3);
  lambda7 = (undefined, function (a, b) {
    return z_div(a, b)
  });
  lambda8 = (undefined, function (a, b) {
    return NofibPrelude.intDiv(a, b)
  });
  tmp5 = runbench(lambda7, lambda8, "div", astart, astep, alim, astart, astep, alim);
  tmp6 = (tmp4 , tmp5);
  lambda9 = (undefined, function (a, b) {
    return z_mod(a, b)
  });
  lambda10 = (undefined, function (a, b) {
    return NofibPrelude.intMod(a, b)
  });
  tmp7 = runbench(lambda9, lambda10, "mod", astart, astep, alim, astart, astep, alim);
  tmp8 = (tmp6 , tmp7);
  lambda11 = (undefined, function (a, b) {
    return z_equal(a, b)
  });
  lambda12 = (undefined, function (a, b) {
    return a == b
  });
  tmp9 = runbench(lambda11, lambda12, "(==)", astart, astep, alim, astart, astep, alim);
  tmp10 = (tmp8 , tmp9);
  lambda13 = (undefined, function (a, b) {
    return z_lt(a, b)
  });
  lambda14 = (undefined, function (a, b) {
    return a < b
  });
  tmp11 = runbench(lambda13, lambda14, "(<)", astart, astep, alim, astart, astep, alim);
  tmp12 = (tmp10 , tmp11);
  lambda15 = (undefined, function (a, b) {
    return z_leq(a, b)
  });
  lambda16 = (undefined, function (a, b) {
    return a <= b
  });
  tmp13 = runbench(lambda15, lambda16, "(<=)", astart, astep, alim, astart, astep, alim);
  tmp14 = (tmp12 , tmp13);
  lambda17 = (undefined, function (a, b) {
    return z_gt(a, b)
  });
  lambda18 = (undefined, function (a, b) {
    return a > b
  });
  tmp15 = runbench(lambda17, lambda18, "(>)", astart, astep, alim, astart, astep, alim);
  tmp16 = (tmp14 , tmp15);
  lambda19 = (undefined, function (a, b) {
    return z_geq(a, b)
  });
  lambda20 = (undefined, function (a, b) {
    return a >= b
  });
  tmp17 = runbench(lambda19, lambda20, "(>=)", astart, astep, alim, astart, astep, alim);
  return (tmp16 , tmp17)
};
testInteger_nofib = function testInteger_nofib(n) {
  let tmp, tmp1, tmp2;
  tmp = - 2100000000;
  tmp1 = - 2100000000;
  tmp2 = - 2100000000;
  return runalltests(tmp, n, 2100000000, tmp1, n, tmp2)
};
lambda = (undefined, function () {
  let tmp;
  tmp = testInteger_nofib(700000001);
  return runtime.safeCall(tmp.toString())
});
BenchmarkPrelude.benchmark(lambda)