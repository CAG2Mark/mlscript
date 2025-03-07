import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let lcss_, algc, findk, algb, testLCSS_nofib, algb2, algb1, lcssMain, lambda;
algb2 = function algb2(x, k0j1, k1j1, yss) {
  let param0, param1, first1, first0, y, k0j, ys, kjcurr, scrut, tmp, tmp1;
  if (yss instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (yss instanceof NofibPrelude.Cons.class) {
    param0 = yss.head;
    param1 = yss.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      y = first0;
      k0j = first1;
      ys = param1;
      scrut = x == y;
      if (scrut === true) {
        tmp = k0j1 + 1;
      } else {
        tmp = NofibPrelude.max(k1j1, k0j);
      }
      kjcurr = tmp;
      tmp1 = algb2(x, k0j, kjcurr, ys);
      return NofibPrelude.Cons([
        y,
        kjcurr
      ], tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
algb1 = function algb1(xss, yss) {
  let param0, param1, x, xs, tmp;
  if (xss instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.map(NofibPrelude.snd, yss)
  } else if (xss instanceof NofibPrelude.Cons.class) {
    param0 = xss.head;
    param1 = xss.tail;
    x = param0;
    xs = param1;
    tmp = algb2(x, 0, 0, yss);
    return algb1(xs, tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
algb = function algb(xs, ys) {
  let listcomp_fun, tmp, tmp1;
  listcomp_fun = function listcomp_fun(listcomp_fun_para) {
    let param0, param1, listcomp_fun_ls_h, listcomp_fun_ls_t, tmp2;
    if (listcomp_fun_para instanceof NofibPrelude.Cons.class) {
      param0 = listcomp_fun_para.head;
      param1 = listcomp_fun_para.tail;
      listcomp_fun_ls_h = param0;
      listcomp_fun_ls_t = param1;
      tmp2 = listcomp_fun(listcomp_fun_ls_t);
      return NofibPrelude.Cons([
        listcomp_fun_ls_h,
        0
      ], tmp2)
    } else if (listcomp_fun_para instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp = listcomp_fun(ys);
  tmp1 = algb1(xs, tmp);
  return NofibPrelude.Cons(0, tmp1)
};
findk = function findk(k, km, m, ls) {
  let param0, param1, first1, first0, x, y, xys, scrut, tmp, tmp1, tmp2, tmp3;
  if (ls instanceof NofibPrelude.Nil.class) {
    return km
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      x = first0;
      y = first1;
      xys = param1;
      tmp = x + y;
      scrut = tmp >= m;
      if (scrut === true) {
        tmp1 = k + 1;
        tmp2 = x + y;
        return findk(tmp1, k, tmp2, xys)
      } else {
        tmp3 = k + 1;
        return findk(tmp3, km, m, xys)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
algc = function algc(m, n, xs, ys) {
  let m2, xs1, xs2, l1, l2, k, param0, param1, x, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, lambda1, lambda2, lambda3;
  if (ys instanceof NofibPrelude.Nil.class) {
    lambda1 = (undefined, function (x1) {
      return x1
    });
    return lambda1
  } else {
    if (xs instanceof NofibPrelude.Cons.class) {
      param0 = xs.head;
      param1 = xs.tail;
      x = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        scrut = NofibPrelude.inList(x, ys);
        if (scrut === true) {
          lambda2 = (undefined, function (t) {
            return NofibPrelude.Cons(x, t)
          });
          return lambda2
        } else {
          lambda3 = (undefined, function (x1) {
            return x1
          });
          return lambda3
        }
      } else {
        tmp = NofibPrelude.intDiv(m, 2);
        m2 = tmp;
        tmp1 = NofibPrelude.take(m2, xs);
        xs1 = tmp1;
        tmp2 = NofibPrelude.drop(m2, xs);
        xs2 = tmp2;
        tmp3 = algb(xs1, ys);
        l1 = tmp3;
        tmp4 = NofibPrelude.reverse(xs2);
        tmp5 = NofibPrelude.reverse(ys);
        tmp6 = algb(tmp4, tmp5);
        tmp7 = NofibPrelude.reverse(tmp6);
        l2 = tmp7;
        tmp8 = - 1;
        tmp9 = NofibPrelude.zip(l1, l2);
        tmp10 = findk(0, 0, tmp8, tmp9);
        k = tmp10;
        tmp11 = NofibPrelude.take(k, ys);
        tmp12 = algc(m2, k, xs1, tmp11);
        tmp13 = m - m2;
        tmp14 = n - k;
        tmp15 = NofibPrelude.drop(k, ys);
        tmp16 = algc(tmp13, tmp14, xs2, tmp15);
        return NofibPrelude.compose(tmp12, tmp16)
      }
    } else {
      tmp17 = NofibPrelude.intDiv(m, 2);
      m2 = tmp17;
      tmp18 = NofibPrelude.take(m2, xs);
      xs1 = tmp18;
      tmp19 = NofibPrelude.drop(m2, xs);
      xs2 = tmp19;
      tmp20 = algb(xs1, ys);
      l1 = tmp20;
      tmp21 = NofibPrelude.reverse(xs2);
      tmp22 = NofibPrelude.reverse(ys);
      tmp23 = algb(tmp21, tmp22);
      tmp24 = NofibPrelude.reverse(tmp23);
      l2 = tmp24;
      tmp25 = - 1;
      tmp26 = NofibPrelude.zip(l1, l2);
      tmp27 = findk(0, 0, tmp25, tmp26);
      k = tmp27;
      tmp28 = NofibPrelude.take(k, ys);
      tmp29 = algc(m2, k, xs1, tmp28);
      tmp30 = m - m2;
      tmp31 = n - k;
      tmp32 = NofibPrelude.drop(k, ys);
      tmp33 = algc(tmp30, tmp31, xs2, tmp32);
      return NofibPrelude.compose(tmp29, tmp33)
    }
  }
};
lcss_ = function lcss_(xs, ys) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.listLen(xs);
  tmp1 = NofibPrelude.listLen(ys);
  tmp2 = algc(tmp, tmp1, xs, ys);
  return runtime.safeCall(tmp2(NofibPrelude.Nil))
};
lcssMain = function lcssMain(a, b, c, d, e, f) {
  let tmp, tmp1;
  tmp = NofibPrelude.enumFromThenTo(a, b, c);
  tmp1 = NofibPrelude.enumFromThenTo(d, e, f);
  return lcss_(tmp, tmp1)
};
testLCSS_nofib = function testLCSS_nofib(d) {
  return lcssMain(1, 2, 60, 30, 31, 90)
};
lambda = (undefined, function () {
  let tmp;
  tmp = testLCSS_nofib(0);
  return runtime.safeCall(tmp.toString())
});
BenchmarkPrelude.benchmark(lambda)