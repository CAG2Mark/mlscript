import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let rs, deriv1, int1, int11, qs, power1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda14, lambda15, lambda16, lambda17, lambda18, lambda19, lambda20, lambda21, lambda22, lambda23, lambda24, lambda25, lambda26, lambda27, lambda28, lambda29, lambda30, lambda31, lambda32, lambda33, lambda34, lambda35, lambda36, lambda37, lambda38, lambda39, lambda40, lambda41, lambda42, lambda43, lambda44, lambda45, lambda46, lambda47, lambda48, lambda49, lambda50, lambda51, lambda$, lambda$1, lambda$2, lambda$3, lambda$4, lambda$5, lambda$6, lambda$7, lambda$8, lambda$9, lambda$10, lambda$11, lambda$12, lambda$13, lambda$14, lambda$15, lambda$16, lambda$17, lambda$18, lambda$19, lambda$20, rs$, lambda$21, lambda$22, lambda$23, lambda$24, lambda$25, lambda$26, lambda$27, lambda$28, qs$, lambda$29, lambda$30;
lambda51 = (undefined, function () {
  return power1.Pz
});
lambda50 = (undefined, function () {
  let tmp;
  tmp = NofibPrelude.lazy(lambda51);
  return power1.Pc(1, tmp)
});
lambda49 = (undefined, function () {
  return power1.Pz
});
lambda48 = (undefined, function () {
  let tmp;
  tmp = NofibPrelude.lazy(lambda49);
  return power1.Pc(1, tmp)
});
lambda47 = (undefined, function () {
  return power1.tree()
});
lambda46 = (undefined, function () {
  let tmp, tmp1, tmp2;
  tmp = power1.list();
  tmp1 = NofibPrelude.lazy(lambda47);
  tmp2 = power1.composeSndLz_(tmp, tmp1);
  return power1.Pc(0, tmp2)
});
lambda45 = (undefined, function () {
  let tmp, tmp1, tmp2;
  tmp = power1.ts();
  tmp1 = power1.ts();
  tmp2 = power1.multPs(tmp, tmp1);
  return power1.Pc(1, tmp2)
});
lambda$30 = function lambda$(fs_) {
  return power1.Pc(1, fs_)
};
lambda44 = (undefined, function (fs_) {
  return () => {
    return lambda$30(fs_)
  }
});
lambda$29 = function lambda$(fs_) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, lambda$this;
  tmp = power1.fromIntegerPs(1);
  lambda$this = runtime.safeCall(lambda44(fs_));
  tmp1 = NofibPrelude.lazy(lambda$this);
  tmp2 = power1.deriv(tmp1);
  tmp3 = qs$(fs_);
  tmp4 = power1.dotMultSndLz(2, tmp3);
  tmp5 = power1.divPs(tmp2, tmp4);
  tmp6 = power1.integral(tmp5);
  return power1.addPs(tmp, tmp6)
};
lambda43 = (undefined, function (fs_) {
  return () => {
    return lambda$29(fs_)
  }
});
qs$ = function qs$(fs_) {
  let tmp;
  tmp = runtime.safeCall(lambda43(fs_));
  return NofibPrelude.lazy(tmp)
};
qs = function qs(fs_) {
  return () => {
    return qs$(fs_)
  }
};
lambda$28 = function lambda$(fss) {
  let scrut, param0, param1, fs_, gss, scrut1, param01, param11, fs_1, tmp, tmp1, tmp2;
  scrut = NofibPrelude.force(fss);
  if (scrut instanceof power1.Pz.class) {
    return power1.Pz
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    if (param0 === 0) {
      gss = param1;
      scrut1 = NofibPrelude.force(gss);
      if (scrut1 instanceof power1.Pc.class) {
        param01 = scrut1.f;
        param11 = scrut1.s;
        if (param01 === 0) {
          fs_1 = param11;
          tmp = power1.sqrtPs(fs_1);
          return power1.Pc(0, tmp)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (param0 === 1) {
      fs_ = param1;
      tmp1 = qs$(fs_);
      tmp2 = NofibPrelude.force(tmp1);
      return NofibPrelude.force(tmp2)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda42 = (undefined, function (fss) {
  return () => {
    return lambda$28(fss)
  }
});
lambda$27 = function lambda$(fss, n) {
  let scrut, param0, param1, f, fs_, tmp, tmp1, tmp2;
  scrut = NofibPrelude.force(fss);
  if (scrut instanceof power1.Pz.class) {
    return power1.Pz
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    f = param0;
    fs_ = param1;
    tmp = f / n;
    tmp1 = n + 1;
    tmp2 = int11(fs_, tmp1);
    return power1.Pc(tmp, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda40 = (undefined, function (fss, n) {
  return () => {
    return lambda$27(fss, n)
  }
});
int11 = function int1(fss, n) {
  let tmp;
  tmp = runtime.safeCall(lambda40(fss, n));
  return NofibPrelude.lazy(tmp)
};
lambda$26 = function lambda$(fs_) {
  let tmp, tmp1;
  tmp = runtime.safeCall(fs_());
  tmp1 = int11(tmp, 1);
  return power1.Pc(0, tmp1)
};
lambda41 = (undefined, function (fs_) {
  return () => {
    return lambda$26(fs_)
  }
});
lambda$25 = function lambda$(fss, n) {
  let scrut, param0, param1, f, fs_, tmp, tmp1, tmp2;
  scrut = NofibPrelude.force(fss);
  if (scrut instanceof power1.Pz.class) {
    return power1.Pz
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    f = param0;
    fs_ = param1;
    tmp = f / n;
    tmp1 = n + 1;
    tmp2 = int1(fs_, tmp1);
    return power1.Pc(tmp, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda38 = (undefined, function (fss, n) {
  return () => {
    return lambda$25(fss, n)
  }
});
int1 = function int1(fss, n) {
  let tmp;
  tmp = runtime.safeCall(lambda38(fss, n));
  return NofibPrelude.lazy(tmp)
};
lambda$24 = function lambda$(fs_) {
  let tmp;
  tmp = int1(fs_, 1);
  return power1.Pc(0, tmp)
};
lambda39 = (undefined, function (fs_) {
  return () => {
    return lambda$24(fs_)
  }
});
lambda$23 = function lambda$(gss, n) {
  let scrut, param0, param1, f, fs_, tmp, tmp1, tmp2;
  scrut = NofibPrelude.force(gss);
  if (scrut instanceof power1.Pz.class) {
    return power1.Pz
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    f = param0;
    fs_ = param1;
    tmp = n * f;
    tmp1 = n + 1;
    tmp2 = deriv1(fs_, tmp1);
    return power1.Pc(tmp, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda37 = (undefined, function (gss, n) {
  return () => {
    return lambda$23(gss, n)
  }
});
deriv1 = function deriv1(gss, n) {
  let tmp;
  tmp = runtime.safeCall(lambda37(gss, n));
  return NofibPrelude.lazy(tmp)
};
lambda$22 = function lambda$(fss) {
  let scrut, param0, param1, fs_, tmp;
  scrut = NofibPrelude.force(fss);
  if (scrut instanceof power1.Pz.class) {
    return power1.Pz
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    fs_ = param1;
    tmp = deriv1(fs_, 1);
    return NofibPrelude.force(tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda36 = (undefined, function (fss) {
  return () => {
    return lambda$22(fss)
  }
});
lambda$21 = function lambda$(fs_) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = power1.fromIntegerPs(1);
  tmp1 = rs$(fs_);
  tmp2 = power1.compose_(fs_, tmp1);
  tmp3 = power1.divPs(tmp, tmp2);
  return power1.Pc(0, tmp3)
};
lambda33 = (undefined, function (fs_) {
  return () => {
    return lambda$21(fs_)
  }
});
rs$ = function rs$(fs_) {
  let tmp;
  tmp = runtime.safeCall(lambda33(fs_));
  return NofibPrelude.lazy(tmp)
};
rs = function rs(fs_) {
  return () => {
    return rs$(fs_)
  }
};
lambda35 = (undefined, function () {
  return power1.Pz
});
lambda$20 = function lambda$(f1) {
  let tmp, tmp1;
  tmp = 1 / f1;
  tmp1 = NofibPrelude.lazy(lambda35);
  return power1.Pc(tmp, tmp1)
};
lambda34 = (undefined, function (f1) {
  return () => {
    return lambda$20(f1)
  }
});
lambda$19 = function lambda$(fss) {
  let scrut, param0, param1, f0, kss, scrut1, param01, param11, f1, gss, scrut2, fs_, tmp, tmp1, tmp2, tmp3, lambda$this;
  scrut = NofibPrelude.force(fss);
  if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    if (param0 === 0) {
      fs_ = param1;
      tmp = rs$(fs_);
      return NofibPrelude.force(tmp)
    } else {
      f0 = param0;
      kss = param1;
      scrut1 = NofibPrelude.force(kss);
      if (scrut1 instanceof power1.Pc.class) {
        param01 = scrut1.f;
        param11 = scrut1.s;
        f1 = param01;
        gss = param11;
        scrut2 = NofibPrelude.force(gss);
        if (scrut2 instanceof power1.Pz.class) {
          tmp1 = - 1;
          tmp2 = tmp1 / f1;
          lambda$this = runtime.safeCall(lambda34(f1));
          tmp3 = NofibPrelude.lazy(lambda$this);
          return power1.Pc(tmp2, tmp3)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda32 = (undefined, function (fss) {
  return () => {
    return lambda$19(fss)
  }
});
lambda26 = (undefined, function () {
  return power1.Pz
});
lambda$18 = function lambda$(gs) {
  return power1.Pc(0, gs)
};
lambda27 = (undefined, function (gs) {
  return () => {
    return lambda$18(gs)
  }
});
lambda29 = (undefined, function () {
  return power1.Pz
});
lambda$17 = function lambda$(f) {
  let tmp;
  tmp = NofibPrelude.lazy(lambda29);
  return power1.Pc(f, tmp)
};
lambda28 = (undefined, function (f) {
  return () => {
    return lambda$17(f)
  }
});
lambda31 = (undefined, function () {
  return power1.Pz
});
lambda$16 = function lambda$(f) {
  let tmp;
  tmp = NofibPrelude.lazy(lambda31);
  return power1.Pc(f, tmp)
};
lambda30 = (undefined, function (f) {
  return () => {
    return lambda$16(f)
  }
});
lambda$15 = function lambda$(fss, gss) {
  let scrut, param0, param1, f, fs_, scrut1, param01, param11, gs, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, lambda$this, lambda$this1, lambda$this2;
  scrut = NofibPrelude.force(fss);
  if (scrut instanceof power1.Pz.class) {
    return power1.Pz
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    f = param0;
    fs_ = param1;
    tmp = NofibPrelude.force(gss);
    scrut1 = NofibPrelude.force(tmp);
    if (scrut1 instanceof power1.Pz.class) {
      tmp1 = NofibPrelude.lazy(lambda26);
      return power1.Pc(f, tmp1)
    } else if (scrut1 instanceof power1.Pc.class) {
      param01 = scrut1.f;
      param11 = scrut1.s;
      if (param01 === 0) {
        gs = param11;
        lambda$this = runtime.safeCall(lambda27(gs));
        tmp2 = NofibPrelude.lazy(lambda$this);
        tmp3 = power1.compose_(fs_, tmp2);
        tmp4 = power1.multPs(gs, tmp3);
        return power1.Pc(f, tmp4)
      } else {
        lambda$this1 = runtime.safeCall(lambda28(f));
        tmp5 = NofibPrelude.lazy(lambda$this1);
        tmp6 = power1.addPs(tmp5);
        tmp7 = power1.composeSndLz_(fs_, gss);
        tmp8 = power1.multPs(gss, tmp7);
        return NofibPrelude.force(tmp6, tmp8)
      }
    } else {
      lambda$this2 = runtime.safeCall(lambda30(f));
      tmp9 = NofibPrelude.lazy(lambda$this2);
      tmp10 = power1.addPs(tmp9);
      tmp11 = power1.composeSndLz_(fs_, gss);
      tmp12 = power1.multPs(gss, tmp11);
      return NofibPrelude.force(tmp10, tmp12)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda25 = (undefined, function (fss, gss) {
  return () => {
    return lambda$15(fss, gss)
  }
});
lambda19 = (undefined, function () {
  return power1.Pz
});
lambda$14 = function lambda$(gs) {
  return power1.Pc(0, gs)
};
lambda20 = (undefined, function (gs) {
  return () => {
    return lambda$14(gs)
  }
});
lambda22 = (undefined, function () {
  return power1.Pz
});
lambda$13 = function lambda$(f) {
  let tmp;
  tmp = NofibPrelude.lazy(lambda22);
  return power1.Pc(f, tmp)
};
lambda21 = (undefined, function (f) {
  return () => {
    return lambda$13(f)
  }
});
lambda24 = (undefined, function () {
  return power1.Pz
});
lambda$12 = function lambda$(f) {
  let tmp;
  tmp = NofibPrelude.lazy(lambda24);
  return power1.Pc(f, tmp)
};
lambda23 = (undefined, function (f) {
  return () => {
    return lambda$12(f)
  }
});
lambda$11 = function lambda$(fss, gss) {
  let scrut, param0, param1, f, fs_, scrut1, param01, param11, gs, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, lambda$this, lambda$this1, lambda$this2;
  scrut = NofibPrelude.force(fss);
  if (scrut instanceof power1.Pz.class) {
    return power1.Pz
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    f = param0;
    fs_ = param1;
    scrut1 = NofibPrelude.force(gss);
    if (scrut1 instanceof power1.Pz.class) {
      tmp = NofibPrelude.lazy(lambda19);
      return power1.Pc(f, tmp)
    } else if (scrut1 instanceof power1.Pc.class) {
      param01 = scrut1.f;
      param11 = scrut1.s;
      if (param01 === 0) {
        gs = param11;
        lambda$this = runtime.safeCall(lambda20(gs));
        tmp1 = NofibPrelude.lazy(lambda$this);
        tmp2 = power1.compose_(fs_, tmp1);
        tmp3 = power1.multPs(gs, tmp2);
        return power1.Pc(f, tmp3)
      } else {
        lambda$this1 = runtime.safeCall(lambda21(f));
        tmp4 = NofibPrelude.lazy(lambda$this1);
        tmp5 = power1.addPs(tmp4);
        tmp6 = power1.compose_(fs_, gss);
        tmp7 = power1.multPs(gss, tmp6);
        return NofibPrelude.force(tmp5, tmp7)
      }
    } else {
      lambda$this2 = runtime.safeCall(lambda23(f));
      tmp8 = NofibPrelude.lazy(lambda$this2);
      tmp9 = power1.addPs(tmp8);
      tmp10 = power1.compose_(fs_, gss);
      tmp11 = power1.multPs(gss, tmp10);
      return NofibPrelude.force(tmp9, tmp11)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda18 = (undefined, function (fss, gss) {
  return () => {
    return lambda$11(fss, gss)
  }
});
lambda14 = (undefined, function () {
  return power1.Pz
});
lambda$10 = function lambda$(g, gs) {
  return power1.Pc(g, gs)
};
lambda15 = (undefined, function (g, gs) {
  return () => {
    return lambda$10(g, gs)
  }
});
lambda$9 = function lambda$(g, gs) {
  return power1.Pc(g, gs)
};
lambda16 = (undefined, function (g, gs) {
  return () => {
    return lambda$9(g, gs)
  }
});
lambda$8 = function lambda$(g, gs) {
  return power1.Pc(g, gs)
};
lambda17 = (undefined, function (g, gs) {
  return () => {
    return lambda$8(g, gs)
  }
});
lambda$7 = function lambda$(fss, gss) {
  let scrut, param0, param1, f, fs_, scrut1, param01, param11, g, gs, q, fs_1, scrut2, param02, param12, g1, gs1, q1, gs2, scrut3, param03, param13, gs3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, lambda$this, lambda$this1, lambda$this2;
  scrut = NofibPrelude.force(fss);
  if (scrut instanceof power1.Pz.class) {
    scrut3 = NofibPrelude.force(gss);
    if (scrut3 instanceof power1.Pz.class) {
      throw globalThis.Error("power series 0/0");
    } else if (scrut3 instanceof power1.Pc.class) {
      param03 = scrut3.f;
      param13 = scrut3.s;
      if (param03 === 0) {
        gs3 = param13;
        tmp = NofibPrelude.lazy(lambda14, gs3);
        tmp1 = power1.divPs(tmp);
        return NofibPrelude.force(tmp1)
      } else {
        return power1.Pz
      }
    } else {
      return power1.Pz
    }
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    if (param0 === 0) {
      fs_1 = param1;
      scrut2 = NofibPrelude.force(gss);
      if (scrut2 instanceof power1.Pc.class) {
        param02 = scrut2.f;
        param12 = scrut2.s;
        if (param02 === 0) {
          gs2 = param12;
          tmp2 = power1.divPs(fs_1, gs2);
          return NofibPrelude.force(tmp2)
        } else {
          g1 = param02;
          gs1 = param12;
          q1 = 0;
          tmp3 = power1.dotMult(q1, gs1);
          tmp4 = power1.negatePs(tmp3);
          tmp5 = power1.addPs(fs_1, tmp4);
          lambda$this = runtime.safeCall(lambda15(g1, gs1));
          tmp6 = NofibPrelude.lazy(lambda$this);
          tmp7 = power1.divPs(tmp5, tmp6);
          return power1.Pc(q1, tmp7)
        }
      } else {
        f = param0;
        fs_ = param1;
        scrut1 = NofibPrelude.force(gss);
        if (scrut1 instanceof power1.Pc.class) {
          param01 = scrut1.f;
          param11 = scrut1.s;
          g = param01;
          gs = param11;
          tmp8 = f / g;
          q = tmp8;
          tmp9 = power1.dotMult(q, gs);
          tmp10 = power1.negatePs(tmp9);
          tmp11 = power1.addPs(fs_, tmp10);
          lambda$this1 = runtime.safeCall(lambda16(g, gs));
          tmp12 = NofibPrelude.lazy(lambda$this1);
          tmp13 = power1.divPs(tmp11, tmp12);
          return power1.Pc(q, tmp13)
        } else {
          throw new globalThis.Error("match error");
        }
      }
    } else {
      f = param0;
      fs_ = param1;
      scrut1 = NofibPrelude.force(gss);
      if (scrut1 instanceof power1.Pc.class) {
        param01 = scrut1.f;
        param11 = scrut1.s;
        g = param01;
        gs = param11;
        tmp14 = f / g;
        q = tmp14;
        tmp15 = power1.dotMult(q, gs);
        tmp16 = power1.negatePs(tmp15);
        tmp17 = power1.addPs(fs_, tmp16);
        lambda$this2 = runtime.safeCall(lambda17(g, gs));
        tmp18 = NofibPrelude.lazy(lambda$this2);
        tmp19 = power1.divPs(tmp17, tmp18);
        return power1.Pc(q, tmp19)
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda13 = (undefined, function (fss, gss) {
  return () => {
    return lambda$7(fss, gss)
  }
});
lambda$6 = function lambda$(fss, gss) {
  let scrut, param0, param1, f, fs_, scrut1, param01, param11, g, gs, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
  tmp = NofibPrelude.force(fss);
  scrut = NofibPrelude.force(tmp);
  if (scrut instanceof power1.Pz.class) {
    return power1.Pz
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    f = param0;
    fs_ = param1;
    scrut1 = NofibPrelude.force(gss);
    if (scrut1 instanceof power1.Pz.class) {
      return power1.Pz
    } else if (scrut1 instanceof power1.Pc.class) {
      param01 = scrut1.f;
      param11 = scrut1.s;
      g = param01;
      gs = param11;
      tmp1 = f * g;
      tmp2 = power1.dotMult(f, gs);
      tmp3 = power1.dotMult(g, fs_);
      tmp4 = power1.addPs(tmp2, tmp3);
      tmp5 = power1.x_();
      tmp6 = power1.multPs(tmp5, fs_);
      tmp7 = power1.multPs(tmp6, gs);
      tmp8 = power1.addPs(tmp4, tmp7);
      return power1.Pc(tmp1, tmp8)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda12 = (undefined, function (fss, gss) {
  return () => {
    return lambda$6(fss, gss)
  }
});
lambda$5 = function lambda$(fss, gss) {
  let scrut, param0, param1, f, fs_, scrut1, param01, param11, g, gs, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  scrut = NofibPrelude.force(fss);
  if (scrut instanceof power1.Pz.class) {
    return power1.Pz
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    f = param0;
    fs_ = param1;
    scrut1 = NofibPrelude.force(gss);
    if (scrut1 instanceof power1.Pz.class) {
      return power1.Pz
    } else if (scrut1 instanceof power1.Pc.class) {
      param01 = scrut1.f;
      param11 = scrut1.s;
      g = param01;
      gs = param11;
      tmp = f * g;
      tmp1 = power1.dotMult(f, gs);
      tmp2 = power1.dotMult(g, fs_);
      tmp3 = power1.addPs(tmp1, tmp2);
      tmp4 = power1.x_();
      tmp5 = power1.multPs(tmp4, fs_);
      tmp6 = power1.multPs(tmp5, gs);
      tmp7 = power1.addPs(tmp3, tmp6);
      return power1.Pc(tmp, tmp7)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda11 = (undefined, function (fss, gss) {
  return () => {
    return lambda$5(fss, gss)
  }
});
lambda$4 = function lambda$(fss, gs) {
  let scrut, param0, param1, f, fs_, scrut1, param01, param11, g, gs1, tmp, tmp1;
  scrut = NofibPrelude.force(fss);
  if (scrut instanceof power1.Pz.class) {
    return NofibPrelude.force(gs)
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    f = param0;
    fs_ = param1;
    scrut1 = NofibPrelude.force(gs);
    if (scrut1 instanceof power1.Pz.class) {
      return NofibPrelude.force(fss)
    } else if (scrut1 instanceof power1.Pc.class) {
      param01 = scrut1.f;
      param11 = scrut1.s;
      g = param01;
      gs1 = param11;
      tmp = f + g;
      tmp1 = power1.addPs(fs_, gs1);
      return power1.Pc(tmp, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda10 = (undefined, function (fss, gs) {
  return () => {
    return lambda$4(fss, gs)
  }
});
lambda$3 = function lambda$(ps) {
  let scrut, param0, param1, f, fs_, tmp, tmp1;
  scrut = NofibPrelude.force(ps);
  if (scrut instanceof power1.Pz.class) {
    return power1.Pz
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    f = param0;
    fs_ = param1;
    tmp = - f;
    tmp1 = power1.negatePs(fs_);
    return power1.Pc(tmp, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda9 = (undefined, function (ps) {
  return () => {
    return lambda$3(ps)
  }
});
lambda$2 = function lambda$(c, ps) {
  let scrut, param0, param1, f, fs_, tmp, tmp1, tmp2;
  tmp = NofibPrelude.force(ps);
  scrut = NofibPrelude.force(tmp);
  if (scrut instanceof power1.Pz.class) {
    return power1.Pz
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    f = param0;
    fs_ = param1;
    tmp1 = c * f;
    tmp2 = power1.dotMult(c, fs_);
    return power1.Pc(tmp1, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda8 = (undefined, function (c, ps) {
  return () => {
    return lambda$2(c, ps)
  }
});
lambda$1 = function lambda$(c, ps) {
  let scrut, param0, param1, f, fs_, tmp, tmp1;
  scrut = NofibPrelude.force(ps);
  if (scrut instanceof power1.Pz.class) {
    return power1.Pz
  } else if (scrut instanceof power1.Pc.class) {
    param0 = scrut.f;
    param1 = scrut.s;
    f = param0;
    fs_ = param1;
    tmp = c * f;
    tmp1 = power1.dotMult(c, fs_);
    return power1.Pc(tmp, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda7 = (undefined, function (c, ps) {
  return () => {
    return lambda$1(c, ps)
  }
});
lambda4 = (undefined, function () {
  return power1.Pz
});
lambda6 = (undefined, function () {
  return power1.Pz
});
lambda$ = function lambda$(c) {
  let tmp;
  tmp = NofibPrelude.lazy(lambda6);
  return power1.Pc(c, tmp)
};
lambda5 = (undefined, function (c) {
  return () => {
    return lambda$(c)
  }
});
lambda3 = (undefined, function () {
  return power1.Pz
});
lambda2 = (undefined, function () {
  let tmp;
  tmp = NofibPrelude.lazy(lambda3);
  return power1.Pc(1, tmp)
});
lambda1 = (undefined, function () {
  let tmp;
  tmp = NofibPrelude.lazy(lambda2);
  return power1.Pc(0, tmp)
});
lambda = (undefined, function () {
  let tmp;
  tmp = power1.list();
  return power1.Pc(1, tmp)
});
power1 = class power {
  static {
    power1 = power;
    let lambda52;
    this.Pss = class Pss {
      constructor() {}
      toString() { return "Pss"; }
    };
    this.Pc = function Pc(f1, s1) {
      return new Pc.class(f1, s1);
    };
    this.Pc.class = class Pc extends power.Pss {
      constructor(f, s) {
        super();
        this.f = f;
        this.s = s;
      }
      toString() { return "Pc(" + globalThis.Predef.render(this.f) + ", " + globalThis.Predef.render(this.s) + ")"; }
    };
    const Pz$class = class Pz extends power.Pss {
      constructor() {
        super();
      }
      toString() { return "Pz"; }
    };
    this.Pz = new Pz$class;
    this.Pz.class = Pz$class;
    lambda52 = (undefined, function () {
      let tmp;
      tmp = power.testPower_nofib(14);
      return runtime.safeCall(tmp.toString())
    });
    BenchmarkPrelude.benchmark(lambda52)
  }
  static list() {
    return NofibPrelude.lazy(lambda)
  } 
  static x_() {
    return NofibPrelude.lazy(lambda1)
  } 
  static fromIntegerPs(c) {
    let scrut, lambda$this;
    scrut = c == 0;
    if (scrut === true) {
      return NofibPrelude.lazy(lambda4)
    } else {
      lambda$this = runtime.safeCall(lambda5(c));
      return NofibPrelude.lazy(lambda$this)
    }
  } 
  static extract(n, ps) {
    let scrut, param0, param1, x, ps1, scrut1, tmp, tmp1;
    scrut1 = n == 0;
    if (scrut1 === true) {
      return NofibPrelude.Nil
    } else {
      scrut = NofibPrelude.force(ps);
      if (scrut instanceof power.Pz.class) {
        return NofibPrelude.Nil
      } else if (scrut instanceof power.Pc.class) {
        param0 = scrut.f;
        param1 = scrut.s;
        x = param0;
        ps1 = param1;
        tmp = n - 1;
        tmp1 = power.extract(tmp, ps1);
        return NofibPrelude.Cons(x, tmp1)
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  static dotMult(c1, ps1) {
    let tmp;
    tmp = runtime.safeCall(lambda7(c1, ps1));
    return NofibPrelude.lazy(tmp)
  } 
  static dotMultSndLz(c2, ps2) {
    let tmp;
    tmp = runtime.safeCall(lambda8(c2, ps2));
    return NofibPrelude.lazy(tmp)
  } 
  static negatePs(ps3) {
    let tmp;
    tmp = runtime.safeCall(lambda9(ps3));
    return NofibPrelude.lazy(tmp)
  } 
  static addPs(fss, gs) {
    let tmp;
    tmp = runtime.safeCall(lambda10(fss, gs));
    return NofibPrelude.lazy(tmp)
  } 
  static minusPs(a, b) {
    let tmp;
    tmp = power.negatePs(b);
    return power.addPs(a, tmp)
  } 
  static multPs(fss1, gss) {
    let tmp;
    tmp = runtime.safeCall(lambda11(fss1, gss));
    return NofibPrelude.lazy(tmp)
  } 
  static multPsFstLz(fss2, gss1) {
    let tmp;
    tmp = runtime.safeCall(lambda12(fss2, gss1));
    return NofibPrelude.lazy(tmp)
  } 
  static powerPs(a1, n1) {
    let scrut, tmp, tmp1;
    scrut = n1 <= 0;
    if (scrut === true) {
      return power.fromIntegerPs(1)
    } else {
      tmp = n1 - 1;
      tmp1 = power.powerPs(a1, tmp);
      return power.multPs(a1, tmp1)
    }
  } 
  static divPs(fss3, gss2) {
    let tmp;
    tmp = runtime.safeCall(lambda13(fss3, gss2));
    return NofibPrelude.lazy(tmp)
  } 
  static compose_(fss4, gss3) {
    let tmp;
    tmp = runtime.safeCall(lambda18(fss4, gss3));
    return NofibPrelude.lazy(tmp)
  } 
  static composeSndLz_(fss5, gss4) {
    let tmp;
    tmp = runtime.safeCall(lambda25(fss5, gss4));
    return NofibPrelude.lazy(tmp)
  } 
  static revert(fss6) {
    let tmp;
    tmp = runtime.safeCall(lambda32(fss6));
    return NofibPrelude.lazy(tmp)
  } 
  static deriv(fss7) {
    let tmp;
    tmp = runtime.safeCall(lambda36(fss7));
    return NofibPrelude.lazy(tmp)
  } 
  static integral(fs_) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda39(fs_));
    return NofibPrelude.lazy(lambda$this)
  } 
  static integralLz(fs_1) {
    let tmp;
    tmp = runtime.safeCall(lambda41(fs_1));
    return NofibPrelude.lazy(tmp)
  } 
  static sqrtPs(fss8) {
    let tmp;
    tmp = runtime.safeCall(lambda42(fss8));
    return NofibPrelude.lazy(tmp)
  } 
  static ts() {
    let tmp;
    tmp = lambda45;
    return NofibPrelude.lazy(tmp)
  } 
  static tree() {
    let tmp;
    tmp = lambda46;
    return NofibPrelude.lazy(tmp)
  } 
  static cosx() {
    let tmp, tmp1, tmp2;
    tmp = NofibPrelude.lazy(lambda48);
    tmp1 = power.integralLz(power.cosx);
    tmp2 = power.integral(tmp1);
    return power.minusPs(tmp, tmp2)
  } 
  static sinx() {
    let tmp, tmp1, tmp2;
    tmp = NofibPrelude.lazy(lambda50);
    tmp1 = power.integralLz(power.sinx);
    tmp2 = power.minusPs(tmp, tmp1);
    return power.integral(tmp2)
  } 
  static testPower_nofib(p) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26;
    tmp = power.sinx();
    tmp1 = power.fromIntegerPs(1);
    tmp2 = power.cosx();
    tmp3 = power.powerPs(tmp2, 2);
    tmp4 = power.minusPs(tmp1, tmp3);
    tmp5 = power.sqrtPs(tmp4);
    tmp6 = power.minusPs(tmp, tmp5);
    tmp7 = power.extract(p, tmp6);
    tmp8 = power.sinx();
    tmp9 = power.cosx();
    tmp10 = power.divPs(tmp8, tmp9);
    tmp11 = power.fromIntegerPs(1);
    tmp12 = power.fromIntegerPs(1);
    tmp13 = power.x_();
    tmp14 = power.powerPs(tmp13, 2);
    tmp15 = power.addPs(tmp12, tmp14);
    tmp16 = power.divPs(tmp11, tmp15);
    tmp17 = power.integral(tmp16);
    tmp18 = power.revert(tmp17);
    tmp19 = power.minusPs(tmp10, tmp18);
    tmp20 = power.extract(p, tmp19);
    tmp21 = (tmp7 , tmp20);
    tmp22 = power.ts();
    tmp23 = power.extract(p, tmp22);
    tmp24 = (tmp21 , tmp23);
    tmp25 = power.tree();
    tmp26 = power.extract(p, tmp25);
    return (tmp24 , tmp26)
  }
  static toString() { return "power"; }
};
let power = power1; export default power;
