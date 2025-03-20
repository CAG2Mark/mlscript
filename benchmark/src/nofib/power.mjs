import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let power1;
power1 = class power {
  static {
    let lambda;
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
    lambda = (undefined, function () {
      let tmp;
      tmp = power.testPower_nofib(14);
      return runtime.safeCall(tmp.toString())
    });
    BenchmarkPrelude.benchmark(lambda)
  }
  static list() {
    let lambda;
    lambda = (undefined, function () {
      let tmp;
      tmp = power.list();
      return power.Pc(1, tmp)
    });
    return NofibPrelude.lazy(lambda)
  } 
  static x_() {
    let lambda;
    lambda = (undefined, function () {
      let tmp, lambda1;
      lambda1 = (undefined, function () {
        let tmp1, lambda2;
        lambda2 = (undefined, function () {
          return power.Pz
        });
        tmp1 = NofibPrelude.lazy(lambda2);
        return power.Pc(1, tmp1)
      });
      tmp = NofibPrelude.lazy(lambda1);
      return power.Pc(0, tmp)
    });
    return NofibPrelude.lazy(lambda)
  } 
  static fromIntegerPs(c) {
    let scrut, lambda, lambda1;
    scrut = c == 0;
    if (scrut === true) {
      lambda = (undefined, function () {
        return power.Pz
      });
      return NofibPrelude.lazy(lambda)
    } else {
      lambda1 = (undefined, function () {
        let tmp, lambda2;
        lambda2 = (undefined, function () {
          return power.Pz
        });
        tmp = NofibPrelude.lazy(lambda2);
        return power.Pc(c, tmp)
      });
      return NofibPrelude.lazy(lambda1)
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
    let tmp, lambda;
    lambda = (undefined, function () {
      let scrut, param0, param1, f, fs_, tmp1, tmp2;
      scrut = NofibPrelude.force(ps1);
      if (scrut instanceof power.Pz.class) {
        return power.Pz
      } else if (scrut instanceof power.Pc.class) {
        param0 = scrut.f;
        param1 = scrut.s;
        f = param0;
        fs_ = param1;
        tmp1 = c1 * f;
        tmp2 = power.dotMult(c1, fs_);
        return power.Pc(tmp1, tmp2)
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static dotMultSndLz(c2, ps2) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let scrut, param0, param1, f, fs_, tmp1, tmp2, tmp3;
      tmp1 = NofibPrelude.force(ps2);
      scrut = NofibPrelude.force(tmp1);
      if (scrut instanceof power.Pz.class) {
        return power.Pz
      } else if (scrut instanceof power.Pc.class) {
        param0 = scrut.f;
        param1 = scrut.s;
        f = param0;
        fs_ = param1;
        tmp2 = c2 * f;
        tmp3 = power.dotMult(c2, fs_);
        return power.Pc(tmp2, tmp3)
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static negatePs(ps3) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let scrut, param0, param1, f, fs_, tmp1, tmp2;
      scrut = NofibPrelude.force(ps3);
      if (scrut instanceof power.Pz.class) {
        return power.Pz
      } else if (scrut instanceof power.Pc.class) {
        param0 = scrut.f;
        param1 = scrut.s;
        f = param0;
        fs_ = param1;
        tmp1 = - f;
        tmp2 = power.negatePs(fs_);
        return power.Pc(tmp1, tmp2)
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static addPs(fss, gs) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let scrut, param0, param1, f, fs_, scrut1, param01, param11, g, gs1, tmp1, tmp2;
      scrut = NofibPrelude.force(fss);
      if (scrut instanceof power.Pz.class) {
        return NofibPrelude.force(gs)
      } else if (scrut instanceof power.Pc.class) {
        param0 = scrut.f;
        param1 = scrut.s;
        f = param0;
        fs_ = param1;
        scrut1 = NofibPrelude.force(gs);
        if (scrut1 instanceof power.Pz.class) {
          return NofibPrelude.force(fss)
        } else if (scrut1 instanceof power.Pc.class) {
          param01 = scrut1.f;
          param11 = scrut1.s;
          g = param01;
          gs1 = param11;
          tmp1 = f + g;
          tmp2 = power.addPs(fs_, gs1);
          return power.Pc(tmp1, tmp2)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static minusPs(a, b) {
    let tmp;
    tmp = power.negatePs(b);
    return power.addPs(a, tmp)
  } 
  static multPs(fss1, gss) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let scrut, param0, param1, f, fs_, scrut1, param01, param11, g, gs1, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
      scrut = NofibPrelude.force(fss1);
      if (scrut instanceof power.Pz.class) {
        return power.Pz
      } else if (scrut instanceof power.Pc.class) {
        param0 = scrut.f;
        param1 = scrut.s;
        f = param0;
        fs_ = param1;
        scrut1 = NofibPrelude.force(gss);
        if (scrut1 instanceof power.Pz.class) {
          return power.Pz
        } else if (scrut1 instanceof power.Pc.class) {
          param01 = scrut1.f;
          param11 = scrut1.s;
          g = param01;
          gs1 = param11;
          tmp1 = f * g;
          tmp2 = power.dotMult(f, gs1);
          tmp3 = power.dotMult(g, fs_);
          tmp4 = power.addPs(tmp2, tmp3);
          tmp5 = power.x_();
          tmp6 = power.multPs(tmp5, fs_);
          tmp7 = power.multPs(tmp6, gs1);
          tmp8 = power.addPs(tmp4, tmp7);
          return power.Pc(tmp1, tmp8)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static multPsFstLz(fss2, gss1) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let scrut, param0, param1, f, fs_, scrut1, param01, param11, g, gs1, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
      tmp1 = NofibPrelude.force(fss2);
      scrut = NofibPrelude.force(tmp1);
      if (scrut instanceof power.Pz.class) {
        return power.Pz
      } else if (scrut instanceof power.Pc.class) {
        param0 = scrut.f;
        param1 = scrut.s;
        f = param0;
        fs_ = param1;
        scrut1 = NofibPrelude.force(gss1);
        if (scrut1 instanceof power.Pz.class) {
          return power.Pz
        } else if (scrut1 instanceof power.Pc.class) {
          param01 = scrut1.f;
          param11 = scrut1.s;
          g = param01;
          gs1 = param11;
          tmp2 = f * g;
          tmp3 = power.dotMult(f, gs1);
          tmp4 = power.dotMult(g, fs_);
          tmp5 = power.addPs(tmp3, tmp4);
          tmp6 = power.x_();
          tmp7 = power.multPs(tmp6, fs_);
          tmp8 = power.multPs(tmp7, gs1);
          tmp9 = power.addPs(tmp5, tmp8);
          return power.Pc(tmp2, tmp9)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
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
    let tmp, lambda;
    lambda = (undefined, function () {
      let scrut, param0, param1, f, fs_, scrut1, param01, param11, g, gs1, q, fs_1, scrut2, param02, param12, g1, gs2, q1, gs3, scrut3, param03, param13, gs4, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, lambda1, lambda2, lambda3, lambda4;
      scrut = NofibPrelude.force(fss3);
      if (scrut instanceof power.Pz.class) {
        scrut3 = NofibPrelude.force(gss2);
        if (scrut3 instanceof power.Pz.class) {
          throw globalThis.Error("power series 0/0");
        } else if (scrut3 instanceof power.Pc.class) {
          param03 = scrut3.f;
          param13 = scrut3.s;
          if (param03 === 0) {
            gs4 = param13;
            lambda1 = (undefined, function () {
              return power.Pz
            });
            tmp1 = NofibPrelude.lazy(lambda1, gs4);
            tmp2 = power.divPs(tmp1);
            return NofibPrelude.force(tmp2)
          } else {
            return power.Pz
          }
        } else {
          return power.Pz
        }
      } else if (scrut instanceof power.Pc.class) {
        param0 = scrut.f;
        param1 = scrut.s;
        if (param0 === 0) {
          fs_1 = param1;
          scrut2 = NofibPrelude.force(gss2);
          if (scrut2 instanceof power.Pc.class) {
            param02 = scrut2.f;
            param12 = scrut2.s;
            if (param02 === 0) {
              gs3 = param12;
              tmp3 = power.divPs(fs_1, gs3);
              return NofibPrelude.force(tmp3)
            } else {
              g1 = param02;
              gs2 = param12;
              q1 = 0;
              tmp4 = power.dotMult(q1, gs2);
              tmp5 = power.negatePs(tmp4);
              tmp6 = power.addPs(fs_1, tmp5);
              lambda2 = (undefined, function () {
                return power.Pc(g1, gs2)
              });
              tmp7 = NofibPrelude.lazy(lambda2);
              tmp8 = power.divPs(tmp6, tmp7);
              return power.Pc(q1, tmp8)
            }
          } else {
            f = param0;
            fs_ = param1;
            scrut1 = NofibPrelude.force(gss2);
            if (scrut1 instanceof power.Pc.class) {
              param01 = scrut1.f;
              param11 = scrut1.s;
              g = param01;
              gs1 = param11;
              tmp9 = f / g;
              q = tmp9;
              tmp10 = power.dotMult(q, gs1);
              tmp11 = power.negatePs(tmp10);
              tmp12 = power.addPs(fs_, tmp11);
              lambda3 = (undefined, function () {
                return power.Pc(g, gs1)
              });
              tmp13 = NofibPrelude.lazy(lambda3);
              tmp14 = power.divPs(tmp12, tmp13);
              return power.Pc(q, tmp14)
            } else {
              throw new globalThis.Error("match error");
            }
          }
        } else {
          f = param0;
          fs_ = param1;
          scrut1 = NofibPrelude.force(gss2);
          if (scrut1 instanceof power.Pc.class) {
            param01 = scrut1.f;
            param11 = scrut1.s;
            g = param01;
            gs1 = param11;
            tmp15 = f / g;
            q = tmp15;
            tmp16 = power.dotMult(q, gs1);
            tmp17 = power.negatePs(tmp16);
            tmp18 = power.addPs(fs_, tmp17);
            lambda4 = (undefined, function () {
              return power.Pc(g, gs1)
            });
            tmp19 = NofibPrelude.lazy(lambda4);
            tmp20 = power.divPs(tmp18, tmp19);
            return power.Pc(q, tmp20)
          } else {
            throw new globalThis.Error("match error");
          }
        }
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static compose_(fss4, gss3) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let scrut, param0, param1, f, fs_, scrut1, param01, param11, gs1, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, lambda1, lambda2, lambda3, lambda4;
      scrut = NofibPrelude.force(fss4);
      if (scrut instanceof power.Pz.class) {
        return power.Pz
      } else if (scrut instanceof power.Pc.class) {
        param0 = scrut.f;
        param1 = scrut.s;
        f = param0;
        fs_ = param1;
        scrut1 = NofibPrelude.force(gss3);
        if (scrut1 instanceof power.Pz.class) {
          lambda1 = (undefined, function () {
            return power.Pz
          });
          tmp1 = NofibPrelude.lazy(lambda1);
          return power.Pc(f, tmp1)
        } else if (scrut1 instanceof power.Pc.class) {
          param01 = scrut1.f;
          param11 = scrut1.s;
          if (param01 === 0) {
            gs1 = param11;
            lambda2 = (undefined, function () {
              return power.Pc(0, gs1)
            });
            tmp2 = NofibPrelude.lazy(lambda2);
            tmp3 = power.compose_(fs_, tmp2);
            tmp4 = power.multPs(gs1, tmp3);
            return power.Pc(f, tmp4)
          } else {
            lambda3 = (undefined, function () {
              let tmp13, lambda5;
              lambda5 = (undefined, function () {
                return power.Pz
              });
              tmp13 = NofibPrelude.lazy(lambda5);
              return power.Pc(f, tmp13)
            });
            tmp5 = NofibPrelude.lazy(lambda3);
            tmp6 = power.addPs(tmp5);
            tmp7 = power.compose_(fs_, gss3);
            tmp8 = power.multPs(gss3, tmp7);
            return NofibPrelude.force(tmp6, tmp8)
          }
        } else {
          lambda4 = (undefined, function () {
            let tmp13, lambda5;
            lambda5 = (undefined, function () {
              return power.Pz
            });
            tmp13 = NofibPrelude.lazy(lambda5);
            return power.Pc(f, tmp13)
          });
          tmp9 = NofibPrelude.lazy(lambda4);
          tmp10 = power.addPs(tmp9);
          tmp11 = power.compose_(fs_, gss3);
          tmp12 = power.multPs(gss3, tmp11);
          return NofibPrelude.force(tmp10, tmp12)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static composeSndLz_(fss5, gss4) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let scrut, param0, param1, f, fs_, scrut1, param01, param11, gs1, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, lambda1, lambda2, lambda3, lambda4;
      scrut = NofibPrelude.force(fss5);
      if (scrut instanceof power.Pz.class) {
        return power.Pz
      } else if (scrut instanceof power.Pc.class) {
        param0 = scrut.f;
        param1 = scrut.s;
        f = param0;
        fs_ = param1;
        tmp1 = NofibPrelude.force(gss4);
        scrut1 = NofibPrelude.force(tmp1);
        if (scrut1 instanceof power.Pz.class) {
          lambda1 = (undefined, function () {
            return power.Pz
          });
          tmp2 = NofibPrelude.lazy(lambda1);
          return power.Pc(f, tmp2)
        } else if (scrut1 instanceof power.Pc.class) {
          param01 = scrut1.f;
          param11 = scrut1.s;
          if (param01 === 0) {
            gs1 = param11;
            lambda2 = (undefined, function () {
              return power.Pc(0, gs1)
            });
            tmp3 = NofibPrelude.lazy(lambda2);
            tmp4 = power.compose_(fs_, tmp3);
            tmp5 = power.multPs(gs1, tmp4);
            return power.Pc(f, tmp5)
          } else {
            lambda3 = (undefined, function () {
              let tmp14, lambda5;
              lambda5 = (undefined, function () {
                return power.Pz
              });
              tmp14 = NofibPrelude.lazy(lambda5);
              return power.Pc(f, tmp14)
            });
            tmp6 = NofibPrelude.lazy(lambda3);
            tmp7 = power.addPs(tmp6);
            tmp8 = power.composeSndLz_(fs_, gss4);
            tmp9 = power.multPs(gss4, tmp8);
            return NofibPrelude.force(tmp7, tmp9)
          }
        } else {
          lambda4 = (undefined, function () {
            let tmp14, lambda5;
            lambda5 = (undefined, function () {
              return power.Pz
            });
            tmp14 = NofibPrelude.lazy(lambda5);
            return power.Pc(f, tmp14)
          });
          tmp10 = NofibPrelude.lazy(lambda4);
          tmp11 = power.addPs(tmp10);
          tmp12 = power.composeSndLz_(fs_, gss4);
          tmp13 = power.multPs(gss4, tmp12);
          return NofibPrelude.force(tmp11, tmp13)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static revert(fss6) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let rs, scrut, param0, param1, f0, kss, scrut1, param01, param11, f1, gss5, scrut2, fs_, tmp1, tmp2, tmp3, tmp4, lambda1;
      scrut = NofibPrelude.force(fss6);
      if (scrut instanceof power.Pc.class) {
        param0 = scrut.f;
        param1 = scrut.s;
        if (param0 === 0) {
          fs_ = param1;
          rs = function rs() {
            let tmp5, lambda2;
            lambda2 = (undefined, function () {
              let tmp6, tmp7, tmp8, tmp9;
              tmp6 = power.fromIntegerPs(1);
              tmp7 = rs();
              tmp8 = power.compose_(fs_, tmp7);
              tmp9 = power.divPs(tmp6, tmp8);
              return power.Pc(0, tmp9)
            });
            tmp5 = lambda2;
            return NofibPrelude.lazy(tmp5)
          };
          tmp1 = rs();
          return NofibPrelude.force(tmp1)
        } else {
          f0 = param0;
          kss = param1;
          scrut1 = NofibPrelude.force(kss);
          if (scrut1 instanceof power.Pc.class) {
            param01 = scrut1.f;
            param11 = scrut1.s;
            f1 = param01;
            gss5 = param11;
            scrut2 = NofibPrelude.force(gss5);
            if (scrut2 instanceof power.Pz.class) {
              tmp2 = - 1;
              tmp3 = tmp2 / f1;
              lambda1 = (undefined, function () {
                let tmp5, tmp6, lambda2;
                tmp5 = 1 / f1;
                lambda2 = (undefined, function () {
                  return power.Pz
                });
                tmp6 = NofibPrelude.lazy(lambda2);
                return power.Pc(tmp5, tmp6)
              });
              tmp4 = NofibPrelude.lazy(lambda1);
              return power.Pc(tmp3, tmp4)
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
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static deriv(fss7) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let deriv1, scrut, param0, param1, fs_, tmp1;
      scrut = NofibPrelude.force(fss7);
      if (scrut instanceof power.Pz.class) {
        return power.Pz
      } else if (scrut instanceof power.Pc.class) {
        param0 = scrut.f;
        param1 = scrut.s;
        fs_ = param1;
        deriv1 = function deriv1(gss5, n2) {
          let tmp2, lambda1;
          lambda1 = (undefined, function () {
            let scrut1, param01, param11, f, fs_1, tmp3, tmp4, tmp5;
            scrut1 = NofibPrelude.force(gss5);
            if (scrut1 instanceof power.Pz.class) {
              return power.Pz
            } else if (scrut1 instanceof power.Pc.class) {
              param01 = scrut1.f;
              param11 = scrut1.s;
              f = param01;
              fs_1 = param11;
              tmp3 = n2 * f;
              tmp4 = n2 + 1;
              tmp5 = deriv1(fs_1, tmp4);
              return power.Pc(tmp3, tmp5)
            } else {
              throw new globalThis.Error("match error");
            }
          });
          tmp2 = lambda1;
          return NofibPrelude.lazy(tmp2)
        };
        tmp1 = deriv1(fs_, 1);
        return NofibPrelude.force(tmp1)
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static integral(fs_) {
    let int1, lambda;
    int1 = function int1(fss8, n2) {
      let tmp, lambda1;
      lambda1 = (undefined, function () {
        let scrut, param0, param1, f, fs_1, tmp1, tmp2, tmp3;
        scrut = NofibPrelude.force(fss8);
        if (scrut instanceof power.Pz.class) {
          return power.Pz
        } else if (scrut instanceof power.Pc.class) {
          param0 = scrut.f;
          param1 = scrut.s;
          f = param0;
          fs_1 = param1;
          tmp1 = f / n2;
          tmp2 = n2 + 1;
          tmp3 = int1(fs_1, tmp2);
          return power.Pc(tmp1, tmp3)
        } else {
          throw new globalThis.Error("match error");
        }
      });
      tmp = lambda1;
      return NofibPrelude.lazy(tmp)
    };
    lambda = (undefined, function () {
      let tmp;
      tmp = int1(fs_, 1);
      return power.Pc(0, tmp)
    });
    return NofibPrelude.lazy(lambda)
  } 
  static integralLz(fs_1) {
    let int1, tmp, lambda;
    int1 = function int1(fss8, n2) {
      let tmp1, lambda1;
      lambda1 = (undefined, function () {
        let scrut, param0, param1, f, fs_2, tmp2, tmp3, tmp4;
        scrut = NofibPrelude.force(fss8);
        if (scrut instanceof power.Pz.class) {
          return power.Pz
        } else if (scrut instanceof power.Pc.class) {
          param0 = scrut.f;
          param1 = scrut.s;
          f = param0;
          fs_2 = param1;
          tmp2 = f / n2;
          tmp3 = n2 + 1;
          tmp4 = int1(fs_2, tmp3);
          return power.Pc(tmp2, tmp4)
        } else {
          throw new globalThis.Error("match error");
        }
      });
      tmp1 = lambda1;
      return NofibPrelude.lazy(tmp1)
    };
    lambda = (undefined, function () {
      let tmp1, tmp2;
      tmp1 = runtime.safeCall(fs_1());
      tmp2 = int1(tmp1, 1);
      return power.Pc(0, tmp2)
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static sqrtPs(fss8) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let qs, scrut, param0, param1, fs_2, gss5, scrut1, param01, param11, fs_3, tmp1, tmp2, tmp3;
      scrut = NofibPrelude.force(fss8);
      if (scrut instanceof power.Pz.class) {
        return power.Pz
      } else if (scrut instanceof power.Pc.class) {
        param0 = scrut.f;
        param1 = scrut.s;
        if (param0 === 0) {
          gss5 = param1;
          scrut1 = NofibPrelude.force(gss5);
          if (scrut1 instanceof power.Pc.class) {
            param01 = scrut1.f;
            param11 = scrut1.s;
            if (param01 === 0) {
              fs_3 = param11;
              tmp1 = power.sqrtPs(fs_3);
              return power.Pc(0, tmp1)
            } else {
              throw new globalThis.Error("match error");
            }
          } else {
            throw new globalThis.Error("match error");
          }
        } else if (param0 === 1) {
          fs_2 = param1;
          qs = function qs() {
            let tmp4, lambda1;
            lambda1 = (undefined, function () {
              let tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, lambda2;
              tmp5 = power.fromIntegerPs(1);
              lambda2 = (undefined, function () {
                return power.Pc(1, fs_2)
              });
              tmp6 = NofibPrelude.lazy(lambda2);
              tmp7 = power.deriv(tmp6);
              tmp8 = qs();
              tmp9 = power.dotMultSndLz(2, tmp8);
              tmp10 = power.divPs(tmp7, tmp9);
              tmp11 = power.integral(tmp10);
              return power.addPs(tmp5, tmp11)
            });
            tmp4 = lambda1;
            return NofibPrelude.lazy(tmp4)
          };
          tmp2 = qs();
          tmp3 = NofibPrelude.force(tmp2);
          return NofibPrelude.force(tmp3)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static ts() {
    let tmp, lambda;
    lambda = (undefined, function () {
      let tmp1, tmp2, tmp3;
      tmp1 = power.ts();
      tmp2 = power.ts();
      tmp3 = power.multPs(tmp1, tmp2);
      return power.Pc(1, tmp3)
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static tree() {
    let tmp, lambda;
    lambda = (undefined, function () {
      let tmp1, tmp2, tmp3, lambda1;
      tmp1 = power.list();
      lambda1 = (undefined, function () {
        return power.tree()
      });
      tmp2 = NofibPrelude.lazy(lambda1);
      tmp3 = power.composeSndLz_(tmp1, tmp2);
      return power.Pc(0, tmp3)
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static cosx() {
    let tmp, tmp1, tmp2, lambda;
    lambda = (undefined, function () {
      let tmp3, lambda1;
      lambda1 = (undefined, function () {
        return power.Pz
      });
      tmp3 = NofibPrelude.lazy(lambda1);
      return power.Pc(1, tmp3)
    });
    tmp = NofibPrelude.lazy(lambda);
    tmp1 = power.integralLz(power.cosx);
    tmp2 = power.integral(tmp1);
    return power.minusPs(tmp, tmp2)
  } 
  static sinx() {
    let tmp, tmp1, tmp2, lambda;
    lambda = (undefined, function () {
      let tmp3, lambda1;
      lambda1 = (undefined, function () {
        return power.Pz
      });
      tmp3 = NofibPrelude.lazy(lambda1);
      return power.Pc(1, tmp3)
    });
    tmp = NofibPrelude.lazy(lambda);
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
