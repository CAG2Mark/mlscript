import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let cichelli1;
cichelli1 = class cichelli {
  static #keys;
  static #numberofkeys;
  static #freqtab;
  static #maxval;
  static {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, lambda;
    tmp = NofibPrelude.nofibStringToList("case");
    tmp1 = NofibPrelude.nofibStringToList("class");
    tmp2 = NofibPrelude.nofibStringToList("data");
    tmp3 = NofibPrelude.nofibStringToList("default");
    tmp4 = NofibPrelude.nofibStringToList("deriving");
    tmp5 = NofibPrelude.nofibStringToList("else");
    tmp6 = NofibPrelude.nofibStringToList("hiding");
    tmp7 = NofibPrelude.nofibStringToList("if");
    tmp8 = NofibPrelude.nofibStringToList("import");
    tmp9 = NofibPrelude.nofibStringToList("in");
    tmp10 = NofibPrelude.nofibStringToList("infix");
    tmp11 = NofibPrelude.nofibStringToList("infixl");
    tmp12 = NofibPrelude.nofibStringToList("instance");
    tmp13 = NofibPrelude.nofibStringToList("interface");
    tmp14 = NofibPrelude.nofibStringToList("let");
    tmp15 = NofibPrelude.nofibStringToList("module");
    tmp16 = NofibPrelude.nofibStringToList("of");
    tmp17 = NofibPrelude.nofibStringToList("renaming");
    tmp18 = NofibPrelude.nofibStringToList("then");
    tmp19 = NofibPrelude.nofibStringToList("to");
    tmp20 = NofibPrelude.nofibStringToList("type");
    tmp21 = NofibPrelude.nofibStringToList("where");
    tmp22 = NofibPrelude.Cons(tmp21, NofibPrelude.Nil);
    tmp23 = NofibPrelude.Cons(tmp20, tmp22);
    tmp24 = NofibPrelude.Cons(tmp19, tmp23);
    tmp25 = NofibPrelude.Cons(tmp18, tmp24);
    tmp26 = NofibPrelude.Cons(tmp17, tmp25);
    tmp27 = NofibPrelude.Cons(tmp16, tmp26);
    tmp28 = NofibPrelude.Cons(tmp15, tmp27);
    tmp29 = NofibPrelude.Cons(tmp14, tmp28);
    tmp30 = NofibPrelude.Cons(tmp13, tmp29);
    tmp31 = NofibPrelude.Cons(tmp12, tmp30);
    tmp32 = NofibPrelude.Cons(tmp11, tmp31);
    tmp33 = NofibPrelude.Cons(tmp10, tmp32);
    tmp34 = NofibPrelude.Cons(tmp9, tmp33);
    tmp35 = NofibPrelude.Cons(tmp8, tmp34);
    tmp36 = NofibPrelude.Cons(tmp7, tmp35);
    tmp37 = NofibPrelude.Cons(tmp6, tmp36);
    tmp38 = NofibPrelude.Cons(tmp5, tmp37);
    tmp39 = NofibPrelude.Cons(tmp4, tmp38);
    tmp40 = NofibPrelude.Cons(tmp3, tmp39);
    tmp41 = NofibPrelude.Cons(tmp2, tmp40);
    tmp42 = NofibPrelude.Cons(tmp1, tmp41);
    tmp43 = NofibPrelude.Cons(tmp, tmp42);
    cichelli.#keys = tmp43;
    this.K = function K(s1, c11, c21, i1) {
      return new K.class(s1, c11, c21, i1);
    };
    this.K.class = class K {
      constructor(s, c1, c2, i) {
        this.s = s;
        this.c1 = c1;
        this.c2 = c2;
        this.i = i;
      }
      toString() { return "K(" + globalThis.Predef.render(this.s) + ", " + globalThis.Predef.render(this.c1) + ", " + globalThis.Predef.render(this.c2) + ", " + globalThis.Predef.render(this.i) + ")"; }
    };
    this.H = function H(f1, s1, ls1) {
      return new H.class(f1, s1, ls1);
    };
    this.H.class = class H {
      constructor(f, s, ls) {
        this.f = f;
        this.s = s;
        this.ls = ls;
      }
      toString() { return "H(" + globalThis.Predef.render(this.f) + ", " + globalThis.Predef.render(this.s) + ", " + globalThis.Predef.render(this.ls) + ")"; }
    };
    tmp44 = NofibPrelude.listLen(cichelli.#keys);
    cichelli.#numberofkeys = tmp44;
    tmp45 = cichelli.attribkeys(cichelli.#keys);
    tmp46 = NofibPrelude.map(cichelli.ends, tmp45);
    tmp47 = NofibPrelude.concat(tmp46);
    tmp48 = cichelli.histo(tmp47);
    cichelli.#freqtab = tmp48;
    tmp49 = NofibPrelude.listLen(cichelli.#freqtab);
    cichelli.#maxval = tmp49;
    this.Status = class Status {
      constructor() {}
      toString() { return "Status"; }
    };
    this.NotEver = function NotEver(i1) {
      return new NotEver.class(i1);
    };
    this.NotEver.class = class NotEver extends cichelli.Status {
      constructor(i) {
        super();
        this.i = i;
      }
      toString() { return "NotEver(" + globalThis.Predef.render(this.i) + ")"; }
    };
    this.YesIts = function YesIts(i1, t1) {
      return new YesIts.class(i1, t1);
    };
    this.YesIts.class = class YesIts extends cichelli.Status {
      constructor(i, t) {
        super();
        this.i = i;
        this.t = t;
      }
      toString() { return "YesIts(" + globalThis.Predef.render(this.i) + ", " + globalThis.Predef.render(this.t) + ")"; }
    };
    lambda = (undefined, function () {
      let tmp50;
      tmp50 = cichelli.prog(6);
      return runtime.safeCall(tmp50.toString())
    });
    BenchmarkPrelude.benchmark(lambda)
  }
  static enumFromTo_lz(a, b) {
    let tmp, lambda;
    lambda = (undefined, function () {
      let scrut, tmp1, tmp2;
      scrut = a <= b;
      if (scrut === true) {
        tmp1 = a + 1;
        tmp2 = cichelli.enumFromTo_lz(tmp1, b);
        return NofibPrelude.LzCons(a, tmp2)
      } else {
        return NofibPrelude.LzNil
      }
    });
    tmp = lambda;
    return NofibPrelude.lazy(tmp)
  } 
  static last(ls) {
    let go, param0, param1, h, t;
    go = function go(h1, t1) {
      let param01, param11, head, t2;
      if (t1 instanceof NofibPrelude.Nil.class) {
        return h1
      } else if (t1 instanceof NofibPrelude.Cons.class) {
        param01 = t1.head;
        param11 = t1.tail;
        head = param01;
        t2 = param11;
        return go(head, t2)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      h = param0;
      t = param1;
      return go(h, t)
    } else {
      throw globalThis.Error("last: empty list");
    }
  } 
  static ends(k) {
    let param0, param1, param2, param3, a1, z, tmp;
    if (k instanceof cichelli.K.class) {
      param0 = k.s;
      param1 = k.c1;
      param2 = k.c2;
      param3 = k.i;
      a1 = param1;
      z = param2;
      tmp = NofibPrelude.Cons(z, NofibPrelude.Nil);
      return NofibPrelude.Cons(a1, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static assoc(x, yz) {
    let param0, param1, first1, first0, y, z, yzs, scrut;
    if (yz instanceof NofibPrelude.Cons.class) {
      param0 = yz.head;
      param1 = yz.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        y = first0;
        z = first1;
        yzs = param1;
        scrut = x === y;
        if (scrut === true) {
          return z
        } else {
          return cichelli.assoc(x, yzs)
        }
      } else {
        throw globalThis.Error("assoc: not found");
      }
    } else {
      throw globalThis.Error("assoc: not found");
    }
  } 
  static assocm(x1, yz1) {
    let param0, param1, first1, first0, y, z, yzs, scrut;
    if (yz1 instanceof NofibPrelude.Cons.class) {
      param0 = yz1.head;
      param1 = yz1.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        y = first0;
        z = first1;
        yzs = param1;
        scrut = x1 === y;
        if (scrut === true) {
          return NofibPrelude.Some(z)
        } else {
          return cichelli.assocm(x1, yzs)
        }
      } else {
        return NofibPrelude.None
      }
    } else {
      return NofibPrelude.None
    }
  } 
  static histins(x2, yns) {
    let param0, param1, first1, first0, y, n, yns1, scrut, tmp, tmp1;
    if (yns instanceof NofibPrelude.Cons.class) {
      param0 = yns.head;
      param1 = yns.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        y = first0;
        n = first1;
        yns1 = param1;
        scrut = x2 === y;
        if (scrut === true) {
          tmp = n + 1;
          return NofibPrelude.Cons([
            y,
            tmp
          ], yns1)
        } else {
          tmp1 = cichelli.histins(x2, yns1);
          return NofibPrelude.Cons([
            y,
            n
          ], tmp1)
        }
      } else {
        return NofibPrelude.Cons([
          x2,
          1
        ], NofibPrelude.Nil)
      }
    } else {
      return NofibPrelude.Cons([
        x2,
        1
      ], NofibPrelude.Nil)
    }
  } 
  static histo(ls1) {
    return NofibPrelude.foldr(cichelli.histins, NofibPrelude.Nil, ls1)
  } 
  static subset(xs, ys) {
    let lambda;
    lambda = (undefined, function (x3) {
      return NofibPrelude.inList(x3, ys)
    });
    return NofibPrelude.all(lambda, xs)
  } 
  static union(xs1, ys1) {
    let lscomp, tmp;
    lscomp = function lscomp(ls2) {
      let param0, param1, h, t, scrut, tmp1, tmp2;
      if (ls2 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls2 instanceof NofibPrelude.Cons.class) {
        param0 = ls2.head;
        param1 = ls2.tail;
        h = param0;
        t = param1;
        tmp1 = NofibPrelude.inList(h, xs1);
        scrut = BenchmarkPrelude.not(tmp1);
        if (scrut === true) {
          tmp2 = lscomp(t);
          return NofibPrelude.Cons(h, tmp2)
        } else {
          return lscomp(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = lscomp(ys1);
    return NofibPrelude.append(xs1, tmp)
  } 
  static attribkeys(ks) {
    let tmp, lambda;
    lambda = (undefined, function (k1) {
      let tmp1, tmp2, tmp3;
      tmp1 = NofibPrelude.head(k1);
      tmp2 = cichelli.last(k1);
      tmp3 = NofibPrelude.listLen(k1);
      return cichelli.K(k1, tmp1, tmp2, tmp3)
    });
    tmp = lambda;
    return NofibPrelude.map(tmp, ks)
  } 
  static minm(x3, y) {
    let param0, x4;
    if (x3 instanceof NofibPrelude.None.class) {
      return y
    } else if (x3 instanceof NofibPrelude.Some.class) {
      param0 = x3.x;
      x4 = param0;
      return NofibPrelude.min(x4, y)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static maxm(x4, y1) {
    let param0, x5;
    if (x4 instanceof NofibPrelude.None.class) {
      return y1
    } else if (x4 instanceof NofibPrelude.Some.class) {
      param0 = x4.x;
      x5 = param0;
      return NofibPrelude.max(x5, y1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static hash(cvs, k1) {
    let param0, param1, param2, param3, a1, z, n, tmp, tmp1, tmp2;
    if (k1 instanceof cichelli.K.class) {
      param0 = k1.s;
      param1 = k1.c1;
      param2 = k1.c2;
      param3 = k1.i;
      a1 = param1;
      z = param2;
      n = param3;
      tmp = cichelli.assoc(a1, cvs);
      tmp1 = n + tmp;
      tmp2 = cichelli.assoc(z, cvs);
      return tmp1 + tmp2
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static select(p, x5, ts_fs) {
    let first1, first0, ts, fs1, scrut, tmp, tmp1;
    if (globalThis.Array.isArray(ts_fs) && ts_fs.length === 2) {
      first0 = ts_fs[0];
      first1 = ts_fs[1];
      ts = first0;
      fs1 = first1;
      scrut = runtime.safeCall(p(x5));
      if (scrut === true) {
        tmp = NofibPrelude.Cons(x5, ts);
        return [
          tmp,
          fs1
        ]
      } else {
        tmp1 = NofibPrelude.Cons(x5, fs1);
        return [
          ts,
          tmp1
        ]
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static partition_(p1, ls2) {
    let lambda;
    lambda = (undefined, function (x6, y2) {
      return cichelli.select(p1, x6, y2)
    });
    return NofibPrelude.foldr(lambda, [
      NofibPrelude.Nil,
      NofibPrelude.Nil
    ], ls2)
  } 
  static freqsorted(x6) {
    return x6
  } 
  static blocked_(ds, ls3) {
    let param0, param1, k2, ks1, ds_, scrut, first1, first0, det, rest, tmp, tmp1, tmp2, tmp3, lambda;
    if (ls3 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls3 instanceof NofibPrelude.Cons.class) {
      param0 = ls3.head;
      param1 = ls3.tail;
      k2 = param0;
      ks1 = param1;
      tmp = cichelli.ends(k2);
      tmp1 = cichelli.union(ds, tmp);
      ds_ = tmp1;
      lambda = (undefined, function (x7) {
        let tmp4;
        tmp4 = cichelli.ends(x7);
        return cichelli.subset(tmp4, ds_)
      });
      scrut = cichelli.partition_(lambda, ks1);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        det = first0;
        rest = first1;
        tmp2 = cichelli.blocked_(ds_, rest);
        tmp3 = NofibPrelude.append(det, tmp2);
        return NofibPrelude.Cons(k2, tmp3)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static blocked(ls4) {
    return cichelli.blocked_(NofibPrelude.Nil, ls4)
  } 
  static hinsert(h, hh) {
    let param0, param1, param2, lo, hi, hs, lo_, hi_, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    if (hh instanceof cichelli.H.class) {
      param0 = hh.f;
      param1 = hh.s;
      param2 = hh.ls;
      lo = param0;
      hi = param1;
      hs = param2;
      tmp = cichelli.minm(lo, h);
      lo_ = tmp;
      tmp1 = cichelli.maxm(hi, h);
      hi_ = tmp1;
      tmp2 = NofibPrelude.inList(h, hs);
      tmp3 = 1 + hi_;
      tmp4 = tmp3 - lo_;
      tmp5 = tmp4 > cichelli.#numberofkeys;
      scrut = tmp2 || tmp5;
      if (scrut === true) {
        return NofibPrelude.None
      } else {
        tmp6 = NofibPrelude.Some(lo_);
        tmp7 = NofibPrelude.Some(hi_);
        tmp8 = NofibPrelude.Cons(h, hs);
        tmp9 = cichelli.H(tmp6, tmp7, tmp8);
        return NofibPrelude.Some(tmp9)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static first(k2, ls5) {
    let scrut, param0, param1, a1, l, param01, leaves, param02, param11, leaves1, y2, tmp, tmp1;
    scrut = NofibPrelude.force(ls5);
    if (scrut instanceof NofibPrelude.LzNil.class) {
      return cichelli.NotEver(k2)
    } else if (scrut instanceof NofibPrelude.LzCons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      a1 = param0;
      l = param1;
      if (a1 instanceof cichelli.YesIts.class) {
        param02 = a1.i;
        param11 = a1.t;
        leaves1 = param02;
        y2 = param11;
        tmp = k2 + leaves1;
        return cichelli.YesIts(tmp, y2)
      } else if (a1 instanceof cichelli.NotEver.class) {
        param01 = a1.i;
        leaves = param01;
        tmp1 = k2 + leaves;
        return cichelli.first(tmp1, l)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static firstSuccess(f, possibles) {
    let tmp;
    tmp = NofibPrelude.map_lz(f, possibles);
    return cichelli.first(0, tmp)
  } 
  static findhash_(keyHashSet, charAssocs, ks1) {
    let lscomp1, tryy, param0, param1, param01, param11, param2, param3, s, a1, z, n, ks2, scrut, first1, first0, param02, ac, param03, zc, ac1, zc1, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, lambda, lambda1, lambda2, lambda3;
    if (ks1 instanceof NofibPrelude.Nil.class) {
      return cichelli.YesIts(1, charAssocs)
    } else if (ks1 instanceof NofibPrelude.Cons.class) {
      param0 = ks1.head;
      param1 = ks1.tail;
      if (param0 instanceof cichelli.K.class) {
        param01 = param0.s;
        param11 = param0.c1;
        param2 = param0.c2;
        param3 = param0.i;
        s = param01;
        a1 = param11;
        z = param2;
        n = param3;
        ks2 = param1;
        tryy = function tryy(newAssocs) {
          let newCharAssocs, scrut2, param04, newKeyHashSet, tmp8, tmp9, tmp10;
          tmp8 = NofibPrelude.append(newAssocs, charAssocs);
          newCharAssocs = tmp8;
          tmp9 = cichelli.K(s, a1, z, n);
          tmp10 = cichelli.hash(newCharAssocs, tmp9);
          scrut2 = cichelli.hinsert(tmp10, keyHashSet);
          if (scrut2 instanceof NofibPrelude.None.class) {
            return cichelli.NotEver(1)
          } else if (scrut2 instanceof NofibPrelude.Some.class) {
            param04 = scrut2.x;
            newKeyHashSet = param04;
            return cichelli.findhash_(newKeyHashSet, newCharAssocs, ks2)
          } else {
            throw new globalThis.Error("match error");
          }
        };
        tmp = cichelli.assocm(a1, charAssocs);
        tmp1 = cichelli.assocm(z, charAssocs);
        scrut = [
          tmp,
          tmp1
        ];
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first0 = scrut[0];
          first1 = scrut[1];
          if (first0 instanceof NofibPrelude.None.class) {
            if (first1 instanceof NofibPrelude.None.class) {
              scrut1 = a1 === z;
              if (scrut1 === true) {
                tmp2 = cichelli.enumFromTo_lz(0, cichelli.#maxval);
                lambda = (undefined, function (m) {
                  let tmp8;
                  tmp8 = NofibPrelude.Cons([
                    a1,
                    m
                  ], NofibPrelude.Nil);
                  return tryy(tmp8)
                });
                return cichelli.firstSuccess(lambda, tmp2)
              } else {
                lscomp1 = function lscomp1(ls11) {
                  let tmp8, lambda4;
                  lambda4 = (undefined, function () {
                    let lscomp2, scrut2, param04, param12, m, ms, tmp9, tmp10;
                    scrut2 = NofibPrelude.force(ls11);
                    if (scrut2 instanceof NofibPrelude.LzNil.class) {
                      return NofibPrelude.LzNil
                    } else if (scrut2 instanceof NofibPrelude.LzCons.class) {
                      param04 = scrut2.head;
                      param12 = scrut2.tail;
                      m = param04;
                      ms = param12;
                      lscomp2 = function lscomp2(ls21) {
                        let scrut3, param05, param13, n1, ns, lambda5;
                        scrut3 = NofibPrelude.force(ls21);
                        if (scrut3 instanceof NofibPrelude.LzNil.class) {
                          return lscomp1(ms)
                        } else if (scrut3 instanceof NofibPrelude.LzCons.class) {
                          param05 = scrut3.head;
                          param13 = scrut3.tail;
                          n1 = param05;
                          ns = param13;
                          lambda5 = (undefined, function () {
                            let tmp11;
                            tmp11 = lscomp2(ns);
                            return NofibPrelude.LzCons([
                              m,
                              n1
                            ], tmp11)
                          });
                          return NofibPrelude.lazy(lambda5)
                        } else {
                          throw new globalThis.Error("match error");
                        }
                      };
                      tmp9 = cichelli.enumFromTo_lz(0, cichelli.#maxval);
                      tmp10 = lscomp2(tmp9);
                      return NofibPrelude.force(tmp10)
                    } else {
                      throw new globalThis.Error("match error");
                    }
                  });
                  tmp8 = lambda4;
                  return NofibPrelude.lazy(tmp8)
                };
                lambda1 = (undefined, function (caseScrut) {
                  let first11, first01, m, n1, tmp8, tmp9;
                  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                    first01 = caseScrut[0];
                    first11 = caseScrut[1];
                    m = first01;
                    n1 = first11;
                    tmp8 = NofibPrelude.Cons([
                      z,
                      n1
                    ], NofibPrelude.Nil);
                    tmp9 = NofibPrelude.Cons([
                      a1,
                      m
                    ], tmp8);
                    return tryy(tmp9)
                  } else {
                    throw new globalThis.Error("match error");
                  }
                });
                tmp3 = lambda1;
                tmp4 = cichelli.enumFromTo_lz(0, cichelli.#maxval);
                tmp5 = lscomp1(tmp4);
                return cichelli.firstSuccess(tmp3, tmp5)
              }
            } else if (first1 instanceof NofibPrelude.Some.class) {
              param03 = first1.x;
              zc1 = param03;
              tmp6 = cichelli.enumFromTo_lz(0, cichelli.#maxval);
              lambda2 = (undefined, function (m) {
                let tmp8;
                tmp8 = NofibPrelude.Cons([
                  a1,
                  m
                ], NofibPrelude.Nil);
                return tryy(tmp8)
              });
              return cichelli.firstSuccess(lambda2, tmp6)
            } else {
              throw new globalThis.Error("match error");
            }
          } else if (first0 instanceof NofibPrelude.Some.class) {
            param02 = first0.x;
            ac1 = param02;
            ac = param02;
            if (first1 instanceof NofibPrelude.None.class) {
              tmp7 = cichelli.enumFromTo_lz(0, cichelli.#maxval);
              lambda3 = (undefined, function (n1) {
                let tmp8;
                tmp8 = NofibPrelude.Cons([
                  z,
                  n1
                ], NofibPrelude.Nil);
                return tryy(tmp8)
              });
              return cichelli.firstSuccess(lambda3, tmp7)
            } else if (first1 instanceof NofibPrelude.Some.class) {
              param03 = first1.x;
              zc = param03;
              return tryy(NofibPrelude.Nil)
            } else {
              throw new globalThis.Error("match error");
            }
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static findhash(keys) {
    let tmp;
    tmp = cichelli.H(NofibPrelude.None, NofibPrelude.None, NofibPrelude.Nil);
    return cichelli.findhash_(tmp, NofibPrelude.Nil, keys)
  } 
  static freq(c) {
    return cichelli.assoc(c, cichelli.#freqtab)
  } 
  static morefreq(k11, k21) {
    let param0, param1, param2, param3, a1, x7, param01, param11, param21, param31, b1, y2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    if (k11 instanceof cichelli.K.class) {
      param0 = k11.s;
      param1 = k11.c1;
      param2 = k11.c2;
      param3 = k11.i;
      a1 = param1;
      x7 = param2;
      if (k21 instanceof cichelli.K.class) {
        param01 = k21.s;
        param11 = k21.c1;
        param21 = k21.c2;
        param31 = k21.i;
        b1 = param11;
        y2 = param21;
        tmp = cichelli.freq(a1);
        tmp1 = cichelli.freq(x7);
        tmp2 = tmp + tmp1;
        tmp3 = cichelli.freq(b1);
        tmp4 = cichelli.freq(y2);
        tmp5 = tmp3 + tmp4;
        return tmp2 > tmp5
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static cichelli(n) {
    let attribkeys_, hashkeys, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = NofibPrelude.intMod(n, 2);
    tmp1 = NofibPrelude.take(tmp, cichelli.#keys);
    tmp2 = NofibPrelude.append(cichelli.#keys, tmp1);
    tmp3 = cichelli.attribkeys(tmp2);
    attribkeys_ = tmp3;
    tmp4 = cichelli.freqsorted(attribkeys_);
    tmp5 = cichelli.blocked(tmp4);
    hashkeys = tmp5;
    return cichelli.findhash(hashkeys)
  } 
  static prog(n1) {
    return cichelli.cichelli(n1)
  }
  static toString() { return "cichelli"; }
};
let cichelli = cichelli1; export default cichelli;
