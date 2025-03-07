import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let firstSuccess, YesIts1, hinsert, union, ends, NotEver1, freq, minm, histo, enumFromTo_lz, maxm, last, assocm, blocked_, assoc, K1, partition_, cichelli_, Status1, prog, histins, attribkeys, select, morefreq, hash, findhash, subset, freqsorted, first, blocked, findhash_, H1, keys, numberofkeys, freqtab, maxval, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, lambda;
enumFromTo_lz = function enumFromTo_lz(a, b) {
  let tmp50, lambda1;
  lambda1 = (undefined, function () {
    let scrut, tmp51, tmp52;
    scrut = a <= b;
    if (scrut === true) {
      tmp51 = a + 1;
      tmp52 = enumFromTo_lz(tmp51, b);
      return NofibPrelude.LzCons(a, tmp52)
    } else {
      return NofibPrelude.LzNil
    }
  });
  tmp50 = lambda1;
  return NofibPrelude.lazy(tmp50)
};
last = function last(ls) {
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
};
ends = function ends(k) {
  let param0, param1, param2, param3, a, z, tmp50;
  if (k instanceof K1.class) {
    param0 = k.s;
    param1 = k.c1;
    param2 = k.c2;
    param3 = k.i;
    a = param1;
    z = param2;
    tmp50 = NofibPrelude.Cons(z, NofibPrelude.Nil);
    return NofibPrelude.Cons(a, tmp50)
  } else {
    throw new globalThis.Error("match error");
  }
};
assoc = function assoc(x, yz) {
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
        return assoc(x, yzs)
      }
    } else {
      throw globalThis.Error("assoc: not found");
    }
  } else {
    throw globalThis.Error("assoc: not found");
  }
};
assocm = function assocm(x, yz) {
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
        return NofibPrelude.Some(z)
      } else {
        return assocm(x, yzs)
      }
    } else {
      return NofibPrelude.None
    }
  } else {
    return NofibPrelude.None
  }
};
histins = function histins(x, yns) {
  let param0, param1, first1, first0, y, n, yns1, scrut, tmp50, tmp51;
  if (yns instanceof NofibPrelude.Cons.class) {
    param0 = yns.head;
    param1 = yns.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      y = first0;
      n = first1;
      yns1 = param1;
      scrut = x === y;
      if (scrut === true) {
        tmp50 = n + 1;
        return NofibPrelude.Cons([
          y,
          tmp50
        ], yns1)
      } else {
        tmp51 = histins(x, yns1);
        return NofibPrelude.Cons([
          y,
          n
        ], tmp51)
      }
    } else {
      return NofibPrelude.Cons([
        x,
        1
      ], NofibPrelude.Nil)
    }
  } else {
    return NofibPrelude.Cons([
      x,
      1
    ], NofibPrelude.Nil)
  }
};
histo = function histo(ls) {
  return NofibPrelude.foldr(histins, NofibPrelude.Nil, ls)
};
subset = function subset(xs, ys) {
  let lambda1;
  lambda1 = (undefined, function (x) {
    return NofibPrelude.inList(x, ys)
  });
  return NofibPrelude.all(lambda1, xs)
};
union = function union(xs, ys) {
  let lscomp, tmp50;
  lscomp = function lscomp(ls) {
    let param0, param1, h, t, scrut, tmp51, tmp52;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      h = param0;
      t = param1;
      tmp51 = NofibPrelude.inList(h, xs);
      scrut = BenchmarkPrelude.not(tmp51);
      if (scrut === true) {
        tmp52 = lscomp(t);
        return NofibPrelude.Cons(h, tmp52)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp50 = lscomp(ys);
  return NofibPrelude.append(xs, tmp50)
};
attribkeys = function attribkeys(ks) {
  let tmp50, lambda1;
  lambda1 = (undefined, function (k) {
    let tmp51, tmp52, tmp53;
    tmp51 = NofibPrelude.head(k);
    tmp52 = last(k);
    tmp53 = NofibPrelude.listLen(k);
    return K1(k, tmp51, tmp52, tmp53)
  });
  tmp50 = lambda1;
  return NofibPrelude.map(tmp50, ks)
};
minm = function minm(x, y) {
  let param0, x1;
  if (x instanceof NofibPrelude.None.class) {
    return y
  } else if (x instanceof NofibPrelude.Some.class) {
    param0 = x.x;
    x1 = param0;
    return NofibPrelude.min(x1, y)
  } else {
    throw new globalThis.Error("match error");
  }
};
maxm = function maxm(x, y) {
  let param0, x1;
  if (x instanceof NofibPrelude.None.class) {
    return y
  } else if (x instanceof NofibPrelude.Some.class) {
    param0 = x.x;
    x1 = param0;
    return NofibPrelude.max(x1, y)
  } else {
    throw new globalThis.Error("match error");
  }
};
hash = function hash(cvs, k) {
  let param0, param1, param2, param3, a, z, n, tmp50, tmp51, tmp52;
  if (k instanceof K1.class) {
    param0 = k.s;
    param1 = k.c1;
    param2 = k.c2;
    param3 = k.i;
    a = param1;
    z = param2;
    n = param3;
    tmp50 = assoc(a, cvs);
    tmp51 = n + tmp50;
    tmp52 = assoc(z, cvs);
    return tmp51 + tmp52
  } else {
    throw new globalThis.Error("match error");
  }
};
select = function select(p, x, ts_fs) {
  let first1, first0, ts, fs, scrut, tmp50, tmp51;
  if (globalThis.Array.isArray(ts_fs) && ts_fs.length === 2) {
    first0 = ts_fs[0];
    first1 = ts_fs[1];
    ts = first0;
    fs = first1;
    scrut = runtime.safeCall(p(x));
    if (scrut === true) {
      tmp50 = NofibPrelude.Cons(x, ts);
      return [
        tmp50,
        fs
      ]
    } else {
      tmp51 = NofibPrelude.Cons(x, fs);
      return [
        ts,
        tmp51
      ]
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
partition_ = function partition_(p, ls) {
  let lambda1;
  lambda1 = (undefined, function (x, y) {
    return select(p, x, y)
  });
  return NofibPrelude.foldr(lambda1, [
    NofibPrelude.Nil,
    NofibPrelude.Nil
  ], ls)
};
freqsorted = function freqsorted(x) {
  return x
};
blocked_ = function blocked_(ds, ls) {
  let param0, param1, k, ks, ds_, scrut, first1, first0, det, rest, tmp50, tmp51, tmp52, tmp53, lambda1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    k = param0;
    ks = param1;
    tmp50 = ends(k);
    tmp51 = NofibPrelude.union(ds, tmp50);
    ds_ = tmp51;
    lambda1 = (undefined, function (x) {
      let tmp54;
      tmp54 = ends(x);
      return subset(tmp54, ds_)
    });
    scrut = partition_(lambda1, ks);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      det = first0;
      rest = first1;
      tmp52 = blocked_(ds_, rest);
      tmp53 = NofibPrelude.append(det, tmp52);
      return NofibPrelude.Cons(k, tmp53)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
blocked = function blocked(ls) {
  return blocked_(NofibPrelude.Nil, ls)
};
hinsert = function hinsert(h, hh) {
  let param0, param1, param2, lo, hi, hs, lo_, hi_, scrut, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59;
  if (hh instanceof H1.class) {
    param0 = hh.f;
    param1 = hh.s;
    param2 = hh.ls;
    lo = param0;
    hi = param1;
    hs = param2;
    tmp50 = minm(lo, h);
    lo_ = tmp50;
    tmp51 = maxm(hi, h);
    hi_ = tmp51;
    tmp52 = NofibPrelude.inList(h, hs);
    tmp53 = 1 + hi_;
    tmp54 = tmp53 - lo_;
    tmp55 = tmp54 > numberofkeys;
    scrut = tmp52 || tmp55;
    if (scrut === true) {
      return NofibPrelude.None
    } else {
      tmp56 = NofibPrelude.Some(lo_);
      tmp57 = NofibPrelude.Some(hi_);
      tmp58 = NofibPrelude.Cons(h, hs);
      tmp59 = H1(tmp56, tmp57, tmp58);
      return NofibPrelude.Some(tmp59)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
first = function first(k, ls) {
  let scrut, param0, param1, a, l, param01, leaves, param02, param11, leaves1, y, tmp50, tmp51;
  scrut = NofibPrelude.force(ls);
  if (scrut instanceof NofibPrelude.LzNil.class) {
    return NotEver1(k)
  } else if (scrut instanceof NofibPrelude.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    a = param0;
    l = param1;
    if (a instanceof YesIts1.class) {
      param02 = a.i;
      param11 = a.t;
      leaves1 = param02;
      y = param11;
      tmp50 = k + leaves1;
      return YesIts1(tmp50, y)
    } else if (a instanceof NotEver1.class) {
      param01 = a.i;
      leaves = param01;
      tmp51 = k + leaves;
      return first(tmp51, l)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
firstSuccess = function firstSuccess(f, possibles) {
  let tmp50;
  tmp50 = NofibPrelude.map_lz(f, possibles);
  return first(0, tmp50)
};
findhash_ = function findhash_(keyHashSet, charAssocs, ks) {
  let lscomp1, tryy, param0, param1, param01, param11, param2, param3, s, a, z, n, ks1, scrut, first1, first0, param02, ac, param03, zc, ac1, zc1, scrut1, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, lambda1, lambda2, lambda3, lambda4;
  if (ks instanceof NofibPrelude.Nil.class) {
    return YesIts1(1, charAssocs)
  } else if (ks instanceof NofibPrelude.Cons.class) {
    param0 = ks.head;
    param1 = ks.tail;
    if (param0 instanceof K1.class) {
      param01 = param0.s;
      param11 = param0.c1;
      param2 = param0.c2;
      param3 = param0.i;
      s = param01;
      a = param11;
      z = param2;
      n = param3;
      ks1 = param1;
      tryy = function tryy(newAssocs) {
        let newCharAssocs, scrut2, param04, newKeyHashSet, tmp58, tmp59, tmp60;
        tmp58 = NofibPrelude.append(newAssocs, charAssocs);
        newCharAssocs = tmp58;
        tmp59 = K1(s, a, z, n);
        tmp60 = hash(newCharAssocs, tmp59);
        scrut2 = hinsert(tmp60, keyHashSet);
        if (scrut2 instanceof NofibPrelude.None.class) {
          return NotEver1(1)
        } else if (scrut2 instanceof NofibPrelude.Some.class) {
          param04 = scrut2.x;
          newKeyHashSet = param04;
          return findhash_(newKeyHashSet, newCharAssocs, ks1)
        } else {
          throw new globalThis.Error("match error");
        }
      };
      tmp50 = assocm(a, charAssocs);
      tmp51 = assocm(z, charAssocs);
      scrut = [
        tmp50,
        tmp51
      ];
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        if (first0 instanceof NofibPrelude.None.class) {
          if (first1 instanceof NofibPrelude.None.class) {
            scrut1 = a === z;
            if (scrut1 === true) {
              tmp52 = enumFromTo_lz(0, maxval);
              lambda1 = (undefined, function (m) {
                let tmp58;
                tmp58 = NofibPrelude.Cons([
                  a,
                  m
                ], NofibPrelude.Nil);
                return tryy(tmp58)
              });
              return firstSuccess(lambda1, tmp52)
            } else {
              lscomp1 = function lscomp1(ls1) {
                let tmp58, lambda5;
                lambda5 = (undefined, function () {
                  let lscomp2, scrut2, param04, param12, m, ms, tmp59, tmp60;
                  scrut2 = NofibPrelude.force(ls1);
                  if (scrut2 instanceof NofibPrelude.LzNil.class) {
                    return NofibPrelude.LzNil
                  } else if (scrut2 instanceof NofibPrelude.LzCons.class) {
                    param04 = scrut2.head;
                    param12 = scrut2.tail;
                    m = param04;
                    ms = param12;
                    lscomp2 = function lscomp2(ls2) {
                      let scrut3, param05, param13, n1, ns, lambda6;
                      scrut3 = NofibPrelude.force(ls2);
                      if (scrut3 instanceof NofibPrelude.LzNil.class) {
                        return lscomp1(ms)
                      } else if (scrut3 instanceof NofibPrelude.LzCons.class) {
                        param05 = scrut3.head;
                        param13 = scrut3.tail;
                        n1 = param05;
                        ns = param13;
                        lambda6 = (undefined, function () {
                          let tmp61;
                          tmp61 = lscomp2(ns);
                          return NofibPrelude.LzCons([
                            m,
                            n1
                          ], tmp61)
                        });
                        return NofibPrelude.lazy(lambda6)
                      } else {
                        throw new globalThis.Error("match error");
                      }
                    };
                    tmp59 = enumFromTo_lz(0, maxval);
                    tmp60 = lscomp2(tmp59);
                    return NofibPrelude.force(tmp60)
                  } else {
                    throw new globalThis.Error("match error");
                  }
                });
                tmp58 = lambda5;
                return NofibPrelude.lazy(tmp58)
              };
              lambda2 = (undefined, function (caseScrut) {
                let first11, first01, m, n1, tmp58, tmp59;
                if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                  first01 = caseScrut[0];
                  first11 = caseScrut[1];
                  m = first01;
                  n1 = first11;
                  tmp58 = NofibPrelude.Cons([
                    z,
                    n1
                  ], NofibPrelude.Nil);
                  tmp59 = NofibPrelude.Cons([
                    a,
                    m
                  ], tmp58);
                  return tryy(tmp59)
                } else {
                  throw new globalThis.Error("match error");
                }
              });
              tmp53 = lambda2;
              tmp54 = enumFromTo_lz(0, maxval);
              tmp55 = lscomp1(tmp54);
              return firstSuccess(tmp53, tmp55)
            }
          } else if (first1 instanceof NofibPrelude.Some.class) {
            param03 = first1.x;
            zc1 = param03;
            tmp56 = enumFromTo_lz(0, maxval);
            lambda3 = (undefined, function (m) {
              let tmp58;
              tmp58 = NofibPrelude.Cons([
                a,
                m
              ], NofibPrelude.Nil);
              return tryy(tmp58)
            });
            return firstSuccess(lambda3, tmp56)
          } else {
            throw new globalThis.Error("match error");
          }
        } else if (first0 instanceof NofibPrelude.Some.class) {
          param02 = first0.x;
          ac1 = param02;
          ac = param02;
          if (first1 instanceof NofibPrelude.None.class) {
            tmp57 = enumFromTo_lz(0, maxval);
            lambda4 = (undefined, function (n1) {
              let tmp58;
              tmp58 = NofibPrelude.Cons([
                z,
                n1
              ], NofibPrelude.Nil);
              return tryy(tmp58)
            });
            return firstSuccess(lambda4, tmp57)
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
};
findhash = function findhash(keys1) {
  let tmp50;
  tmp50 = H1(NofibPrelude.None, NofibPrelude.None, NofibPrelude.Nil);
  return findhash_(tmp50, NofibPrelude.Nil, keys1)
};
freq = function freq(c) {
  return assoc(c, freqtab)
};
morefreq = function morefreq(k1, k2) {
  let param0, param1, param2, param3, a, x, param01, param11, param21, param31, b, y, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55;
  if (k1 instanceof K1.class) {
    param0 = k1.s;
    param1 = k1.c1;
    param2 = k1.c2;
    param3 = k1.i;
    a = param1;
    x = param2;
    if (k2 instanceof K1.class) {
      param01 = k2.s;
      param11 = k2.c1;
      param21 = k2.c2;
      param31 = k2.i;
      b = param11;
      y = param21;
      tmp50 = freq(a);
      tmp51 = freq(x);
      tmp52 = tmp50 + tmp51;
      tmp53 = freq(b);
      tmp54 = freq(y);
      tmp55 = tmp53 + tmp54;
      return tmp52 > tmp55
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
cichelli_ = function cichelli_(n) {
  let attribkeys_, hashkeys, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55;
  tmp50 = NofibPrelude.intMod(n, 2);
  tmp51 = NofibPrelude.take(tmp50, keys);
  tmp52 = NofibPrelude.append(keys, tmp51);
  tmp53 = attribkeys(tmp52);
  attribkeys_ = tmp53;
  tmp54 = freqsorted(attribkeys_);
  tmp55 = blocked(tmp54);
  hashkeys = tmp55;
  return findhash(hashkeys)
};
prog = function prog(n) {
  return cichelli_(n)
};
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
keys = tmp43;
K1 = function K(s1, c11, c21, i1) {
  return new K.class(s1, c11, c21, i1);
};
K1.class = class K {
  constructor(s, c1, c2, i) {
    this.s = s;
    this.c1 = c1;
    this.c2 = c2;
    this.i = i;
  }
  toString() { return "K(" + globalThis.Predef.render(this.s) + ", " + globalThis.Predef.render(this.c1) + ", " + globalThis.Predef.render(this.c2) + ", " + globalThis.Predef.render(this.i) + ")"; }
};
H1 = function H(f1, s1, ls1) {
  return new H.class(f1, s1, ls1);
};
H1.class = class H {
  constructor(f, s, ls) {
    this.f = f;
    this.s = s;
    this.ls = ls;
  }
  toString() { return "H(" + globalThis.Predef.render(this.f) + ", " + globalThis.Predef.render(this.s) + ", " + globalThis.Predef.render(this.ls) + ")"; }
};
tmp44 = NofibPrelude.listLen(keys);
numberofkeys = tmp44;
tmp45 = attribkeys(keys);
tmp46 = NofibPrelude.map(ends, tmp45);
tmp47 = NofibPrelude.concat(tmp46);
tmp48 = histo(tmp47);
freqtab = tmp48;
tmp49 = NofibPrelude.listLen(freqtab);
maxval = tmp49;
Status1 = class Status {
  constructor() {}
  toString() { return "Status"; }
};
NotEver1 = function NotEver(i1) {
  return new NotEver.class(i1);
};
NotEver1.class = class NotEver extends Status1 {
  constructor(i) {
    super();
    this.i = i;
  }
  toString() { return "NotEver(" + globalThis.Predef.render(this.i) + ")"; }
};
YesIts1 = function YesIts(i1, t1) {
  return new YesIts.class(i1, t1);
};
YesIts1.class = class YesIts extends Status1 {
  constructor(i, t) {
    super();
    this.i = i;
    this.t = t;
  }
  toString() { return "YesIts(" + globalThis.Predef.render(this.i) + ", " + globalThis.Predef.render(this.t) + ")"; }
};
lambda = (undefined, function () {
  let tmp50;
  tmp50 = prog(6);
  return runtime.safeCall(tmp50.toString())
});
BenchmarkPrelude.benchmark(lambda)