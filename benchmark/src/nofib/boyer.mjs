import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let EXP1, NOT1, U1, ERROR1, rewrite_with_lemmas, CONSP1, FALSE1, IF1, D1, Term1, LISTP1, tautologyp, X1, falsep, REVERSE1, Id1, find, ZEROP1, tautp, OR1, apply_subst, TRUE1, Var1, termLsEq, MEMBER1, rewrite_with_lemmas_helper, termEq, GREATEREQP1, Y1, LESSEQP1, SUB11, PLUS1, DIFFERENCE1, F1, GCD1, ADD11, A1, QUOTIENT1, test0, APPEND1, REMAINDER1, GREATERP1, CONS1, TWO1, NIL1, truep, LENGTH1, B1, ONE1, rewrite, one_way_unify1_lst, C1, IMPLIES1, termInList, LESSP1, W1, EQUAL1, FOUR1, IFF1, testBoyer_nofib, DIVIDES1, ZERO1, EVEN1, one_way_unify1, NLISTP1, AND1, NILP1, ODD1, one_way_unify, TIMES1, Z1, Fun1, lambda;
termLsEq = function termLsEq(h1t1, h2t2) {
  let param0, param1, h1, t1, param01, param11, h2, t2, scrut;
  if (h1t1 instanceof NofibPrelude.Cons.class) {
    param0 = h1t1.head;
    param1 = h1t1.tail;
    h1 = param0;
    t1 = param1;
    if (h2t2 instanceof NofibPrelude.Cons.class) {
      param01 = h2t2.head;
      param11 = h2t2.tail;
      h2 = param01;
      t2 = param11;
      scrut = termEq(h1, h2);
      if (scrut === true) {
        return termLsEq(t1, t2)
      } else {
        return false
      }
    } else {
      return true
    }
  } else {
    return true
  }
};
termEq = function termEq(t1, t2) {
  let param0, param1, param2, f1, ts1, param01, param11, param21, f2, ts2, scrut, scrut1, param02, i1, param03, i2;
  if (t1 instanceof Var1.class) {
    param02 = t1.i;
    i1 = param02;
    if (t2 instanceof Var1.class) {
      param03 = t2.i;
      i2 = param03;
      return i1 === i2
    } else {
      return false
    }
  } else if (t1 instanceof Fun1.class) {
    param0 = t1.i;
    param1 = t1.t;
    param2 = t1.l;
    f1 = param0;
    ts1 = param1;
    if (t2 instanceof Fun1.class) {
      param01 = t2.i;
      param11 = t2.t;
      param21 = t2.l;
      f2 = param01;
      ts2 = param11;
      scrut = f1 === f2;
      if (scrut === true) {
        scrut1 = termLsEq(ts1, ts2);
        if (scrut1 === true) {
          return true
        } else {
          return false
        }
      } else {
        return false
      }
    } else {
      return false
    }
  } else {
    return false
  }
};
termInList = function termInList(term, ht) {
  let param0, param1, h, t, scrut;
  if (ht instanceof NofibPrelude.Cons.class) {
    param0 = ht.head;
    param1 = ht.tail;
    h = param0;
    t = param1;
    scrut = termEq(term, h);
    if (scrut === true) {
      return true
    } else {
      return termInList(term, t)
    }
  } else if (ht instanceof NofibPrelude.Nil.class) {
    return false
  } else {
    throw new globalThis.Error("match error");
  }
};
find = function find(vid, ls) {
  let param0, param1, first1, first0, vid2, val2, bs, scrut;
  if (ls instanceof NofibPrelude.Nil.class) {
    return [
      false,
      ERROR1
    ]
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      vid2 = first0;
      val2 = first1;
      bs = param1;
      scrut = vid === vid2;
      if (scrut === true) {
        return [
          true,
          val2
        ]
      } else {
        return find(vid, bs)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
one_way_unify1 = function one_way_unify1(term1, term2, subst) {
  let param0, param1, param2, f1, as1, param01, param11, param21, f2, as2, scrut, param02, vid2, scrut1, first1, first0, found, v2, tmp, tmp1;
  if (term2 instanceof Var1.class) {
    param02 = term2.i;
    vid2 = param02;
    scrut1 = find(vid2, subst);
    if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
      first0 = scrut1[0];
      first1 = scrut1[1];
      found = first0;
      v2 = first1;
      if (found === true) {
        tmp = termEq(term1, v2);
        return [
          tmp,
          subst
        ]
      } else {
        tmp1 = NofibPrelude.Cons([
          vid2,
          term1
        ], subst);
        return [
          true,
          tmp1
        ]
      }
    } else {
      if (term1 instanceof Fun1.class) {
        param0 = term1.i;
        param1 = term1.t;
        param2 = term1.l;
        f1 = param0;
        as1 = param1;
        return [
          false,
          NofibPrelude.Nil
        ]
      } else {
        return [
          false,
          NofibPrelude.Nil
        ]
      }
    }
  } else {
    if (term1 instanceof Fun1.class) {
      param0 = term1.i;
      param1 = term1.t;
      param2 = term1.l;
      f1 = param0;
      as1 = param1;
      if (term2 instanceof Fun1.class) {
        param01 = term2.i;
        param11 = term2.t;
        param21 = term2.l;
        f2 = param01;
        as2 = param11;
        scrut = f1 === f2;
        if (scrut === true) {
          return one_way_unify1_lst(as1, as2, subst)
        } else {
          return [
            false,
            NofibPrelude.Nil
          ]
        }
      } else {
        return [
          false,
          NofibPrelude.Nil
        ]
      }
    } else {
      return [
        false,
        NofibPrelude.Nil
      ]
    }
  }
};
one_way_unify1_lst = function one_way_unify1_lst(tts1, tts2, subst) {
  let param0, param1, t1, ts1, param01, param11, t2, ts2, scrut, first1, first0, hd_ok, subst_, scrut1, first11, first01, tl_ok, subst__, tmp;
  if (tts1 instanceof NofibPrelude.Nil.class) {
    if (tts2 instanceof NofibPrelude.Nil.class) {
      return [
        true,
        subst
      ]
    } else {
      return [
        false,
        NofibPrelude.Nil
      ]
    }
  } else if (tts1 instanceof NofibPrelude.Cons.class) {
    param0 = tts1.head;
    param1 = tts1.tail;
    t1 = param0;
    ts1 = param1;
    if (tts2 instanceof NofibPrelude.Cons.class) {
      param01 = tts2.head;
      param11 = tts2.tail;
      t2 = param01;
      ts2 = param11;
      scrut = one_way_unify1(t1, t2, subst);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        hd_ok = first0;
        subst_ = first1;
        scrut1 = one_way_unify1_lst(ts1, ts2, subst_);
        if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
          first01 = scrut1[0];
          first11 = scrut1[1];
          tl_ok = first01;
          subst__ = first11;
          if (hd_ok === true) {
            if (tl_ok === true) {
              tmp = true;
            } else {
              tmp = false;
            }
          } else {
            tmp = false;
          }
          return [
            tmp,
            subst__
          ]
        } else {
          return [
            false,
            NofibPrelude.Nil
          ]
        }
      } else {
        return [
          false,
          NofibPrelude.Nil
        ]
      }
    } else {
      return [
        false,
        NofibPrelude.Nil
      ]
    }
  } else {
    return [
      false,
      NofibPrelude.Nil
    ]
  }
};
one_way_unify = function one_way_unify(term1, term2) {
  return one_way_unify1(term1, term2, NofibPrelude.Nil)
};
apply_subst = function apply_subst(subst, t) {
  let param0, param1, param2, f, args, ls, param01, vid, scrut, first1, first0, found, value, tmp, lambda1;
  if (t instanceof Var1.class) {
    param01 = t.i;
    vid = param01;
    scrut = find(vid, subst);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      found = first0;
      value = first1;
      if (found === true) {
        return value
      } else {
        return Var1(vid)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else if (t instanceof Fun1.class) {
    param0 = t.i;
    param1 = t.t;
    param2 = t.l;
    f = param0;
    args = param1;
    ls = param2;
    lambda1 = (undefined, function (x) {
      return apply_subst(subst, x)
    });
    tmp = NofibPrelude.map(lambda1, args);
    return Fun1(f, tmp, ls)
  } else {
    throw new globalThis.Error("match error");
  }
};
rewrite_with_lemmas_helper = function rewrite_with_lemmas_helper(term, lss) {
  let param0, param1, first1, first0, lhs, rhs, ls, scrut, first11, first01, unified, subst, tmp;
  if (lss instanceof NofibPrelude.Nil.class) {
    return term
  } else if (lss instanceof NofibPrelude.Cons.class) {
    param0 = lss.head;
    param1 = lss.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      lhs = first0;
      rhs = first1;
      ls = param1;
      scrut = one_way_unify(term, lhs);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first01 = scrut[0];
        first11 = scrut[1];
        unified = first01;
        subst = first11;
        if (unified === true) {
          tmp = apply_subst(subst, rhs);
          return rewrite(tmp)
        } else {
          return rewrite_with_lemmas_helper(term, ls)
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
rewrite_with_lemmas = function rewrite_with_lemmas(term, lss) {
  let tmp;
  tmp = NofibPrelude.force(lss);
  return rewrite_with_lemmas_helper(term, tmp)
};
rewrite = function rewrite(t) {
  let param0, param1, param2, f, args, lemmas, param01, v, tmp, tmp1;
  if (t instanceof Var1.class) {
    param01 = t.i;
    v = param01;
    return Var1(v)
  } else if (t instanceof Fun1.class) {
    param0 = t.i;
    param1 = t.t;
    param2 = t.l;
    f = param0;
    args = param1;
    lemmas = param2;
    tmp = NofibPrelude.map(rewrite, args);
    tmp1 = Fun1(f, tmp, lemmas);
    return rewrite_with_lemmas(tmp1, lemmas)
  } else {
    throw new globalThis.Error("match error");
  }
};
truep = function truep(x, l) {
  let param0, param1, param2;
  if (x instanceof Fun1.class) {
    param0 = x.i;
    param1 = x.t;
    param2 = x.l;
    if (param0 instanceof TRUE1.class) {
      return true
    } else {
      return termInList(x, l)
    }
  } else {
    return termInList(x, l)
  }
};
falsep = function falsep(x, l) {
  let param0, param1, param2;
  if (x instanceof Fun1.class) {
    param0 = x.i;
    param1 = x.t;
    param2 = x.l;
    if (param0 instanceof FALSE1.class) {
      return true
    } else {
      return termInList(x, l)
    }
  } else {
    return termInList(x, l)
  }
};
tautologyp = function tautologyp(x, true_lst, false_lst) {
  let param0, param1, param2, param01, param11, cond, param02, param12, t, param03, param13, e, scrut, scrut1, scrut2, scrut3, scrut4, scrut5, tmp, tmp1;
  scrut5 = truep(x, true_lst);
  if (scrut5 === true) {
    return true
  } else {
    scrut4 = falsep(x, false_lst);
    if (scrut4 === true) {
      return false
    } else {
      if (x instanceof Fun1.class) {
        param0 = x.i;
        param1 = x.t;
        param2 = x.l;
        if (param0 instanceof IF1.class) {
          if (param1 instanceof NofibPrelude.Cons.class) {
            param01 = param1.head;
            param11 = param1.tail;
            cond = param01;
            if (param11 instanceof NofibPrelude.Cons.class) {
              param02 = param11.head;
              param12 = param11.tail;
              t = param02;
              if (param12 instanceof NofibPrelude.Cons.class) {
                param03 = param12.head;
                param13 = param12.tail;
                e = param03;
                if (param13 instanceof NofibPrelude.Nil.class) {
                  scrut3 = truep(cond, true_lst);
                  if (scrut3 === true) {
                    return tautologyp(t, true_lst, false_lst)
                  } else {
                    scrut2 = falsep(cond, false_lst);
                    if (scrut2 === true) {
                      return tautologyp(e, true_lst, false_lst)
                    } else {
                      tmp = NofibPrelude.Cons(cond, true_lst);
                      scrut = tautologyp(t, tmp, false_lst);
                      if (scrut === true) {
                        tmp1 = NofibPrelude.Cons(cond, false_lst);
                        scrut1 = tautologyp(e, true_lst, tmp1);
                        if (scrut1 === true) {
                          return true
                        } else {
                          return false
                        }
                      } else {
                        return false
                      }
                    }
                  }
                } else {
                  return false
                }
              } else {
                return false
              }
            } else {
              return false
            }
          } else {
            return false
          }
        } else {
          return false
        }
      } else {
        return false
      }
    }
  }
};
tautp = function tautp(x) {
  let tmp;
  tmp = rewrite(x);
  return tautologyp(tmp, NofibPrelude.Nil, NofibPrelude.Nil)
};
test0 = function test0(xxxx) {
  let quotient, if_, sub1, plus, f, implies, times, exp_, gcd_, difference, nlistp, one, remainder, four, and_, reverse_, greaterp, or_, odd_, two, lessp, cons, add1, divides, nilp, listp, consp, lesseqp, equal, append_, greatereqp, member, zerop, not_, iff, length_, even_, a, b, c, d, u, w, x, y, z, boyerFalse, nil, boyerTrue, zero, subst0, theorem, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, lambda1, lambda2, lambda3, lambda4;
  one = function one() {
    let tmp51, tmp52, lambda5;
    lambda5 = (undefined, function () {
      let tmp53, tmp54;
      tmp53 = one();
      tmp54 = add1(zero);
      return NofibPrelude.Cons([
        tmp53,
        tmp54
      ], NofibPrelude.Nil)
    });
    tmp51 = lambda5;
    tmp52 = NofibPrelude.lazy(tmp51);
    return Fun1(ONE1, NofibPrelude.Nil, tmp52)
  };
  two = function two() {
    let tmp51, tmp52, lambda5;
    lambda5 = (undefined, function () {
      let tmp53, tmp54, tmp55;
      tmp53 = two();
      tmp54 = one();
      tmp55 = add1(tmp54);
      return NofibPrelude.Cons([
        tmp53,
        tmp55
      ], NofibPrelude.Nil)
    });
    tmp51 = lambda5;
    tmp52 = NofibPrelude.lazy(tmp51);
    return Fun1(TWO1, NofibPrelude.Nil, tmp52)
  };
  four = function four() {
    let tmp51, tmp52, lambda5;
    lambda5 = (undefined, function () {
      let tmp53, tmp54, tmp55, tmp56;
      tmp53 = four();
      tmp54 = two();
      tmp55 = add1(tmp54);
      tmp56 = add1(tmp55);
      return NofibPrelude.Cons([
        tmp53,
        tmp56
      ], NofibPrelude.Nil)
    });
    tmp51 = lambda5;
    tmp52 = NofibPrelude.lazy(tmp51);
    return Fun1(FOUR1, NofibPrelude.Nil, tmp52)
  };
  add1 = function add1(a1) {
    let tmp51, tmp52, lambda5;
    tmp51 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
    lambda5 = (undefined, function () {
      return NofibPrelude.Nil
    });
    tmp52 = NofibPrelude.lazy(lambda5);
    return Fun1(ADD11, tmp51, tmp52)
  };
  if_ = function if_(a1, b1, c1) {
    let tmp51, tmp52, tmp53, tmp54, tmp55, lambda5;
    tmp51 = NofibPrelude.Cons(c1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(b1, tmp51);
    tmp53 = NofibPrelude.Cons(a1, tmp52);
    lambda5 = (undefined, function () {
      let tmp56, tmp57, tmp58, tmp59, tmp60;
      tmp56 = if_(x, y, z);
      tmp57 = if_(tmp56, u, w);
      tmp58 = if_(y, u, w);
      tmp59 = if_(z, u, w);
      tmp60 = if_(x, tmp58, tmp59);
      return NofibPrelude.Cons([
        tmp57,
        tmp60
      ], NofibPrelude.Nil)
    });
    tmp54 = lambda5;
    tmp55 = NofibPrelude.lazy(tmp54);
    return Fun1(IF1, tmp53, tmp55)
  };
  not_ = function not_(a1) {
    let tmp51, tmp52, tmp53, lambda5;
    tmp51 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
    lambda5 = (undefined, function () {
      let tmp54, tmp55;
      tmp54 = not_(x);
      tmp55 = if_(x, boyerFalse, boyerTrue);
      return NofibPrelude.Cons([
        tmp54,
        tmp55
      ], NofibPrelude.Nil)
    });
    tmp52 = lambda5;
    tmp53 = NofibPrelude.lazy(tmp52);
    return Fun1(NOT1, tmp51, tmp53)
  };
  and_ = function and_(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57;
      tmp55 = and_(x, y);
      tmp56 = if_(y, boyerTrue, boyerFalse);
      tmp57 = if_(x, tmp56, boyerFalse);
      return NofibPrelude.Cons([
        tmp55,
        tmp57
      ], NofibPrelude.Nil)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(AND1, tmp52, tmp54)
  };
  append_ = function append_(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57, tmp58;
      tmp55 = append_(x, y);
      tmp56 = append_(tmp55, z);
      tmp57 = append_(y, z);
      tmp58 = append_(x, tmp57);
      return NofibPrelude.Cons([
        tmp56,
        tmp58
      ], NofibPrelude.Nil)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(APPEND1, tmp52, tmp54)
  };
  cons = function cons(a1, b1) {
    let tmp51, tmp52, tmp53, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      return NofibPrelude.Nil
    });
    tmp53 = NofibPrelude.lazy(lambda5);
    return Fun1(CONS1, tmp52, tmp53)
  };
  consp = function consp(a1) {
    let tmp51, tmp52, tmp53, lambda5;
    tmp51 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
    lambda5 = (undefined, function () {
      let tmp54, tmp55;
      tmp54 = cons(x, y);
      tmp55 = consp(tmp54);
      return NofibPrelude.Cons([
        tmp55,
        boyerTrue
      ], NofibPrelude.Nil)
    });
    tmp52 = lambda5;
    tmp53 = NofibPrelude.lazy(tmp52);
    return Fun1(CONSP1, tmp51, tmp53)
  };
  difference = function difference(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75, tmp76, tmp77, tmp78, tmp79, tmp80, tmp81;
      tmp55 = difference(x, x);
      tmp56 = plus(x, y);
      tmp57 = difference(tmp56, x);
      tmp58 = plus(y, x);
      tmp59 = difference(tmp58, x);
      tmp60 = plus(x, y);
      tmp61 = plus(x, z);
      tmp62 = difference(tmp60, tmp61);
      tmp63 = difference(y, z);
      tmp64 = plus(x, z);
      tmp65 = plus(y, tmp64);
      tmp66 = difference(tmp65, x);
      tmp67 = plus(y, z);
      tmp68 = plus(y, z);
      tmp69 = add1(tmp68);
      tmp70 = difference(tmp69, z);
      tmp71 = add1(y);
      tmp72 = add1(x);
      tmp73 = add1(tmp72);
      tmp74 = two();
      tmp75 = difference(tmp73, tmp74);
      tmp76 = NofibPrelude.Cons([
        tmp75,
        x
      ], NofibPrelude.Nil);
      tmp77 = NofibPrelude.Cons([
        tmp70,
        tmp71
      ], tmp76);
      tmp78 = NofibPrelude.Cons([
        tmp66,
        tmp67
      ], tmp77);
      tmp79 = NofibPrelude.Cons([
        tmp62,
        tmp63
      ], tmp78);
      tmp80 = NofibPrelude.Cons([
        tmp59,
        y
      ], tmp79);
      tmp81 = NofibPrelude.Cons([
        tmp57,
        y
      ], tmp80);
      return NofibPrelude.Cons([
        tmp55,
        zero
      ], tmp81)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(DIFFERENCE1, tmp52, tmp54)
  };
  divides = function divides(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57;
      tmp55 = divides(x, y);
      tmp56 = remainder(y, x);
      tmp57 = zerop(tmp56);
      return NofibPrelude.Cons([
        tmp55,
        tmp57
      ], NofibPrelude.Nil)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(DIVIDES1, tmp52, tmp54)
  };
  equal = function equal(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75, tmp76, tmp77, tmp78, tmp79, tmp80, tmp81, tmp82, tmp83, tmp84, tmp85, tmp86, tmp87, tmp88, tmp89, tmp90, tmp91, tmp92, tmp93, tmp94, tmp95, tmp96, tmp97, tmp98, tmp99, tmp100, tmp101, tmp102, tmp103, tmp104, tmp105, tmp106, tmp107, tmp108, tmp109, tmp110, tmp111, tmp112, tmp113, tmp114, tmp115, tmp116, tmp117, tmp118, tmp119, tmp120, tmp121, tmp122, tmp123, tmp124, tmp125, tmp126, tmp127, tmp128, tmp129;
      tmp55 = plus(x, y);
      tmp56 = equal(tmp55, zero);
      tmp57 = zerop(x);
      tmp58 = zerop(y);
      tmp59 = and_(tmp57, tmp58);
      tmp60 = plus(x, y);
      tmp61 = plus(x, z);
      tmp62 = equal(tmp60, tmp61);
      tmp63 = equal(y, z);
      tmp64 = difference(x, y);
      tmp65 = equal(zero, tmp64);
      tmp66 = lessp(y, x);
      tmp67 = not_(tmp66);
      tmp68 = difference(x, y);
      tmp69 = equal(x, tmp68);
      tmp70 = equal(x, zero);
      tmp71 = zerop(y);
      tmp72 = or_(tmp70, tmp71);
      tmp73 = times(x, y);
      tmp74 = equal(tmp73, zero);
      tmp75 = zerop(x);
      tmp76 = zerop(y);
      tmp77 = or_(tmp75, tmp76);
      tmp78 = append_(x, y);
      tmp79 = append_(x, z);
      tmp80 = equal(tmp78, tmp79);
      tmp81 = equal(y, z);
      tmp82 = times(x, y);
      tmp83 = equal(y, tmp82);
      tmp84 = equal(y, zero);
      tmp85 = one();
      tmp86 = equal(x, tmp85);
      tmp87 = or_(tmp84, tmp86);
      tmp88 = times(x, y);
      tmp89 = equal(x, tmp88);
      tmp90 = equal(x, zero);
      tmp91 = one();
      tmp92 = equal(y, tmp91);
      tmp93 = or_(tmp90, tmp92);
      tmp94 = times(x, y);
      tmp95 = one();
      tmp96 = equal(tmp94, tmp95);
      tmp97 = one();
      tmp98 = equal(x, tmp97);
      tmp99 = one();
      tmp100 = equal(y, tmp99);
      tmp101 = and_(tmp98, tmp100);
      tmp102 = difference(x, y);
      tmp103 = difference(z, y);
      tmp104 = equal(tmp102, tmp103);
      tmp105 = lessp(x, y);
      tmp106 = lessp(y, z);
      tmp107 = not_(tmp106);
      tmp108 = lessp(z, y);
      tmp109 = lessp(y, x);
      tmp110 = not_(tmp109);
      tmp111 = equal(x, z);
      tmp112 = if_(tmp108, tmp110, tmp111);
      tmp113 = if_(tmp105, tmp107, tmp112);
      tmp114 = lessp(x, y);
      tmp115 = equal(tmp114, z);
      tmp116 = lessp(x, y);
      tmp117 = equal(boyerTrue, z);
      tmp118 = equal(boyerFalse, z);
      tmp119 = if_(tmp116, tmp117, tmp118);
      tmp120 = NofibPrelude.Cons([
        tmp115,
        tmp119
      ], NofibPrelude.Nil);
      tmp121 = NofibPrelude.Cons([
        tmp104,
        tmp113
      ], tmp120);
      tmp122 = NofibPrelude.Cons([
        tmp96,
        tmp101
      ], tmp121);
      tmp123 = NofibPrelude.Cons([
        tmp89,
        tmp93
      ], tmp122);
      tmp124 = NofibPrelude.Cons([
        tmp83,
        tmp87
      ], tmp123);
      tmp125 = NofibPrelude.Cons([
        tmp80,
        tmp81
      ], tmp124);
      tmp126 = NofibPrelude.Cons([
        tmp74,
        tmp77
      ], tmp125);
      tmp127 = NofibPrelude.Cons([
        tmp69,
        tmp72
      ], tmp126);
      tmp128 = NofibPrelude.Cons([
        tmp65,
        tmp67
      ], tmp127);
      tmp129 = NofibPrelude.Cons([
        tmp62,
        tmp63
      ], tmp128);
      return NofibPrelude.Cons([
        tmp56,
        tmp59
      ], tmp129)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(EQUAL1, tmp52, tmp54)
  };
  even_ = function even_(a1) {
    let tmp51, tmp52, tmp53, lambda5;
    tmp51 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
    lambda5 = (undefined, function () {
      let tmp54, tmp55, tmp56, tmp57, tmp58;
      tmp54 = even_(x);
      tmp55 = zerop(x);
      tmp56 = sub1(x);
      tmp57 = odd_(tmp56);
      tmp58 = if_(tmp55, boyerTrue, tmp57);
      return NofibPrelude.Cons([
        tmp54,
        tmp58
      ], NofibPrelude.Nil)
    });
    tmp52 = lambda5;
    tmp53 = NofibPrelude.lazy(tmp52);
    return Fun1(EVEN1, tmp51, tmp53)
  };
  exp_ = function exp_(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64;
      tmp55 = plus(y, z);
      tmp56 = exp_(x, tmp55);
      tmp57 = exp_(x, y);
      tmp58 = exp_(x, z);
      tmp59 = times(tmp57, tmp58);
      tmp60 = times(y, z);
      tmp61 = exp_(x, tmp60);
      tmp62 = exp_(x, y);
      tmp63 = exp_(tmp62, z);
      tmp64 = NofibPrelude.Cons([
        tmp61,
        tmp63
      ], NofibPrelude.Nil);
      return NofibPrelude.Cons([
        tmp56,
        tmp59
      ], tmp64)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(EXP1, tmp52, tmp54)
  };
  f = function f(a1) {
    let tmp51, tmp52, lambda5;
    tmp51 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
    lambda5 = (undefined, function () {
      return NofibPrelude.Nil
    });
    tmp52 = NofibPrelude.lazy(lambda5);
    return Fun1(F1, tmp51, tmp52)
  };
  gcd_ = function gcd_(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62;
      tmp55 = gcd_(x, y);
      tmp56 = gcd_(y, x);
      tmp57 = times(x, z);
      tmp58 = times(y, z);
      tmp59 = gcd_(tmp57, tmp58);
      tmp60 = gcd_(x, y);
      tmp61 = times(z, tmp60);
      tmp62 = NofibPrelude.Cons([
        tmp59,
        tmp61
      ], NofibPrelude.Nil);
      return NofibPrelude.Cons([
        tmp55,
        tmp56
      ], tmp62)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(GCD1, tmp52, tmp54)
  };
  greatereqp = function greatereqp(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57;
      tmp55 = greatereqp(x, y);
      tmp56 = lessp(x, y);
      tmp57 = not_(tmp56);
      return NofibPrelude.Cons([
        tmp55,
        tmp57
      ], NofibPrelude.Nil)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(GREATEREQP1, tmp52, tmp54)
  };
  greaterp = function greaterp(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56;
      tmp55 = greaterp(x, y);
      tmp56 = lessp(y, x);
      return NofibPrelude.Cons([
        tmp55,
        tmp56
      ], NofibPrelude.Nil)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(GREATERP1, tmp52, tmp54)
  };
  implies = function implies(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57;
      tmp55 = implies(x, y);
      tmp56 = if_(y, boyerTrue, boyerFalse);
      tmp57 = if_(x, tmp56, boyerTrue);
      return NofibPrelude.Cons([
        tmp55,
        tmp57
      ], NofibPrelude.Nil)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(IMPLIES1, tmp52, tmp54)
  };
  iff = function iff(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57, tmp58;
      tmp55 = iff(x, y);
      tmp56 = implies(x, y);
      tmp57 = implies(y, x);
      tmp58 = and_(tmp56, tmp57);
      return NofibPrelude.Cons([
        tmp55,
        tmp58
      ], NofibPrelude.Nil)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(IFF1, tmp52, tmp54)
  };
  length_ = function length_(a1) {
    let tmp51, tmp52, tmp53, lambda5;
    tmp51 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
    lambda5 = (undefined, function () {
      let tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65;
      tmp54 = reverse_(x);
      tmp55 = length_(tmp54);
      tmp56 = length_(x);
      tmp57 = cons(u, w);
      tmp58 = cons(z, tmp57);
      tmp59 = cons(y, tmp58);
      tmp60 = cons(x, tmp59);
      tmp61 = length_(tmp60);
      tmp62 = four();
      tmp63 = length_(w);
      tmp64 = plus(tmp62, tmp63);
      tmp65 = NofibPrelude.Cons([
        tmp61,
        tmp64
      ], NofibPrelude.Nil);
      return NofibPrelude.Cons([
        tmp55,
        tmp56
      ], tmp65)
    });
    tmp52 = lambda5;
    tmp53 = NofibPrelude.lazy(tmp52);
    return Fun1(LENGTH1, tmp51, tmp53)
  };
  lesseqp = function lesseqp(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57;
      tmp55 = lesseqp(x, y);
      tmp56 = lessp(y, x);
      tmp57 = not_(tmp56);
      return NofibPrelude.Cons([
        tmp55,
        tmp57
      ], NofibPrelude.Nil)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(LESSEQP1, tmp52, tmp54)
  };
  lessp = function lessp(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75, tmp76, tmp77, tmp78, tmp79, tmp80, tmp81, tmp82, tmp83, tmp84;
      tmp55 = remainder(x, y);
      tmp56 = lessp(tmp55, y);
      tmp57 = zerop(y);
      tmp58 = not_(tmp57);
      tmp59 = quotient(x, y);
      tmp60 = lessp(tmp59, x);
      tmp61 = zerop(x);
      tmp62 = not_(tmp61);
      tmp63 = one();
      tmp64 = lessp(tmp63, y);
      tmp65 = and_(tmp62, tmp64);
      tmp66 = plus(x, y);
      tmp67 = plus(x, z);
      tmp68 = lessp(tmp66, tmp67);
      tmp69 = lessp(y, z);
      tmp70 = times(x, z);
      tmp71 = times(y, z);
      tmp72 = lessp(tmp70, tmp71);
      tmp73 = zerop(z);
      tmp74 = not_(tmp73);
      tmp75 = lessp(x, y);
      tmp76 = and_(tmp74, tmp75);
      tmp77 = plus(x, y);
      tmp78 = lessp(y, tmp77);
      tmp79 = zerop(x);
      tmp80 = not_(tmp79);
      tmp81 = NofibPrelude.Cons([
        tmp78,
        tmp80
      ], NofibPrelude.Nil);
      tmp82 = NofibPrelude.Cons([
        tmp72,
        tmp76
      ], tmp81);
      tmp83 = NofibPrelude.Cons([
        tmp68,
        tmp69
      ], tmp82);
      tmp84 = NofibPrelude.Cons([
        tmp60,
        tmp65
      ], tmp83);
      return NofibPrelude.Cons([
        tmp56,
        tmp58
      ], tmp84)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(LESSP1, tmp52, tmp54)
  };
  nilp = function nilp(a1) {
    let tmp51, tmp52, tmp53, lambda5;
    tmp51 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
    lambda5 = (undefined, function () {
      let tmp54, tmp55;
      tmp54 = nilp(x);
      tmp55 = equal(x, nil);
      return NofibPrelude.Cons([
        tmp54,
        tmp55
      ], NofibPrelude.Nil)
    });
    tmp52 = lambda5;
    tmp53 = NofibPrelude.lazy(tmp52);
    return Fun1(NILP1, tmp51, tmp53)
  };
  listp = function listp(a1) {
    let tmp51, tmp52, tmp53, lambda5;
    tmp51 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
    lambda5 = (undefined, function () {
      let tmp54, tmp55, tmp56, tmp57;
      tmp54 = listp(x);
      tmp55 = nilp(x);
      tmp56 = consp(x);
      tmp57 = or_(tmp55, tmp56);
      return NofibPrelude.Cons([
        tmp54,
        tmp57
      ], NofibPrelude.Nil)
    });
    tmp52 = lambda5;
    tmp53 = NofibPrelude.lazy(tmp52);
    return Fun1(LISTP1, tmp51, tmp53)
  };
  member = function member(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63;
      tmp55 = append_(y, z);
      tmp56 = member(x, tmp55);
      tmp57 = member(x, y);
      tmp58 = member(x, z);
      tmp59 = or_(tmp57, tmp58);
      tmp60 = reverse_(y);
      tmp61 = member(x, tmp60);
      tmp62 = member(x, y);
      tmp63 = NofibPrelude.Cons([
        tmp61,
        tmp62
      ], NofibPrelude.Nil);
      return NofibPrelude.Cons([
        tmp56,
        tmp59
      ], tmp63)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(MEMBER1, tmp52, tmp54)
  };
  nlistp = function nlistp(a1) {
    let tmp51, tmp52, tmp53, lambda5;
    tmp51 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
    lambda5 = (undefined, function () {
      let tmp54, tmp55, tmp56;
      tmp54 = nlistp(x);
      tmp55 = listp(x);
      tmp56 = not_(tmp55);
      return NofibPrelude.Cons([
        tmp54,
        tmp56
      ], NofibPrelude.Nil)
    });
    tmp52 = lambda5;
    tmp53 = NofibPrelude.lazy(tmp52);
    return Fun1(NLISTP1, tmp51, tmp53)
  };
  odd_ = function odd_(a1) {
    let tmp51, tmp52, tmp53, lambda5;
    tmp51 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
    lambda5 = (undefined, function () {
      let tmp54, tmp55, tmp56;
      tmp54 = odd_(x);
      tmp55 = sub1(x);
      tmp56 = even_(tmp55);
      return NofibPrelude.Cons([
        tmp54,
        tmp56
      ], NofibPrelude.Nil)
    });
    tmp52 = lambda5;
    tmp53 = NofibPrelude.lazy(tmp52);
    return Fun1(ODD1, tmp51, tmp53)
  };
  or_ = function or_(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57;
      tmp55 = or_(x, y);
      tmp56 = if_(y, boyerTrue, boyerFalse);
      tmp57 = if_(x, boyerTrue, tmp56);
      return NofibPrelude.Cons([
        tmp55,
        tmp57
      ], NofibPrelude.Nil)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(OR1, tmp52, tmp54)
  };
  plus = function plus(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68;
      tmp55 = plus(x, y);
      tmp56 = plus(tmp55, z);
      tmp57 = plus(y, z);
      tmp58 = plus(x, tmp57);
      tmp59 = remainder(x, y);
      tmp60 = quotient(x, y);
      tmp61 = times(y, tmp60);
      tmp62 = plus(tmp59, tmp61);
      tmp63 = add1(y);
      tmp64 = plus(x, tmp63);
      tmp65 = plus(x, y);
      tmp66 = add1(tmp65);
      tmp67 = NofibPrelude.Cons([
        tmp64,
        tmp66
      ], NofibPrelude.Nil);
      tmp68 = NofibPrelude.Cons([
        tmp62,
        x
      ], tmp67);
      return NofibPrelude.Cons([
        tmp56,
        tmp58
      ], tmp68)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(PLUS1, tmp52, tmp54)
  };
  quotient = function quotient(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66;
      tmp55 = plus(x, y);
      tmp56 = plus(x, tmp55);
      tmp57 = two();
      tmp58 = quotient(tmp56, tmp57);
      tmp59 = two();
      tmp60 = quotient(y, tmp59);
      tmp61 = plus(x, tmp60);
      tmp62 = times(y, x);
      tmp63 = quotient(tmp62, y);
      tmp64 = zerop(y);
      tmp65 = if_(tmp64, zero, x);
      tmp66 = NofibPrelude.Cons([
        tmp63,
        tmp65
      ], NofibPrelude.Nil);
      return NofibPrelude.Cons([
        tmp58,
        tmp61
      ], tmp66)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(QUOTIENT1, tmp52, tmp54)
  };
  remainder = function remainder(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64;
      tmp55 = one();
      tmp56 = remainder(x, tmp55);
      tmp57 = remainder(x, x);
      tmp58 = times(x, y);
      tmp59 = remainder(tmp58, x);
      tmp60 = times(x, y);
      tmp61 = remainder(tmp60, y);
      tmp62 = NofibPrelude.Cons([
        tmp61,
        zero
      ], NofibPrelude.Nil);
      tmp63 = NofibPrelude.Cons([
        tmp59,
        zero
      ], tmp62);
      tmp64 = NofibPrelude.Cons([
        tmp57,
        zero
      ], tmp63);
      return NofibPrelude.Cons([
        tmp56,
        zero
      ], tmp64)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(REMAINDER1, tmp52, tmp54)
  };
  reverse_ = function reverse_(a1) {
    let tmp51, tmp52, tmp53, lambda5;
    tmp51 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
    lambda5 = (undefined, function () {
      let tmp54, tmp55, tmp56, tmp57, tmp58;
      tmp54 = append_(x, y);
      tmp55 = reverse_(tmp54);
      tmp56 = reverse_(y);
      tmp57 = reverse_(x);
      tmp58 = append_(tmp56, tmp57);
      return NofibPrelude.Cons([
        tmp55,
        tmp58
      ], NofibPrelude.Nil)
    });
    tmp52 = lambda5;
    tmp53 = NofibPrelude.lazy(tmp52);
    return Fun1(REVERSE1, tmp51, tmp53)
  };
  sub1 = function sub1(a1) {
    let tmp51, tmp52, tmp53, lambda5;
    tmp51 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
    lambda5 = (undefined, function () {
      let tmp54, tmp55;
      tmp54 = add1(x);
      tmp55 = sub1(tmp54);
      return NofibPrelude.Cons([
        tmp55,
        x
      ], NofibPrelude.Nil)
    });
    tmp52 = lambda5;
    tmp53 = NofibPrelude.lazy(tmp52);
    return Fun1(SUB11, tmp51, tmp53)
  };
  times = function times(a1, b1) {
    let tmp51, tmp52, tmp53, tmp54, lambda5;
    tmp51 = NofibPrelude.Cons(b1, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(a1, tmp51);
    lambda5 = (undefined, function () {
      let tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75;
      tmp55 = plus(y, z);
      tmp56 = times(x, tmp55);
      tmp57 = times(x, y);
      tmp58 = times(x, z);
      tmp59 = plus(tmp57, tmp58);
      tmp60 = times(x, y);
      tmp61 = times(tmp60, z);
      tmp62 = times(y, z);
      tmp63 = times(x, tmp62);
      tmp64 = difference(y, z);
      tmp65 = times(x, tmp64);
      tmp66 = times(y, x);
      tmp67 = times(z, x);
      tmp68 = difference(tmp66, tmp67);
      tmp69 = add1(y);
      tmp70 = times(x, tmp69);
      tmp71 = times(x, y);
      tmp72 = plus(x, tmp71);
      tmp73 = NofibPrelude.Cons([
        tmp70,
        tmp72
      ], NofibPrelude.Nil);
      tmp74 = NofibPrelude.Cons([
        tmp65,
        tmp68
      ], tmp73);
      tmp75 = NofibPrelude.Cons([
        tmp61,
        tmp63
      ], tmp74);
      return NofibPrelude.Cons([
        tmp56,
        tmp59
      ], tmp75)
    });
    tmp53 = lambda5;
    tmp54 = NofibPrelude.lazy(tmp53);
    return Fun1(TIMES1, tmp52, tmp54)
  };
  zerop = function zerop(a1) {
    let tmp51, tmp52, tmp53, lambda5;
    tmp51 = NofibPrelude.Cons(a1, NofibPrelude.Nil);
    lambda5 = (undefined, function () {
      let tmp54, tmp55;
      tmp54 = zerop(x);
      tmp55 = equal(x, zero);
      return NofibPrelude.Cons([
        tmp54,
        tmp55
      ], NofibPrelude.Nil)
    });
    tmp52 = lambda5;
    tmp53 = NofibPrelude.lazy(tmp52);
    return Fun1(ZEROP1, tmp51, tmp53)
  };
  tmp = Var1(A1);
  a = tmp;
  tmp1 = Var1(B1);
  b = tmp1;
  tmp2 = Var1(C1);
  c = tmp2;
  tmp3 = Var1(D1);
  d = tmp3;
  tmp4 = Var1(U1);
  u = tmp4;
  tmp5 = Var1(W1);
  w = tmp5;
  tmp6 = Var1(X1);
  x = tmp6;
  tmp7 = Var1(Y1);
  y = tmp7;
  tmp8 = Var1(Z1);
  z = tmp8;
  lambda1 = (undefined, function () {
    return NofibPrelude.Nil
  });
  tmp9 = NofibPrelude.lazy(lambda1);
  tmp10 = Fun1(FALSE1, NofibPrelude.Nil, tmp9);
  boyerFalse = tmp10;
  lambda2 = (undefined, function () {
    return NofibPrelude.Nil
  });
  tmp11 = NofibPrelude.lazy(lambda2);
  tmp12 = Fun1(NIL1, NofibPrelude.Nil, tmp11);
  nil = tmp12;
  lambda3 = (undefined, function () {
    return NofibPrelude.Nil
  });
  tmp13 = NofibPrelude.lazy(lambda3);
  tmp14 = Fun1(TRUE1, NofibPrelude.Nil, tmp13);
  boyerTrue = tmp14;
  lambda4 = (undefined, function () {
    return NofibPrelude.Nil
  });
  tmp15 = NofibPrelude.lazy(lambda4);
  tmp16 = Fun1(ZERO1, NofibPrelude.Nil, tmp15);
  zero = tmp16;
  tmp17 = plus(a, b);
  tmp18 = plus(c, zero);
  tmp19 = plus(tmp17, tmp18);
  tmp20 = f(tmp19);
  tmp21 = times(a, b);
  tmp22 = plus(c, d);
  tmp23 = times(tmp21, tmp22);
  tmp24 = f(tmp23);
  tmp25 = append_(a, b);
  tmp26 = append_(tmp25, nil);
  tmp27 = reverse_(tmp26);
  tmp28 = f(tmp27);
  tmp29 = plus(a, b);
  tmp30 = difference(x, y);
  tmp31 = equal(tmp29, tmp30);
  tmp32 = remainder(a, b);
  tmp33 = length_(b);
  tmp34 = member(a, tmp33);
  tmp35 = lessp(tmp32, tmp34);
  tmp36 = NofibPrelude.Cons([
    W1,
    tmp35
  ], NofibPrelude.Nil);
  tmp37 = NofibPrelude.Cons([
    U1,
    tmp31
  ], tmp36);
  tmp38 = NofibPrelude.Cons([
    Z1,
    tmp28
  ], tmp37);
  tmp39 = NofibPrelude.Cons([
    Y1,
    tmp24
  ], tmp38);
  tmp40 = NofibPrelude.Cons([
    X1,
    tmp20
  ], tmp39);
  subst0 = tmp40;
  tmp41 = implies(xxxx, y);
  tmp42 = implies(y, z);
  tmp43 = implies(z, u);
  tmp44 = implies(u, w);
  tmp45 = and_(tmp43, tmp44);
  tmp46 = and_(tmp42, tmp45);
  tmp47 = and_(tmp41, tmp46);
  tmp48 = implies(x, w);
  tmp49 = implies(tmp47, tmp48);
  theorem = tmp49;
  tmp50 = apply_subst(subst0, theorem);
  return tautp(tmp50)
};
testBoyer_nofib = function testBoyer_nofib(n) {
  let tmp, tmp1;
  tmp = Var1(X1);
  tmp1 = NofibPrelude.replicate(n, tmp);
  return NofibPrelude.all(test0, tmp1)
};
Id1 = class Id {
  constructor() {}
  toString() { return "Id"; }
};
const A$class = class A extends Id1 {
  constructor() {
    super();
  }
  toString() { return "A"; }
}; A1 = new A$class;
A1.class = A$class;
const B$class = class B extends Id1 {
  constructor() {
    super();
  }
  toString() { return "B"; }
}; B1 = new B$class;
B1.class = B$class;
const C$class = class C extends Id1 {
  constructor() {
    super();
  }
  toString() { return "C"; }
}; C1 = new C$class;
C1.class = C$class;
const D$class = class D extends Id1 {
  constructor() {
    super();
  }
  toString() { return "D"; }
}; D1 = new D$class;
D1.class = D$class;
const X$class = class X extends Id1 {
  constructor() {
    super();
  }
  toString() { return "X"; }
}; X1 = new X$class;
X1.class = X$class;
const Y$class = class Y extends Id1 {
  constructor() {
    super();
  }
  toString() { return "Y"; }
}; Y1 = new Y$class;
Y1.class = Y$class;
const Z$class = class Z extends Id1 {
  constructor() {
    super();
  }
  toString() { return "Z"; }
}; Z1 = new Z$class;
Z1.class = Z$class;
const U$class = class U extends Id1 {
  constructor() {
    super();
  }
  toString() { return "U"; }
}; U1 = new U$class;
U1.class = U$class;
const W$class = class W extends Id1 {
  constructor() {
    super();
  }
  toString() { return "W"; }
}; W1 = new W$class;
W1.class = W$class;
const ADD1$class = class ADD1 extends Id1 {
  constructor() {
    super();
  }
  toString() { return "ADD1"; }
}; ADD11 = new ADD1$class;
ADD11.class = ADD1$class;
const AND$class = class AND extends Id1 {
  constructor() {
    super();
  }
  toString() { return "AND"; }
}; AND1 = new AND$class;
AND1.class = AND$class;
const APPEND$class = class APPEND extends Id1 {
  constructor() {
    super();
  }
  toString() { return "APPEND"; }
}; APPEND1 = new APPEND$class;
APPEND1.class = APPEND$class;
const CONS$class = class CONS extends Id1 {
  constructor() {
    super();
  }
  toString() { return "CONS"; }
}; CONS1 = new CONS$class;
CONS1.class = CONS$class;
const CONSP$class = class CONSP extends Id1 {
  constructor() {
    super();
  }
  toString() { return "CONSP"; }
}; CONSP1 = new CONSP$class;
CONSP1.class = CONSP$class;
const DIFFERENCE$class = class DIFFERENCE extends Id1 {
  constructor() {
    super();
  }
  toString() { return "DIFFERENCE"; }
}; DIFFERENCE1 = new DIFFERENCE$class;
DIFFERENCE1.class = DIFFERENCE$class;
const DIVIDES$class = class DIVIDES extends Id1 {
  constructor() {
    super();
  }
  toString() { return "DIVIDES"; }
}; DIVIDES1 = new DIVIDES$class;
DIVIDES1.class = DIVIDES$class;
const EQUAL$class = class EQUAL extends Id1 {
  constructor() {
    super();
  }
  toString() { return "EQUAL"; }
}; EQUAL1 = new EQUAL$class;
EQUAL1.class = EQUAL$class;
const EVEN$class = class EVEN extends Id1 {
  constructor() {
    super();
  }
  toString() { return "EVEN"; }
}; EVEN1 = new EVEN$class;
EVEN1.class = EVEN$class;
const EXP$class = class EXP extends Id1 {
  constructor() {
    super();
  }
  toString() { return "EXP"; }
}; EXP1 = new EXP$class;
EXP1.class = EXP$class;
const F$class = class F extends Id1 {
  constructor() {
    super();
  }
  toString() { return "F"; }
}; F1 = new F$class;
F1.class = F$class;
const FALSE$class = class FALSE extends Id1 {
  constructor() {
    super();
  }
  toString() { return "FALSE"; }
}; FALSE1 = new FALSE$class;
FALSE1.class = FALSE$class;
const FOUR$class = class FOUR extends Id1 {
  constructor() {
    super();
  }
  toString() { return "FOUR"; }
}; FOUR1 = new FOUR$class;
FOUR1.class = FOUR$class;
const GCD$class = class GCD extends Id1 {
  constructor() {
    super();
  }
  toString() { return "GCD"; }
}; GCD1 = new GCD$class;
GCD1.class = GCD$class;
const GREATEREQP$class = class GREATEREQP extends Id1 {
  constructor() {
    super();
  }
  toString() { return "GREATEREQP"; }
}; GREATEREQP1 = new GREATEREQP$class;
GREATEREQP1.class = GREATEREQP$class;
const GREATERP$class = class GREATERP extends Id1 {
  constructor() {
    super();
  }
  toString() { return "GREATERP"; }
}; GREATERP1 = new GREATERP$class;
GREATERP1.class = GREATERP$class;
const IF$class = class IF extends Id1 {
  constructor() {
    super();
  }
  toString() { return "IF"; }
}; IF1 = new IF$class;
IF1.class = IF$class;
const IFF$class = class IFF extends Id1 {
  constructor() {
    super();
  }
  toString() { return "IFF"; }
}; IFF1 = new IFF$class;
IFF1.class = IFF$class;
const IMPLIES$class = class IMPLIES extends Id1 {
  constructor() {
    super();
  }
  toString() { return "IMPLIES"; }
}; IMPLIES1 = new IMPLIES$class;
IMPLIES1.class = IMPLIES$class;
const LENGTH$class = class LENGTH extends Id1 {
  constructor() {
    super();
  }
  toString() { return "LENGTH"; }
}; LENGTH1 = new LENGTH$class;
LENGTH1.class = LENGTH$class;
const LESSEQP$class = class LESSEQP extends Id1 {
  constructor() {
    super();
  }
  toString() { return "LESSEQP"; }
}; LESSEQP1 = new LESSEQP$class;
LESSEQP1.class = LESSEQP$class;
const LESSP$class = class LESSP extends Id1 {
  constructor() {
    super();
  }
  toString() { return "LESSP"; }
}; LESSP1 = new LESSP$class;
LESSP1.class = LESSP$class;
const LISTP$class = class LISTP extends Id1 {
  constructor() {
    super();
  }
  toString() { return "LISTP"; }
}; LISTP1 = new LISTP$class;
LISTP1.class = LISTP$class;
const MEMBER$class = class MEMBER extends Id1 {
  constructor() {
    super();
  }
  toString() { return "MEMBER"; }
}; MEMBER1 = new MEMBER$class;
MEMBER1.class = MEMBER$class;
const NIL$class = class NIL extends Id1 {
  constructor() {
    super();
  }
  toString() { return "NIL"; }
}; NIL1 = new NIL$class;
NIL1.class = NIL$class;
const NILP$class = class NILP extends Id1 {
  constructor() {
    super();
  }
  toString() { return "NILP"; }
}; NILP1 = new NILP$class;
NILP1.class = NILP$class;
const NLISTP$class = class NLISTP extends Id1 {
  constructor() {
    super();
  }
  toString() { return "NLISTP"; }
}; NLISTP1 = new NLISTP$class;
NLISTP1.class = NLISTP$class;
const NOT$class = class NOT extends Id1 {
  constructor() {
    super();
  }
  toString() { return "NOT"; }
}; NOT1 = new NOT$class;
NOT1.class = NOT$class;
const ODD$class = class ODD extends Id1 {
  constructor() {
    super();
  }
  toString() { return "ODD"; }
}; ODD1 = new ODD$class;
ODD1.class = ODD$class;
const ONE$class = class ONE extends Id1 {
  constructor() {
    super();
  }
  toString() { return "ONE"; }
}; ONE1 = new ONE$class;
ONE1.class = ONE$class;
const OR$class = class OR extends Id1 {
  constructor() {
    super();
  }
  toString() { return "OR"; }
}; OR1 = new OR$class;
OR1.class = OR$class;
const PLUS$class = class PLUS extends Id1 {
  constructor() {
    super();
  }
  toString() { return "PLUS"; }
}; PLUS1 = new PLUS$class;
PLUS1.class = PLUS$class;
const QUOTIENT$class = class QUOTIENT extends Id1 {
  constructor() {
    super();
  }
  toString() { return "QUOTIENT"; }
}; QUOTIENT1 = new QUOTIENT$class;
QUOTIENT1.class = QUOTIENT$class;
const REMAINDER$class = class REMAINDER extends Id1 {
  constructor() {
    super();
  }
  toString() { return "REMAINDER"; }
}; REMAINDER1 = new REMAINDER$class;
REMAINDER1.class = REMAINDER$class;
const REVERSE$class = class REVERSE extends Id1 {
  constructor() {
    super();
  }
  toString() { return "REVERSE"; }
}; REVERSE1 = new REVERSE$class;
REVERSE1.class = REVERSE$class;
const SUB1$class = class SUB1 extends Id1 {
  constructor() {
    super();
  }
  toString() { return "SUB1"; }
}; SUB11 = new SUB1$class;
SUB11.class = SUB1$class;
const TIMES$class = class TIMES extends Id1 {
  constructor() {
    super();
  }
  toString() { return "TIMES"; }
}; TIMES1 = new TIMES$class;
TIMES1.class = TIMES$class;
const TRUE$class = class TRUE extends Id1 {
  constructor() {
    super();
  }
  toString() { return "TRUE"; }
}; TRUE1 = new TRUE$class;
TRUE1.class = TRUE$class;
const TWO$class = class TWO extends Id1 {
  constructor() {
    super();
  }
  toString() { return "TWO"; }
}; TWO1 = new TWO$class;
TWO1.class = TWO$class;
const ZERO$class = class ZERO extends Id1 {
  constructor() {
    super();
  }
  toString() { return "ZERO"; }
}; ZERO1 = new ZERO$class;
ZERO1.class = ZERO$class;
const ZEROP$class = class ZEROP extends Id1 {
  constructor() {
    super();
  }
  toString() { return "ZEROP"; }
}; ZEROP1 = new ZEROP$class;
ZEROP1.class = ZEROP$class;
Term1 = class Term {
  constructor() {}
  toString() { return "Term"; }
};
Var1 = function Var(i1) {
  return new Var.class(i1);
};
Var1.class = class Var extends Term1 {
  constructor(i) {
    super();
    this.i = i;
  }
  toString() { return "Var(" + globalThis.Predef.render(this.i) + ")"; }
};
Fun1 = function Fun(i1, t1, l1) {
  return new Fun.class(i1, t1, l1);
};
Fun1.class = class Fun extends Term1 {
  constructor(i, t, l) {
    super();
    this.i = i;
    this.t = t;
    this.l = l;
  }
  toString() { return "Fun(" + globalThis.Predef.render(this.i) + ", " + globalThis.Predef.render(this.t) + ", " + globalThis.Predef.render(this.l) + ")"; }
};
const ERROR$class = class ERROR extends Term1 {
  constructor() {
    super();
  }
  toString() { return "ERROR"; }
}; ERROR1 = new ERROR$class;
ERROR1.class = ERROR$class;
lambda = (undefined, function () {
  return testBoyer_nofib(5)
});
BenchmarkPrelude.benchmark(lambda)