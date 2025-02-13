import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let traverseTerm, showTerm, App1, mainMonad, Lam1, MyState1, traverseCon, testLambda_nofib, eqTerm, simpleEvalCon, myRunState, Unit1, pushVar, Thunk1, Term1, lookup, Con1, eval_nofib, myMaybe, myEvalState, ppenv, ev, lookupVar, simpleApply, Var1, ppn, Add1, eqEnv, bracket, myBind, withEnv, simpleEval, myReturn, apply, IfZero1, mainSimple, pp, Incr1, myGet, incr, lfxx, fix, nMinus1, partialSum0, sum0, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34;
lookup = function lookup(k, t) {
  let param0, param1, first1, first0, x, v, t1, scrut;
  if (t instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.None
  } else if (t instanceof NofibPrelude.Cons.class) {
    param0 = t.head;
    param1 = t.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      x = first0;
      v = first1;
      t1 = param1;
      scrut = NofibPrelude.listEq(k, x);
      if (scrut === true) {
        return NofibPrelude.Some(v)
      } else {
        return lookup(k, t1)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
myRunState = function myRunState(m, s) {
  let param0, f;
  if (m instanceof MyState1.class) {
    param0 = m.r;
    f = param0;
    return runtime.safeCall(f(s))
  } else {
    throw new globalThis.Error("match error");
  }
};
myBind = function myBind(m, f) {
  let tmp35;
  tmp35 = (s) => {
    let scrut, first1, first0, s_, a, tmp36;
    scrut = myRunState(m, s);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      s_ = first0;
      a = first1;
      tmp36 = runtime.safeCall(f(a));
      return myRunState(tmp36, s_)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  return MyState1(tmp35)
};
myReturn = function myReturn(a) {
  return MyState1((s) => {
    return [
      s,
      a
    ]
  })
};
myEvalState = function myEvalState(m, s) {
  let scrut, first1, first0, s_, a;
  scrut = myRunState(m, s);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    s_ = first0;
    a = first1;
    return a
  } else {
    throw new globalThis.Error("match error");
  }
};
eqEnv = function eqEnv(a, b) {
  let param0, param1, first1, first0, s1, t1, b1, param01, param11, first11, first01, s2, t2, d, scrut, scrut1;
  if (a instanceof NofibPrelude.Nil.class) {
    if (b instanceof NofibPrelude.Nil.class) {
      return true
    } else {
      return false
    }
  } else if (a instanceof NofibPrelude.Cons.class) {
    param0 = a.head;
    param1 = a.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      s1 = first0;
      t1 = first1;
      b1 = param1;
      if (b1 instanceof NofibPrelude.Cons.class) {
        param01 = b1.head;
        param11 = b1.tail;
        if (globalThis.Array.isArray(param01) && param01.length === 2) {
          first01 = param01[0];
          first11 = param01[1];
          s2 = first01;
          t2 = first11;
          d = param11;
          scrut = NofibPrelude.listEq(s1, s2);
          if (scrut === true) {
            scrut1 = eqTerm(t1, t2);
            if (scrut1 === true) {
              return eqEnv(b1, d)
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
};
eqTerm = function eqTerm(a, b) {
  let param0, param1, a1, b1, param01, param11, c, d, param02, param12, param2, a2, b2, c1, param03, param13, param21, d1, e, f, param04, param14, a3, b3, param05, param15, c2, d2, param06, param16, a4, b4, param07, param17, c3, d3, param08, param18, a5, b5, param09, param19, c4, d4, param010, a6, param011, b6, param012, a7, param013, b7, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46;
  if (a instanceof Var1.class) {
    param012 = a.s;
    a7 = param012;
    if (b instanceof Var1.class) {
      param013 = b.s;
      b7 = param013;
      return NofibPrelude.listEq(a7, b7)
    } else {
      return false
    }
  } else if (a instanceof Con1.class) {
    param010 = a.i;
    a6 = param010;
    if (b instanceof Con1.class) {
      param011 = b.i;
      b6 = param011;
      return a6 === b6
    } else {
      return false
    }
  } else if (a instanceof Incr1.class) {
    if (b instanceof Incr1.class) {
      return true
    } else {
      return false
    }
  } else if (a instanceof Add1.class) {
    param08 = a.a;
    param18 = a.b;
    a5 = param08;
    b5 = param18;
    if (b5 instanceof Add1.class) {
      param09 = b5.a;
      param19 = b5.b;
      c4 = param09;
      d4 = param19;
      tmp35 = eqTerm(a5, c4);
      tmp36 = eqTerm(b5, d4);
      return tmp35 && tmp36
    } else {
      return false
    }
  } else if (a instanceof Lam1.class) {
    param06 = a.s;
    param16 = a.t;
    a4 = param06;
    b4 = param16;
    if (b4 instanceof Lam1.class) {
      param07 = b4.s;
      param17 = b4.t;
      c3 = param07;
      d3 = param17;
      tmp37 = NofibPrelude.listEq(a4, c3);
      tmp38 = eqTerm(b4, d3);
      return tmp37 && tmp38
    } else {
      return false
    }
  } else if (a instanceof App1.class) {
    param04 = a.a;
    param14 = a.b;
    a3 = param04;
    b3 = param14;
    if (b3 instanceof App1.class) {
      param05 = b3.a;
      param15 = b3.b;
      c2 = param05;
      d2 = param15;
      tmp39 = eqTerm(a3, c2);
      tmp40 = eqTerm(b3, d2);
      return tmp39 && tmp40
    } else {
      return false
    }
  } else if (a instanceof IfZero1.class) {
    param02 = a.a;
    param12 = a.b;
    param2 = a.c;
    a2 = param02;
    b2 = param12;
    c1 = param2;
    if (b2 instanceof IfZero1.class) {
      param03 = b2.a;
      param13 = b2.b;
      param21 = b2.c;
      d1 = param03;
      e = param13;
      f = param21;
      tmp41 = eqTerm(a2, d1);
      tmp42 = eqTerm(b2, e);
      tmp43 = tmp41 && tmp42;
      tmp44 = eqTerm(c1, f);
      return tmp43 && tmp44
    } else {
      return false
    }
  } else if (a instanceof Thunk1.class) {
    param0 = a.t;
    param1 = a.e;
    a1 = param0;
    b1 = param1;
    if (b1 instanceof Thunk1.class) {
      param01 = b1.t;
      param11 = b1.e;
      c = param01;
      d = param11;
      tmp45 = eqTerm(a1, c);
      tmp46 = eqEnv(b1, d);
      return tmp45 && tmp46
    } else {
      return false
    }
  } else {
    return false
  }
};
myMaybe = function myMaybe(d, f, x) {
  let param0, x1;
  if (x instanceof NofibPrelude.Some.class) {
    param0 = x.x;
    x1 = param0;
    return runtime.safeCall(f(x1))
  } else {
    throw new globalThis.Error("match error");
  }
};
lookupVar = function lookupVar(v) {
  let lookup2;
  lookup2 = function lookup2(env) {
    let tmp35;
    tmp35 = lookup(v, env);
    return myMaybe((dummy) => {
      throw globalThis.Error("undefined");
    }, (x) => {
      return x
    }, tmp35)
  };
  return myBind(myGet, (env) => {
    let tmp35;
    tmp35 = lookup2(env);
    return myReturn(tmp35)
  })
};
withEnv = function withEnv(tmp35, m) {
  let tmp36;
  tmp36 = myEvalState(m, tmp35);
  return myReturn(tmp36)
};
pushVar = function pushVar(v, t, m) {
  return myBind(myGet, (env) => {
    let tmp35;
    tmp35 = NofibPrelude.Cons([
      v,
      t
    ], env);
    return withEnv(tmp35, m)
  })
};
traverseTerm = function traverseTerm(t) {
  return eval_nofib(t)
};
traverseCon = function traverseCon(t) {
  let tmp35, tmp36;
  tmp35 = traverseTerm(t);
  tmp36 = (_t) => {
    let param0, c;
    if (_t instanceof Con1.class) {
      param0 = _t.i;
      c = param0;
      return myReturn(c)
    } else {
      throw globalThis.Error("Not a Con");
    }
  };
  return myBind(tmp35, tmp36)
};
apply = function apply(t, a) {
  let param0, param1, param01, param11, x, b, e;
  if (t instanceof Thunk1.class) {
    param0 = t.t;
    param1 = t.e;
    if (param0 instanceof Lam1.class) {
      param01 = param0.s;
      param11 = param0.t;
      x = param01;
      b = param11;
      e = param1;
      return myBind(myGet, (orig) => {
        let tmp35, tmp36, tmp37;
        tmp35 = Thunk1(a, orig);
        tmp36 = traverseTerm(b);
        tmp37 = pushVar(x, tmp35, tmp36);
        return withEnv(e, tmp37)
      })
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
eval_nofib = function eval_nofib(ter) {
  let param0, i, param01, param1, param2, c, a, b, param02, param11, u, v, param03, param12, x, b1, param04, param13, t, e, param05, param14, u1, v1, param06, x1, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40;
  if (ter instanceof Var1.class) {
    param06 = ter.s;
    x1 = param06;
    return myBind(myGet, (e1) => {
      let tmp41;
      tmp41 = lookupVar(x1);
      return myBind(tmp41, (t1) => {
        return traverseTerm(t1)
      })
    })
  } else if (ter instanceof Add1.class) {
    param05 = ter.a;
    param14 = ter.b;
    u1 = param05;
    v1 = param14;
    tmp35 = traverseCon(u1);
    return myBind(tmp35, (u_) => {
      let tmp41;
      tmp41 = traverseCon(v1);
      return myBind(tmp41, (v_) => {
        let tmp42, tmp43;
        tmp42 = u_ + v_;
        tmp43 = Con1(tmp42);
        return myReturn(tmp43)
      })
    })
  } else if (ter instanceof Thunk1.class) {
    param04 = ter.t;
    param13 = ter.e;
    t = param04;
    e = param13;
    tmp36 = traverseTerm(t);
    return withEnv(e, tmp36)
  } else if (ter instanceof Lam1.class) {
    param03 = ter.s;
    param12 = ter.t;
    x = param03;
    b1 = param12;
    return myBind(myGet, (env) => {
      let tmp41, tmp42;
      tmp41 = Lam1(x, b1);
      tmp42 = Thunk1(tmp41, env);
      return myReturn(tmp42)
    })
  } else if (ter instanceof App1.class) {
    param02 = ter.a;
    param11 = ter.b;
    u = param02;
    v = param11;
    tmp37 = traverseTerm(u);
    return myBind(tmp37, (u_) => {
      return apply(u_, v)
    })
  } else if (ter instanceof IfZero1.class) {
    param01 = ter.a;
    param1 = ter.b;
    param2 = ter.c;
    c = param01;
    a = param1;
    b = param2;
    tmp38 = traverseTerm(c);
    tmp39 = (vall) => {
      let scrut, tmp41;
      tmp41 = Con1(0);
      scrut = eqTerm(vall, tmp41);
      if (scrut === true) {
        return traverseTerm(a)
      } else {
        return traverseTerm(b)
      }
    };
    return myBind(tmp38, tmp39)
  } else if (ter instanceof Con1.class) {
    param0 = ter.i;
    i = param0;
    tmp40 = Con1(i);
    return myReturn(tmp40)
  } else if (ter instanceof Incr1.class) {
    return myBind(incr, (_dummy) => {
      let tmp41;
      tmp41 = Con1(0);
      return myReturn(tmp41)
    })
  } else {
    throw new globalThis.Error("match error");
  }
};
simpleEval = function simpleEval(env, ter) {
  let param0, param1, t, e, param01, param11, param2, c, a, b, val_, scrut, param02, param12, u, v, u_, param03, param13, x, b1, param04, param14, u1, v1, u_1, v_, param05, e1, param06, v2, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43;
  if (ter instanceof Var1.class) {
    param06 = ter.s;
    v2 = param06;
    tmp35 = lookup(v2, env);
    tmp36 = myMaybe((dummy) => {
      throw globalThis.Error("undefined var");
    }, (x1) => {
      return x1
    }, tmp35);
    return simpleEval(env, tmp36)
  } else if (ter instanceof Con1.class) {
    param05 = ter.i;
    e1 = param05;
    return Con1(e1)
  } else if (ter instanceof Incr1.class) {
    return Con1(0)
  } else if (ter instanceof Add1.class) {
    param04 = ter.a;
    param14 = ter.b;
    u1 = param04;
    v1 = param14;
    tmp37 = simpleEvalCon(env, u1);
    u_1 = tmp37;
    tmp38 = simpleEvalCon(env, v1);
    v_ = tmp38;
    tmp39 = u_1 + v_;
    return Con1(tmp39)
  } else if (ter instanceof Lam1.class) {
    param03 = ter.s;
    param13 = ter.t;
    x = param03;
    b1 = param13;
    tmp40 = Lam1(x, b1);
    return Thunk1(tmp40, env)
  } else if (ter instanceof App1.class) {
    param02 = ter.a;
    param12 = ter.b;
    u = param02;
    v = param12;
    tmp41 = simpleEval(env, u);
    u_ = tmp41;
    return simpleApply(env, u_, v)
  } else if (ter instanceof IfZero1.class) {
    param01 = ter.a;
    param11 = ter.b;
    param2 = ter.c;
    c = param01;
    a = param11;
    b = param2;
    tmp42 = simpleEval(env, c);
    val_ = tmp42;
    tmp43 = Con1(0);
    scrut = eqTerm(val_, tmp43);
    if (scrut === true) {
      return simpleEval(env, a)
    } else {
      return simpleEval(env, b)
    }
  } else if (ter instanceof Thunk1.class) {
    param0 = ter.t;
    param1 = ter.e;
    t = param0;
    e = param1;
    return simpleEval(e, t)
  } else {
    throw globalThis.Error(ter);
  }
};
simpleApply = function simpleApply(env, t, a) {
  let param0, param1, param01, param11, x, b, e, tmp35, tmp36;
  if (t instanceof Thunk1.class) {
    param0 = t.t;
    param1 = t.e;
    if (param0 instanceof Lam1.class) {
      param01 = param0.s;
      param11 = param0.t;
      x = param01;
      b = param11;
      e = param1;
      tmp35 = Thunk1(a, env);
      tmp36 = NofibPrelude.Cons([
        x,
        tmp35
      ], e);
      return simpleEval(tmp36, b)
    } else {
      throw globalThis.Error("bad application");
    }
  } else {
    throw globalThis.Error("bad application");
  }
};
simpleEvalCon = function simpleEvalCon(env, e) {
  let e_, param0, c, tmp35;
  tmp35 = simpleEval(env, e);
  e_ = tmp35;
  if (e_ instanceof Con1.class) {
    param0 = e_.i;
    c = param0;
    return c
  } else {
    throw globalThis.Error("Not a Con");
  }
};
bracket = function bracket(ot, ths, t) {
  let scrut, tmp35, tmp36;
  scrut = ths <= ot;
  if (scrut === true) {
    tmp35 = NofibPrelude.nofibStringToList(")");
    tmp36 = NofibPrelude.append(t, tmp35);
    return NofibPrelude.Cons("(", tmp36)
  } else {
    return t
  }
};
ppn = function ppn(n, ter) {
  let param0, param1, t, e, param01, param11, param2, c, a, b, param02, param12, a1, b1, param03, param13, a2, b2, param04, param14, v, t1, param05, i, param06, v1, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67;
  if (ter instanceof Var1.class) {
    param06 = ter.s;
    v1 = param06;
    return v1
  } else if (ter instanceof Con1.class) {
    param05 = ter.i;
    i = param05;
    tmp35 = NofibPrelude.stringOfInt(i);
    return NofibPrelude.nofibStringToList(tmp35)
  } else if (ter instanceof Incr1.class) {
    return NofibPrelude.nofibStringToList("INCR")
  } else if (ter instanceof Lam1.class) {
    param04 = ter.s;
    param14 = ter.t;
    v = param04;
    t1 = param14;
    tmp36 = NofibPrelude.nofibStringToList(". ");
    tmp37 = 0 - 1;
    tmp38 = ppn(tmp37, t1);
    tmp39 = NofibPrelude.append(tmp36, tmp38);
    tmp40 = NofibPrelude.append(v, tmp39);
    tmp41 = NofibPrelude.Cons("@", tmp40);
    return bracket(n, 0, tmp41)
  } else if (ter instanceof Add1.class) {
    param03 = ter.a;
    param13 = ter.b;
    a2 = param03;
    b2 = param13;
    tmp42 = ppn(1, a2);
    tmp43 = NofibPrelude.nofibStringToList(" + ");
    tmp44 = ppn(1, b2);
    tmp45 = NofibPrelude.append(tmp43, tmp44);
    tmp46 = NofibPrelude.append(tmp42, tmp45);
    return bracket(n, 1, tmp46)
  } else if (ter instanceof App1.class) {
    param02 = ter.a;
    param12 = ter.b;
    a1 = param02;
    b1 = param12;
    tmp47 = ppn(2, a1);
    tmp48 = NofibPrelude.nofibStringToList(" ");
    tmp49 = ppn(2, b1);
    tmp50 = NofibPrelude.append(tmp48, tmp49);
    tmp51 = NofibPrelude.append(tmp47, tmp50);
    return bracket(n, 2, tmp51)
  } else if (ter instanceof IfZero1.class) {
    param01 = ter.a;
    param11 = ter.b;
    param2 = ter.c;
    c = param01;
    a = param11;
    b = param2;
    tmp52 = NofibPrelude.nofibStringToList("IF ");
    tmp53 = ppn(0, c);
    tmp54 = NofibPrelude.nofibStringToList(" THEN ");
    tmp55 = ppn(0, a);
    tmp56 = NofibPrelude.nofibStringToList(" ELSE ");
    tmp57 = ppn(0, b);
    tmp58 = NofibPrelude.append(tmp56, tmp57);
    tmp59 = NofibPrelude.append(tmp55, tmp58);
    tmp60 = NofibPrelude.append(tmp54, tmp59);
    tmp61 = NofibPrelude.append(tmp53, tmp60);
    tmp62 = NofibPrelude.append(tmp52, tmp61);
    return bracket(n, 0, tmp62)
  } else if (ter instanceof Thunk1.class) {
    param0 = ter.t;
    param1 = ter.e;
    t = param0;
    e = param1;
    tmp63 = ppn(3, t);
    tmp64 = NofibPrelude.nofibStringToList("::");
    tmp65 = ppenv(e);
    tmp66 = NofibPrelude.append(tmp64, tmp65);
    tmp67 = NofibPrelude.append(tmp63, tmp66);
    return bracket(n, 0, tmp67)
  } else {
    throw new globalThis.Error("match error");
  }
};
pp = function pp(t) {
  return ppn(0, t)
};
ppenv = function ppenv(env) {
  let tmp35, tmp36, tmp37, tmp38, tmp39;
  tmp35 = NofibPrelude.nofibStringToList("[");
  tmp36 = (caseScrut) => {
    let first1, first0, v, t, tmp40, tmp41, tmp42, tmp43, tmp44;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      v = first0;
      t = first1;
      tmp40 = NofibPrelude.nofibStringToList("=");
      tmp41 = pp(t);
      tmp42 = NofibPrelude.nofibStringToList(", ");
      tmp43 = NofibPrelude.append(tmp41, tmp42);
      tmp44 = NofibPrelude.append(tmp40, tmp43);
      return NofibPrelude.append(v, tmp44)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp37 = NofibPrelude.flatMap(tmp36, env);
  tmp38 = NofibPrelude.nofibStringToList("]");
  tmp39 = NofibPrelude.append(tmp37, tmp38);
  return NofibPrelude.append(tmp35, tmp39)
};
showTerm = function showTerm(t) {
  let param0, a, tmp35, tmp36, tmp37;
  if (t instanceof Con1.class) {
    param0 = t.i;
    a = param0;
    tmp35 = NofibPrelude.nofibStringToList("Con ");
    tmp36 = NofibPrelude.stringOfInt(a);
    tmp37 = NofibPrelude.nofibStringToList(tmp36);
    return NofibPrelude.append(tmp35, tmp37)
  } else {
    throw new globalThis.Error("match error");
  }
};
ev = function ev(t) {
  let envt2, first1, first0, env, t2, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40;
  tmp35 = traverseTerm(t);
  tmp36 = myRunState(tmp35, NofibPrelude.Nil);
  envt2 = tmp36;
  if (globalThis.Array.isArray(envt2) && envt2.length === 2) {
    first0 = envt2[0];
    first1 = envt2[1];
    env = first0;
    t2 = first1;
    tmp37 = pp(t2);
    tmp38 = NofibPrelude.nofibStringToList("  ");
    tmp39 = ppenv(env);
    tmp40 = NofibPrelude.append(tmp38, tmp39);
    return NofibPrelude.append(tmp37, tmp40)
  } else {
    throw new globalThis.Error("match error");
  }
};
mainSimple = function mainSimple(args) {
  let scrut, tmp35, tmp36, tmp37, tmp38;
  scrut = NofibPrelude.null_(args);
  if (scrut === true) {
    throw globalThis.Error("Args: number-to-sum-up-to");
  } else {
    tmp35 = NofibPrelude.head(args);
    tmp36 = Con1(tmp35);
    tmp37 = App1(sum0, tmp36);
    tmp38 = simpleEval(NofibPrelude.Nil, tmp37);
    return showTerm(tmp38)
  }
};
mainMonad = function mainMonad(args) {
  let scrut, tmp35, tmp36, tmp37;
  scrut = NofibPrelude.null_(args);
  if (scrut === true) {
    throw globalThis.Error("Args: number-to-sum-up-to");
  } else {
    tmp35 = NofibPrelude.head(args);
    tmp36 = Con1(tmp35);
    tmp37 = App1(sum0, tmp36);
    return ev(tmp37)
  }
};
testLambda_nofib = function testLambda_nofib(n) {
  let tmp35, tmp36, tmp37, tmp38;
  tmp35 = NofibPrelude.Cons(n, NofibPrelude.Nil);
  tmp36 = mainSimple(tmp35);
  tmp37 = NofibPrelude.Cons(n, NofibPrelude.Nil);
  tmp38 = mainMonad(tmp37);
  return [
    tmp36,
    tmp38
  ]
};
MyState1 = function MyState(r1) { return new MyState.class(r1); };
MyState1.class = class MyState {
  constructor(r) {
    this.r = r;
  }
  toString() { return "MyState(" + globalThis.Predef.render(this.r) + ")"; }
};
tmp = MyState1((s) => {
  return [
    s,
    s
  ]
});
myGet = tmp;
Term1 = class Term {
  constructor() {}
  toString() { return "Term"; }
};
const Incr$class = class Incr extends Term1 {
  constructor() {
    super();
  }
  toString() { return "Incr"; }
}; Incr1 = new Incr$class;
Incr1.class = Incr$class;
Var1 = function Var(s1) { return new Var.class(s1); };
Var1.class = class Var extends Term1 {
  constructor(s) {
    super();
    this.s = s;
  }
  toString() { return "Var(" + globalThis.Predef.render(this.s) + ")"; }
};
Con1 = function Con(i1) { return new Con.class(i1); };
Con1.class = class Con extends Term1 {
  constructor(i) {
    super();
    this.i = i;
  }
  toString() { return "Con(" + globalThis.Predef.render(this.i) + ")"; }
};
Add1 = function Add(a1, b1) { return new Add.class(a1, b1); };
Add1.class = class Add extends Term1 {
  constructor(a, b) {
    super();
    this.a = a;
    this.b = b;
  }
  toString() { return "Add(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
};
Lam1 = function Lam(s1, t1) { return new Lam.class(s1, t1); };
Lam1.class = class Lam extends Term1 {
  constructor(s, t) {
    super();
    this.s = s;
    this.t = t;
  }
  toString() { return "Lam(" + globalThis.Predef.render(this.s) + ", " + globalThis.Predef.render(this.t) + ")"; }
};
App1 = function App(a1, b1) { return new App.class(a1, b1); };
App1.class = class App extends Term1 {
  constructor(a, b) {
    super();
    this.a = a;
    this.b = b;
  }
  toString() { return "App(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
};
IfZero1 = function IfZero(a1, b1, c1) { return new IfZero.class(a1, b1, c1); };
IfZero1.class = class IfZero extends Term1 {
  constructor(a, b, c) {
    super();
    this.a = a;
    this.b = b;
    this.c = c;
  }
  toString() { return "IfZero(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.c) + ")"; }
};
Thunk1 = function Thunk(t1, e1) { return new Thunk.class(t1, e1); };
Thunk1.class = class Thunk extends Term1 {
  constructor(t, e) {
    super();
    this.t = t;
    this.e = e;
  }
  toString() { return "Thunk(" + globalThis.Predef.render(this.t) + ", " + globalThis.Predef.render(this.e) + ")"; }
};
const Unit$class = class Unit {
  constructor() {}
  toString() { return "Unit"; }
}; Unit1 = new Unit$class;
Unit1.class = Unit$class;
tmp1 = myReturn(Unit1);
incr = tmp1;
tmp2 = NofibPrelude.nofibStringToList("x");
tmp3 = NofibPrelude.nofibStringToList("F");
tmp4 = Var1(tmp3);
tmp5 = NofibPrelude.nofibStringToList("x");
tmp6 = Var1(tmp5);
tmp7 = NofibPrelude.nofibStringToList("x");
tmp8 = Var1(tmp7);
tmp9 = App1(tmp6, tmp8);
tmp10 = App1(tmp4, tmp9);
tmp11 = Lam1(tmp2, tmp10);
lfxx = tmp11;
tmp12 = NofibPrelude.nofibStringToList("F");
tmp13 = App1(lfxx, lfxx);
tmp14 = Lam1(tmp12, tmp13);
fix = tmp14;
tmp15 = NofibPrelude.nofibStringToList("n");
tmp16 = Var1(tmp15);
tmp17 = - 1;
tmp18 = Con1(tmp17);
tmp19 = Add1(tmp16, tmp18);
nMinus1 = tmp19;
tmp20 = NofibPrelude.nofibStringToList("sum");
tmp21 = NofibPrelude.nofibStringToList("n");
tmp22 = NofibPrelude.nofibStringToList("n");
tmp23 = Var1(tmp22);
tmp24 = Con1(0);
tmp25 = NofibPrelude.nofibStringToList("n");
tmp26 = Var1(tmp25);
tmp27 = NofibPrelude.nofibStringToList("sum");
tmp28 = Var1(tmp27);
tmp29 = App1(tmp28, nMinus1);
tmp30 = Add1(tmp26, tmp29);
tmp31 = IfZero1(tmp23, tmp24, tmp30);
tmp32 = Lam1(tmp21, tmp31);
tmp33 = Lam1(tmp20, tmp32);
partialSum0 = tmp33;
tmp34 = App1(fix, partialSum0);
sum0 = tmp34;
BenchmarkPrelude.benchmark(() => {
  let tmp35;
  tmp35 = testLambda_nofib(80);
  return runtime.safeCall(tmp35.toString())
})