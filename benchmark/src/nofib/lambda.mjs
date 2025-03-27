import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let lookup2, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda14, lambda15, lambda16, lambda17, lambda18, lambda19, lambda20, lambda$, lambda$1, lambda$2, lookup2$, lambda$3, lambda$4, lambda$5, lambda$6, lambda$7, lambda$8, lambda$9, lambda$10;
lambda20 = (undefined, function (caseScrut) {
  let first1, first0, v, t, tmp, tmp1, tmp2, tmp3, tmp4;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    v = first0;
    t = first1;
    tmp = NofibPrelude.nofibStringToList("=");
    tmp1 = lambda1.pp(t);
    tmp2 = NofibPrelude.nofibStringToList(", ");
    tmp3 = NofibPrelude.append(tmp1, tmp2);
    tmp4 = NofibPrelude.append(tmp, tmp3);
    return NofibPrelude.append(v, tmp4)
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda18 = (undefined, function (dummy) {
  throw globalThis.Error("undefined var");
});
lambda19 = (undefined, function (x) {
  return x
});
lambda11 = (undefined, function (t) {
  return lambda1.traverseTerm(t)
});
lambda$10 = function lambda$(x, e) {
  let tmp;
  tmp = lambda1.lookupVar(x);
  return lambda1.myBind(tmp, lambda11)
};
lambda10 = (undefined, function (x) {
  return (e) => {
    return lambda$10(x, e)
  }
});
lambda$9 = function lambda$(u_, v_) {
  let tmp, tmp1;
  tmp = u_ + v_;
  tmp1 = lambda1.Con(tmp);
  return lambda1.myReturn(tmp1)
};
lambda13 = (undefined, function (u_) {
  return (v_) => {
    return lambda$9(u_, v_)
  }
});
lambda$8 = function lambda$(v, u_) {
  let tmp, lambda$this;
  tmp = lambda1.traverseCon(v);
  lambda$this = runtime.safeCall(lambda13(u_));
  return lambda1.myBind(tmp, lambda$this)
};
lambda12 = (undefined, function (v) {
  return (u_) => {
    return lambda$8(v, u_)
  }
});
lambda$7 = function lambda$(x, b, env) {
  let tmp, tmp1;
  tmp = lambda1.Lam(x, b);
  tmp1 = lambda1.Thunk(tmp, env);
  return lambda1.myReturn(tmp1)
};
lambda14 = (undefined, function (x, b) {
  return (env) => {
    return lambda$7(x, b, env)
  }
});
lambda$6 = function lambda$(v, u_) {
  return lambda1.apply(u_, v)
};
lambda15 = (undefined, function (v) {
  return (u_) => {
    return lambda$6(v, u_)
  }
});
lambda$5 = function lambda$(a, b, vall) {
  let scrut, tmp;
  tmp = lambda1.Con(0);
  scrut = lambda1.eqTerm(vall, tmp);
  if (scrut === true) {
    return lambda1.traverseTerm(a)
  } else {
    return lambda1.traverseTerm(b)
  }
};
lambda16 = (undefined, function (a, b) {
  return (vall) => {
    return lambda$5(a, b, vall)
  }
});
lambda17 = (undefined, function (_dummy) {
  let tmp;
  tmp = lambda1.Con(0);
  return lambda1.myReturn(tmp)
});
lambda$4 = function lambda$(a, x, b, e, orig) {
  let tmp, tmp1, tmp2;
  tmp = lambda1.Thunk(a, orig);
  tmp1 = lambda1.traverseTerm(b);
  tmp2 = lambda1.pushVar(x, tmp, tmp1);
  return lambda1.withEnv(e, tmp2)
};
lambda9 = (undefined, function (a, x, b, e) {
  return (orig) => {
    return lambda$4(a, x, b, e, orig)
  }
});
lambda8 = (undefined, function (_t) {
  let param0, c;
  if (_t instanceof lambda1.Con.class) {
    param0 = _t.i;
    c = param0;
    return lambda1.myReturn(c)
  } else {
    throw globalThis.Error("Not a Con");
  }
});
lambda$3 = function lambda$(v, t, m, env) {
  let tmp;
  tmp = NofibPrelude.Cons([
    v,
    t
  ], env);
  return lambda1.withEnv(tmp, m)
};
lambda7 = (undefined, function (v, t, m) {
  return (env) => {
    return lambda$3(v, t, m, env)
  }
});
lambda4 = (undefined, function (dummy) {
  throw globalThis.Error("undefined");
});
lambda5 = (undefined, function (x) {
  return x
});
lookup2$ = function lookup2$(v, env) {
  let tmp;
  tmp = lambda1.lookup(v, env);
  return lambda1.myMaybe(lambda4, lambda5, tmp)
};
lookup2 = function lookup2(v) {
  return (env) => {
    return lookup2$(v, env)
  }
};
lambda$2 = function lambda$(v, env) {
  let tmp;
  tmp = lookup2$(v, env);
  return lambda1.myReturn(tmp)
};
lambda6 = (undefined, function (v) {
  return (env) => {
    return lambda$2(v, env)
  }
});
lambda$1 = function lambda$(a, s) {
  return [
    s,
    a
  ]
};
lambda3 = (undefined, function (a) {
  return (s) => {
    return lambda$1(a, s)
  }
});
lambda$ = function lambda$(m, f, s) {
  let scrut, first1, first0, s_, a, tmp;
  scrut = lambda1.myRunState(m, s);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    s_ = first0;
    a = first1;
    tmp = runtime.safeCall(f(a));
    return lambda1.myRunState(tmp, s_)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda2 = (undefined, function (m, f) {
  return (s) => {
    return lambda$(m, f, s)
  }
});
lambda1 = class lambda {
  static {
    lambda1 = lambda;
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, lambda21, lambda22;
    this.MyState = function MyState(r1) {
      return new MyState.class(r1);
    };
    this.MyState.class = class MyState {
      constructor(r) {
        this.r = r;
      }
      toString() { return "MyState(" + globalThis.Predef.render(this.r) + ")"; }
    };
    lambda21 = (undefined, function (s) {
      return [
        s,
        s
      ]
    });
    tmp = lambda.MyState(lambda21);
    this.myGet = tmp;
    this.Term = class Term {
      constructor() {}
      toString() { return "Term"; }
    };
    const Incr$class = class Incr extends lambda.Term {
      constructor() {
        super();
      }
      toString() { return "Incr"; }
    };
    this.Incr = new Incr$class;
    this.Incr.class = Incr$class;
    this.Var = function Var(s1) {
      return new Var.class(s1);
    };
    this.Var.class = class Var extends lambda.Term {
      constructor(s) {
        super();
        this.s = s;
      }
      toString() { return "Var(" + globalThis.Predef.render(this.s) + ")"; }
    };
    this.Con = function Con(i1) {
      return new Con.class(i1);
    };
    this.Con.class = class Con extends lambda.Term {
      constructor(i) {
        super();
        this.i = i;
      }
      toString() { return "Con(" + globalThis.Predef.render(this.i) + ")"; }
    };
    this.Add = function Add(a1, b1) {
      return new Add.class(a1, b1);
    };
    this.Add.class = class Add extends lambda.Term {
      constructor(a, b) {
        super();
        this.a = a;
        this.b = b;
      }
      toString() { return "Add(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    this.Lam = function Lam(s1, t1) {
      return new Lam.class(s1, t1);
    };
    this.Lam.class = class Lam extends lambda.Term {
      constructor(s, t) {
        super();
        this.s = s;
        this.t = t;
      }
      toString() { return "Lam(" + globalThis.Predef.render(this.s) + ", " + globalThis.Predef.render(this.t) + ")"; }
    };
    this.App = function App(a1, b1) {
      return new App.class(a1, b1);
    };
    this.App.class = class App extends lambda.Term {
      constructor(a, b) {
        super();
        this.a = a;
        this.b = b;
      }
      toString() { return "App(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    this.IfZero = function IfZero(a1, b1, c1) {
      return new IfZero.class(a1, b1, c1);
    };
    this.IfZero.class = class IfZero extends lambda.Term {
      constructor(a, b, c) {
        super();
        this.a = a;
        this.b = b;
        this.c = c;
      }
      toString() { return "IfZero(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.c) + ")"; }
    };
    this.Thunk = function Thunk(t1, e1) {
      return new Thunk.class(t1, e1);
    };
    this.Thunk.class = class Thunk extends lambda.Term {
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
    };
    this.Unit = new Unit$class;
    this.Unit.class = Unit$class;
    tmp1 = lambda.myReturn(lambda.Unit);
    this.incr = tmp1;
    tmp2 = NofibPrelude.nofibStringToList("x");
    tmp3 = NofibPrelude.nofibStringToList("F");
    tmp4 = lambda.Var(tmp3);
    tmp5 = NofibPrelude.nofibStringToList("x");
    tmp6 = lambda.Var(tmp5);
    tmp7 = NofibPrelude.nofibStringToList("x");
    tmp8 = lambda.Var(tmp7);
    tmp9 = lambda.App(tmp6, tmp8);
    tmp10 = lambda.App(tmp4, tmp9);
    tmp11 = lambda.Lam(tmp2, tmp10);
    this.lfxx = tmp11;
    tmp12 = NofibPrelude.nofibStringToList("F");
    tmp13 = lambda.App(lambda.lfxx, lambda.lfxx);
    tmp14 = lambda.Lam(tmp12, tmp13);
    this.fix = tmp14;
    tmp15 = NofibPrelude.nofibStringToList("n");
    tmp16 = lambda.Var(tmp15);
    tmp17 = - 1;
    tmp18 = lambda.Con(tmp17);
    tmp19 = lambda.Add(tmp16, tmp18);
    this.nMinus1 = tmp19;
    tmp20 = NofibPrelude.nofibStringToList("sum");
    tmp21 = NofibPrelude.nofibStringToList("n");
    tmp22 = NofibPrelude.nofibStringToList("n");
    tmp23 = lambda.Var(tmp22);
    tmp24 = lambda.Con(0);
    tmp25 = NofibPrelude.nofibStringToList("n");
    tmp26 = lambda.Var(tmp25);
    tmp27 = NofibPrelude.nofibStringToList("sum");
    tmp28 = lambda.Var(tmp27);
    tmp29 = lambda.App(tmp28, lambda.nMinus1);
    tmp30 = lambda.Add(tmp26, tmp29);
    tmp31 = lambda.IfZero(tmp23, tmp24, tmp30);
    tmp32 = lambda.Lam(tmp21, tmp31);
    tmp33 = lambda.Lam(tmp20, tmp32);
    this.partialSum0 = tmp33;
    tmp34 = lambda.App(lambda.fix, lambda.partialSum0);
    this.sum0 = tmp34;
    lambda22 = (undefined, function () {
      let tmp35;
      tmp35 = lambda.testLambda_nofib(80);
      return runtime.safeCall(tmp35.toString())
    });
    BenchmarkPrelude.benchmark(lambda22)
  }
  static lookup(k, t) {
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
          return lambda.lookup(k, t1)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static myRunState(m, s) {
    let param0, f;
    if (m instanceof lambda.MyState.class) {
      param0 = m.r;
      f = param0;
      return runtime.safeCall(f(s))
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static myBind(m1, f) {
    let tmp;
    tmp = runtime.safeCall(lambda2(m1, f));
    return lambda.MyState(tmp)
  } 
  static myReturn(a) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda3(a));
    return lambda.MyState(lambda$this)
  } 
  static myEvalState(m2, s1) {
    let scrut, first1, first0, s_, a1;
    scrut = lambda.myRunState(m2, s1);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      s_ = first0;
      a1 = first1;
      return a1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static eqEnv(a1, b) {
    let param0, param1, first1, first0, s11, t1, b1, param01, param11, first11, first01, s2, t2, d, scrut, scrut1;
    if (a1 instanceof NofibPrelude.Nil.class) {
      if (b instanceof NofibPrelude.Nil.class) {
        return true
      } else {
        return false
      }
    } else if (a1 instanceof NofibPrelude.Cons.class) {
      param0 = a1.head;
      param1 = a1.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        s11 = first0;
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
            scrut = NofibPrelude.listEq(s11, s2);
            if (scrut === true) {
              scrut1 = lambda.eqTerm(t1, t2);
              if (scrut1 === true) {
                return lambda.eqEnv(b1, d)
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
  static eqTerm(a2, b1) {
    let param0, param1, a3, b2, param01, param11, c, d, param02, param12, param2, a4, b3, c1, param03, param13, param21, d1, e, f1, param04, param14, a5, b4, param05, param15, c2, d2, param06, param16, a6, b5, param07, param17, c3, d3, param08, param18, a7, b6, param09, param19, c4, d4, param010, a8, param011, b7, param012, a9, param013, b8, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
    if (a2 instanceof lambda.Var.class) {
      param012 = a2.s;
      a9 = param012;
      if (b1 instanceof lambda.Var.class) {
        param013 = b1.s;
        b8 = param013;
        return NofibPrelude.listEq(a9, b8)
      } else {
        return false
      }
    } else if (a2 instanceof lambda.Con.class) {
      param010 = a2.i;
      a8 = param010;
      if (b1 instanceof lambda.Con.class) {
        param011 = b1.i;
        b7 = param011;
        return a8 === b7
      } else {
        return false
      }
    } else if (a2 instanceof lambda.Incr.class) {
      if (b1 instanceof lambda.Incr.class) {
        return true
      } else {
        return false
      }
    } else if (a2 instanceof lambda.Add.class) {
      param08 = a2.a;
      param18 = a2.b;
      a7 = param08;
      b6 = param18;
      if (b6 instanceof lambda.Add.class) {
        param09 = b6.a;
        param19 = b6.b;
        c4 = param09;
        d4 = param19;
        tmp = lambda.eqTerm(a7, c4);
        tmp1 = lambda.eqTerm(b6, d4);
        return tmp && tmp1
      } else {
        return false
      }
    } else if (a2 instanceof lambda.Lam.class) {
      param06 = a2.s;
      param16 = a2.t;
      a6 = param06;
      b5 = param16;
      if (b5 instanceof lambda.Lam.class) {
        param07 = b5.s;
        param17 = b5.t;
        c3 = param07;
        d3 = param17;
        tmp2 = NofibPrelude.listEq(a6, c3);
        tmp3 = lambda.eqTerm(b5, d3);
        return tmp2 && tmp3
      } else {
        return false
      }
    } else if (a2 instanceof lambda.App.class) {
      param04 = a2.a;
      param14 = a2.b;
      a5 = param04;
      b4 = param14;
      if (b4 instanceof lambda.App.class) {
        param05 = b4.a;
        param15 = b4.b;
        c2 = param05;
        d2 = param15;
        tmp4 = lambda.eqTerm(a5, c2);
        tmp5 = lambda.eqTerm(b4, d2);
        return tmp4 && tmp5
      } else {
        return false
      }
    } else if (a2 instanceof lambda.IfZero.class) {
      param02 = a2.a;
      param12 = a2.b;
      param2 = a2.c;
      a4 = param02;
      b3 = param12;
      c1 = param2;
      if (b3 instanceof lambda.IfZero.class) {
        param03 = b3.a;
        param13 = b3.b;
        param21 = b3.c;
        d1 = param03;
        e = param13;
        f1 = param21;
        tmp6 = lambda.eqTerm(a4, d1);
        tmp7 = lambda.eqTerm(b3, e);
        tmp8 = tmp6 && tmp7;
        tmp9 = lambda.eqTerm(c1, f1);
        return tmp8 && tmp9
      } else {
        return false
      }
    } else if (a2 instanceof lambda.Thunk.class) {
      param0 = a2.t;
      param1 = a2.e;
      a3 = param0;
      b2 = param1;
      if (b2 instanceof lambda.Thunk.class) {
        param01 = b2.t;
        param11 = b2.e;
        c = param01;
        d = param11;
        tmp10 = lambda.eqTerm(a3, c);
        tmp11 = lambda.eqEnv(b2, d);
        return tmp10 && tmp11
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static myMaybe(d, f1, x) {
    let param0, x1;
    if (x instanceof NofibPrelude.Some.class) {
      param0 = x.x;
      x1 = param0;
      return runtime.safeCall(f1(x1))
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static lookupVar(v) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda6(v));
    return lambda.myBind(lambda.myGet, lambda$this)
  } 
  static withEnv(tmp, m3) {
    let tmp1;
    tmp1 = lambda.myEvalState(m3, tmp);
    return lambda.myReturn(tmp1)
  } 
  static pushVar(v1, t1, m4) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda7(v1, t1, m4));
    return lambda.myBind(lambda.myGet, lambda$this)
  } 
  static traverseTerm(t2) {
    return lambda.eval(t2)
  } 
  static traverseCon(t3) {
    let tmp1, tmp2;
    tmp1 = lambda.traverseTerm(t3);
    tmp2 = lambda8;
    return lambda.myBind(tmp1, tmp2)
  } 
  static apply(t4, a3) {
    let param0, param1, param01, param11, x1, b2, e, tmp1;
    if (t4 instanceof lambda.Thunk.class) {
      param0 = t4.t;
      param1 = t4.e;
      if (param0 instanceof lambda.Lam.class) {
        param01 = param0.s;
        param11 = param0.t;
        x1 = param01;
        b2 = param11;
        e = param1;
        tmp1 = runtime.safeCall(lambda9(a3, x1, b2, e));
        return lambda.myBind(lambda.myGet, tmp1)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static eval(ter) {
    let param0, i, param01, param1, param2, c, a4, b2, param02, param11, u, v2, param03, param12, x1, b3, param04, param13, t5, e, param05, param14, u1, v3, param06, x2, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, lambda$this, lambda$this1, lambda$this2;
    if (ter instanceof lambda.Var.class) {
      param06 = ter.s;
      x2 = param06;
      lambda$this = runtime.safeCall(lambda10(x2));
      return lambda.myBind(lambda.myGet, lambda$this)
    } else if (ter instanceof lambda.Add.class) {
      param05 = ter.a;
      param14 = ter.b;
      u1 = param05;
      v3 = param14;
      tmp1 = lambda.traverseCon(u1);
      lambda$this1 = runtime.safeCall(lambda12(v3));
      return lambda.myBind(tmp1, lambda$this1)
    } else if (ter instanceof lambda.Thunk.class) {
      param04 = ter.t;
      param13 = ter.e;
      t5 = param04;
      e = param13;
      tmp2 = lambda.traverseTerm(t5);
      return lambda.withEnv(e, tmp2)
    } else if (ter instanceof lambda.Lam.class) {
      param03 = ter.s;
      param12 = ter.t;
      x1 = param03;
      b3 = param12;
      tmp3 = runtime.safeCall(lambda14(x1, b3));
      return lambda.myBind(lambda.myGet, tmp3)
    } else if (ter instanceof lambda.App.class) {
      param02 = ter.a;
      param11 = ter.b;
      u = param02;
      v2 = param11;
      tmp4 = lambda.traverseTerm(u);
      lambda$this2 = runtime.safeCall(lambda15(v2));
      return lambda.myBind(tmp4, lambda$this2)
    } else if (ter instanceof lambda.IfZero.class) {
      param01 = ter.a;
      param1 = ter.b;
      param2 = ter.c;
      c = param01;
      a4 = param1;
      b2 = param2;
      tmp5 = lambda.traverseTerm(c);
      tmp6 = runtime.safeCall(lambda16(a4, b2));
      return lambda.myBind(tmp5, tmp6)
    } else if (ter instanceof lambda.Con.class) {
      param0 = ter.i;
      i = param0;
      tmp7 = lambda.Con(i);
      return lambda.myReturn(tmp7)
    } else if (ter instanceof lambda.Incr.class) {
      return lambda.myBind(lambda.incr, lambda17)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static simpleEval(env, ter1) {
    let param0, param1, t5, e, param01, param11, param2, c, a4, b2, val_, scrut, param02, param12, u, v2, u_, param03, param13, x1, b3, param04, param14, u1, v3, u_1, v_, param05, e1, param06, v4, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    if (ter1 instanceof lambda.Var.class) {
      param06 = ter1.s;
      v4 = param06;
      tmp1 = lambda.lookup(v4, env);
      tmp2 = lambda.myMaybe(lambda18, lambda19, tmp1);
      return lambda.simpleEval(env, tmp2)
    } else if (ter1 instanceof lambda.Con.class) {
      param05 = ter1.i;
      e1 = param05;
      return lambda.Con(e1)
    } else if (ter1 instanceof lambda.Incr.class) {
      return lambda.Con(0)
    } else if (ter1 instanceof lambda.Add.class) {
      param04 = ter1.a;
      param14 = ter1.b;
      u1 = param04;
      v3 = param14;
      tmp3 = lambda.simpleEvalCon(env, u1);
      u_1 = tmp3;
      tmp4 = lambda.simpleEvalCon(env, v3);
      v_ = tmp4;
      tmp5 = u_1 + v_;
      return lambda.Con(tmp5)
    } else if (ter1 instanceof lambda.Lam.class) {
      param03 = ter1.s;
      param13 = ter1.t;
      x1 = param03;
      b3 = param13;
      tmp6 = lambda.Lam(x1, b3);
      return lambda.Thunk(tmp6, env)
    } else if (ter1 instanceof lambda.App.class) {
      param02 = ter1.a;
      param12 = ter1.b;
      u = param02;
      v2 = param12;
      tmp7 = lambda.simpleEval(env, u);
      u_ = tmp7;
      return lambda.simpleApply(env, u_, v2)
    } else if (ter1 instanceof lambda.IfZero.class) {
      param01 = ter1.a;
      param11 = ter1.b;
      param2 = ter1.c;
      c = param01;
      a4 = param11;
      b2 = param2;
      tmp8 = lambda.simpleEval(env, c);
      val_ = tmp8;
      tmp9 = lambda.Con(0);
      scrut = lambda.eqTerm(val_, tmp9);
      if (scrut === true) {
        return lambda.simpleEval(env, a4)
      } else {
        return lambda.simpleEval(env, b2)
      }
    } else if (ter1 instanceof lambda.Thunk.class) {
      param0 = ter1.t;
      param1 = ter1.e;
      t5 = param0;
      e = param1;
      return lambda.simpleEval(e, t5)
    } else {
      throw globalThis.Error(ter1);
    }
  } 
  static simpleApply(env1, t5, a4) {
    let param0, param1, param01, param11, x1, b2, e, tmp1, tmp2;
    if (t5 instanceof lambda.Thunk.class) {
      param0 = t5.t;
      param1 = t5.e;
      if (param0 instanceof lambda.Lam.class) {
        param01 = param0.s;
        param11 = param0.t;
        x1 = param01;
        b2 = param11;
        e = param1;
        tmp1 = lambda.Thunk(a4, env1);
        tmp2 = NofibPrelude.Cons([
          x1,
          tmp1
        ], e);
        return lambda.simpleEval(tmp2, b2)
      } else {
        throw globalThis.Error("bad application");
      }
    } else {
      throw globalThis.Error("bad application");
    }
  } 
  static simpleEvalCon(env2, e) {
    let e_, param0, c, tmp1;
    tmp1 = lambda.simpleEval(env2, e);
    e_ = tmp1;
    if (e_ instanceof lambda.Con.class) {
      param0 = e_.i;
      c = param0;
      return c
    } else {
      throw globalThis.Error("Not a Con");
    }
  } 
  static bracket(ot, ths, t6) {
    let scrut, tmp1, tmp2;
    scrut = ths <= ot;
    if (scrut === true) {
      tmp1 = NofibPrelude.nofibStringToList(")");
      tmp2 = NofibPrelude.append(t6, tmp1);
      return NofibPrelude.Cons("(", tmp2)
    } else {
      return t6
    }
  } 
  static ppn(n, ter2) {
    let param0, param1, t7, e1, param01, param11, param2, c, a5, b2, param02, param12, a6, b3, param03, param13, a7, b4, param04, param14, v2, t8, param05, i, param06, v3, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33;
    if (ter2 instanceof lambda.Var.class) {
      param06 = ter2.s;
      v3 = param06;
      return v3
    } else if (ter2 instanceof lambda.Con.class) {
      param05 = ter2.i;
      i = param05;
      tmp1 = NofibPrelude.stringOfInt(i);
      return NofibPrelude.nofibStringToList(tmp1)
    } else if (ter2 instanceof lambda.Incr.class) {
      return NofibPrelude.nofibStringToList("INCR")
    } else if (ter2 instanceof lambda.Lam.class) {
      param04 = ter2.s;
      param14 = ter2.t;
      v2 = param04;
      t8 = param14;
      tmp2 = NofibPrelude.nofibStringToList(". ");
      tmp3 = 0 - 1;
      tmp4 = lambda.ppn(tmp3, t8);
      tmp5 = NofibPrelude.append(tmp2, tmp4);
      tmp6 = NofibPrelude.append(v2, tmp5);
      tmp7 = NofibPrelude.Cons("@", tmp6);
      return lambda.bracket(n, 0, tmp7)
    } else if (ter2 instanceof lambda.Add.class) {
      param03 = ter2.a;
      param13 = ter2.b;
      a7 = param03;
      b4 = param13;
      tmp8 = lambda.ppn(1, a7);
      tmp9 = NofibPrelude.nofibStringToList(" + ");
      tmp10 = lambda.ppn(1, b4);
      tmp11 = NofibPrelude.append(tmp9, tmp10);
      tmp12 = NofibPrelude.append(tmp8, tmp11);
      return lambda.bracket(n, 1, tmp12)
    } else if (ter2 instanceof lambda.App.class) {
      param02 = ter2.a;
      param12 = ter2.b;
      a6 = param02;
      b3 = param12;
      tmp13 = lambda.ppn(2, a6);
      tmp14 = NofibPrelude.nofibStringToList(" ");
      tmp15 = lambda.ppn(2, b3);
      tmp16 = NofibPrelude.append(tmp14, tmp15);
      tmp17 = NofibPrelude.append(tmp13, tmp16);
      return lambda.bracket(n, 2, tmp17)
    } else if (ter2 instanceof lambda.IfZero.class) {
      param01 = ter2.a;
      param11 = ter2.b;
      param2 = ter2.c;
      c = param01;
      a5 = param11;
      b2 = param2;
      tmp18 = NofibPrelude.nofibStringToList("IF ");
      tmp19 = lambda.ppn(0, c);
      tmp20 = NofibPrelude.nofibStringToList(" THEN ");
      tmp21 = lambda.ppn(0, a5);
      tmp22 = NofibPrelude.nofibStringToList(" ELSE ");
      tmp23 = lambda.ppn(0, b2);
      tmp24 = NofibPrelude.append(tmp22, tmp23);
      tmp25 = NofibPrelude.append(tmp21, tmp24);
      tmp26 = NofibPrelude.append(tmp20, tmp25);
      tmp27 = NofibPrelude.append(tmp19, tmp26);
      tmp28 = NofibPrelude.append(tmp18, tmp27);
      return lambda.bracket(n, 0, tmp28)
    } else if (ter2 instanceof lambda.Thunk.class) {
      param0 = ter2.t;
      param1 = ter2.e;
      t7 = param0;
      e1 = param1;
      tmp29 = lambda.ppn(3, t7);
      tmp30 = NofibPrelude.nofibStringToList("::");
      tmp31 = lambda.ppenv(e1);
      tmp32 = NofibPrelude.append(tmp30, tmp31);
      tmp33 = NofibPrelude.append(tmp29, tmp32);
      return lambda.bracket(n, 0, tmp33)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static pp(t7) {
    return lambda.ppn(0, t7)
  } 
  static ppenv(env3) {
    let tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp1 = NofibPrelude.nofibStringToList("[");
    tmp2 = lambda20;
    tmp3 = NofibPrelude.flatMap(tmp2, env3);
    tmp4 = NofibPrelude.nofibStringToList("]");
    tmp5 = NofibPrelude.append(tmp3, tmp4);
    return NofibPrelude.append(tmp1, tmp5)
  } 
  static showTerm(t8) {
    let param0, a5, tmp1, tmp2, tmp3;
    if (t8 instanceof lambda.Con.class) {
      param0 = t8.i;
      a5 = param0;
      tmp1 = NofibPrelude.nofibStringToList("Con ");
      tmp2 = NofibPrelude.stringOfInt(a5);
      tmp3 = NofibPrelude.nofibStringToList(tmp2);
      return NofibPrelude.append(tmp1, tmp3)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static ev(t9) {
    let envt2, first1, first0, env4, t21, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp1 = lambda.traverseTerm(t9);
    tmp2 = lambda.myRunState(tmp1, NofibPrelude.Nil);
    envt2 = tmp2;
    if (globalThis.Array.isArray(envt2) && envt2.length === 2) {
      first0 = envt2[0];
      first1 = envt2[1];
      env4 = first0;
      t21 = first1;
      tmp3 = lambda.pp(t21);
      tmp4 = NofibPrelude.nofibStringToList("  ");
      tmp5 = lambda.ppenv(env4);
      tmp6 = NofibPrelude.append(tmp4, tmp5);
      return NofibPrelude.append(tmp3, tmp6)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static mainSimple(args) {
    let scrut, tmp1, tmp2, tmp3, tmp4;
    scrut = NofibPrelude.null_(args);
    if (scrut === true) {
      throw globalThis.Error("Args: number-to-sum-up-to");
    } else {
      tmp1 = NofibPrelude.head(args);
      tmp2 = lambda.Con(tmp1);
      tmp3 = lambda.App(lambda.sum0, tmp2);
      tmp4 = lambda.simpleEval(NofibPrelude.Nil, tmp3);
      return lambda.showTerm(tmp4)
    }
  } 
  static mainMonad(args1) {
    let scrut, tmp1, tmp2, tmp3;
    scrut = NofibPrelude.null_(args1);
    if (scrut === true) {
      throw globalThis.Error("Args: number-to-sum-up-to");
    } else {
      tmp1 = NofibPrelude.head(args1);
      tmp2 = lambda.Con(tmp1);
      tmp3 = lambda.App(lambda.sum0, tmp2);
      return lambda.ev(tmp3)
    }
  } 
  static testLambda_nofib(n1) {
    let tmp1, tmp2, tmp3, tmp4;
    tmp1 = NofibPrelude.Cons(n1, NofibPrelude.Nil);
    tmp2 = lambda.mainSimple(tmp1);
    tmp3 = NofibPrelude.Cons(n1, NofibPrelude.Nil);
    tmp4 = lambda.mainMonad(tmp3);
    return [
      tmp2,
      tmp4
    ]
  }
  static toString() { return "lambda"; }
};
let lambda = lambda1; export default lambda;
