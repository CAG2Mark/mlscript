import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let cryptarithm21, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda14, lambda15, lambda16, lambda17, lambda18, lambda19, lambda20, lambda21, lambda22, lambda23, lambda24, lambda25, look, expand, lambda26, lambda27, lambda28, lambda29, lambda$, lambda$1, lambda$2, lambda$3, lambda$4, lambda$5, lambda$6, lambda$7, lambda$8, lambda$9, lambda$10, lambda$11, lambda$12, lambda$13, lambda$14, lambda$15, lambda$16, lambda$17, lambda$18, expand$, lambda$19, look$;
look$ = function look$(env, c) {
  let tmp;
  tmp = cryptarithm21.lookup(c, env);
  return NofibPrelude.fromSome(tmp)
};
look = function look(env) {
  return (c) => {
    return look$(env, c)
  }
};
lambda$19 = function lambda$(look1, a, b) {
  let tmp, tmp1;
  tmp = a * 10;
  tmp1 = runtime.safeCall(look1(b));
  return tmp + tmp1
};
lambda26 = (undefined, function (look1) {
  return (a, b) => {
    return lambda$19(look1, a, b)
  }
});
expand$ = function expand$(look1, ls) {
  let lambda$this;
  lambda$this = runtime.safeCall(lambda26(look1));
  return NofibPrelude.foldl(lambda$this, 0, ls)
};
expand = function expand(look1) {
  return (ls) => {
    return expand$(look1, ls)
  }
};
lambda$18 = function lambda$(expand1, xs) {
  return runtime.safeCall(expand1(xs))
};
lambda27 = (undefined, function (expand1) {
  return (xs) => {
    return lambda$18(expand1, xs)
  }
});
lambda28 = (undefined, function (x, y) {
  return x === y
});
lambda29 = (undefined, function (caseScrut) {
  let first1, first0, c, i, tmp, tmp1, tmp2, tmp3;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    c = first0;
    i = first1;
    tmp = NofibPrelude.nofibStringToList(" => ");
    tmp1 = NofibPrelude.stringOfInt(i);
    tmp2 = NofibPrelude.nofibStringToList(tmp1);
    tmp3 = NofibPrelude.append(tmp, tmp2);
    return NofibPrelude.Cons(c, tmp3)
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda$17 = function lambda$(carry, topNS) {
  let tmp, tmp1;
  tmp = NofibPrelude.sum(topNS);
  tmp1 = tmp + carry;
  return cryptarithm21.return_(tmp1)
};
lambda19 = (undefined, function (carry) {
  return (topNS) => {
    return lambda$17(carry, topNS)
  }
});
lambda$16 = function lambda$(tops, botss, topN, _s) {
  let tmp, tmp1;
  tmp = cryptarithm21.rest(tops);
  tmp1 = NofibPrelude.intDiv(topN, 10);
  return cryptarithm21.solve(tmp, botss, tmp1)
};
lambda22 = (undefined, function (tops, botss, topN) {
  return (_s) => {
    return lambda$16(tops, botss, topN, _s)
  }
});
lambda$15 = function lambda$(tops, botss, topN, botN) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.intMod(topN, 10);
  tmp1 = tmp === botN;
  tmp2 = cryptarithm21.guard(tmp1);
  tmp3 = runtime.safeCall(lambda22(tops, botss, topN));
  return cryptarithm21.bind(tmp2, tmp3)
};
lambda21 = (undefined, function (tops, botss, topN) {
  return (botN) => {
    return lambda$15(tops, botss, topN, botN)
  }
});
lambda$14 = function lambda$(tops, bot, botss, topN) {
  let tmp, tmp1;
  tmp = cryptarithm21.select(bot);
  tmp1 = runtime.safeCall(lambda21(tops, botss, topN));
  return cryptarithm21.bind(tmp, tmp1)
};
lambda20 = (undefined, function (tops, bot, botss) {
  return (topN) => {
    return lambda$14(tops, bot, botss, topN)
  }
});
lambda23 = (undefined, function (_p) {
  return NofibPrelude.Nil
});
lambda24 = (undefined, function (_p) {
  return NofibPrelude.Nil
});
lambda25 = (undefined, function (_p) {
  return NofibPrelude.Nil
});
lambda$13 = function lambda$(c, st) {
  let scrut, param0, r, tmp;
  tmp = cryptarithm21.digitEnv(st);
  scrut = cryptarithm21.lookup(c, tmp);
  if (scrut instanceof NofibPrelude.Some.class) {
    param0 = scrut.x;
    r = param0;
    return cryptarithm21.return_(r)
  } else if (scrut instanceof NofibPrelude.None.class) {
    return cryptarithm21.permute(c)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda18 = (undefined, function (c) {
  return (st) => {
    return lambda$13(c, st)
  }
});
lambda$12 = function lambda$(xs, x) {
  let tmp, tmp1;
  tmp = NofibPrelude.Cons(x, NofibPrelude.Nil);
  tmp1 = cryptarithm21.listDiff(xs, tmp);
  return [
    x,
    tmp1
  ]
};
lambda15 = (undefined, function (xs) {
  return (x) => {
    return lambda$12(xs, x)
  }
});
lambda$11 = function lambda$(i, _p) {
  return cryptarithm21.return_(i)
};
lambda17 = (undefined, function (i) {
  return (_p) => {
    return lambda$11(i, _p)
  }
});
lambda$10 = function lambda$(c, st, iis) {
  let first1, first0, i, iss, tmp, tmp1, tmp2, tmp3, lambda$this;
  if (globalThis.Array.isArray(iis) && iis.length === 2) {
    first0 = iis[0];
    first1 = iis[1];
    i = first0;
    iss = first1;
    tmp = cryptarithm21.digitEnv(st);
    tmp1 = NofibPrelude.Cons([
      c,
      i
    ], tmp);
    tmp2 = cryptarithm21.Digits(iss, tmp1);
    tmp3 = cryptarithm21.put(tmp2);
    lambda$this = runtime.safeCall(lambda17(i));
    return cryptarithm21.bind(tmp3, lambda$this)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda16 = (undefined, function (c, st) {
  return (iis) => {
    return lambda$10(c, st, iis)
  }
});
lambda$9 = function lambda$(c, st) {
  let xs, tmp, tmp1, tmp2, tmp3, tmp4;
  tmp = cryptarithm21.digits(st);
  xs = tmp;
  tmp1 = runtime.safeCall(lambda15(xs));
  tmp2 = NofibPrelude.map(tmp1, xs);
  tmp3 = cryptarithm21.lift(tmp2);
  tmp4 = runtime.safeCall(lambda16(c, st));
  return cryptarithm21.bind(tmp3, tmp4)
};
lambda14 = (undefined, function (c) {
  return (st) => {
    return lambda$9(c, st)
  }
});
lambda$8 = function lambda$(s, x) {
  return NofibPrelude.Cons([
    cryptarithm21.Unit,
    s
  ], NofibPrelude.Nil)
};
lambda13 = (undefined, function (s) {
  return (x) => {
    return lambda$8(s, x)
  }
});
lambda11 = (undefined, function (s) {
  return NofibPrelude.Cons([
    cryptarithm21.Unit,
    s
  ], NofibPrelude.Nil)
});
lambda12 = (undefined, function (s) {
  return NofibPrelude.Nil
});
lambda10 = (undefined, function (caseScrut) {
  let first1, first0, a, s;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    a = first0;
    s = first1;
    return NofibPrelude.Cons(s, NofibPrelude.Nil)
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda$7 = function lambda$(s, x) {
  return NofibPrelude.Cons([
    x,
    s
  ], NofibPrelude.Nil)
};
lambda9 = (undefined, function (s) {
  return (x) => {
    return lambda$7(s, x)
  }
});
lambda$6 = function lambda$(ls, s) {
  let tmp, lambda$this;
  lambda$this = runtime.safeCall(lambda9(s));
  tmp = NofibPrelude.map(lambda$this, ls);
  return NofibPrelude.concat(tmp)
};
lambda8 = (undefined, function (ls) {
  return (s) => {
    return lambda$6(ls, s)
  }
});
lambda$5 = function lambda$(x, xs) {
  let tmp;
  tmp = NofibPrelude.Cons(x, xs);
  return cryptarithm21.return_(tmp)
};
lambda7 = (undefined, function (x) {
  return (xs) => {
    return lambda$5(x, xs)
  }
});
lambda$4 = function lambda$(r, x) {
  let lambda$this;
  lambda$this = runtime.safeCall(lambda7(x));
  return cryptarithm21.bind(r, lambda$this)
};
lambda6 = (undefined, function (r) {
  return (x) => {
    return lambda$4(r, x)
  }
});
lambda$3 = function lambda$(f, a, r) {
  let tmp, lambda$this;
  tmp = runtime.safeCall(f(a));
  lambda$this = runtime.safeCall(lambda6(r));
  return cryptarithm21.bind(tmp, lambda$this)
};
lambda5 = (undefined, function (f) {
  return (a, r) => {
    return lambda$3(f, a, r)
  }
});
lambda$2 = function lambda$(a, s) {
  return NofibPrelude.Cons([
    a,
    s
  ], NofibPrelude.Nil)
};
lambda4 = (undefined, function (a) {
  return (s) => {
    return lambda$2(a, s)
  }
});
lambda$1 = function lambda$(f, caseScrut) {
  let first1, first0, a, ss, tmp;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    a = first0;
    ss = first1;
    tmp = runtime.safeCall(f(a));
    return cryptarithm21.runStateT(tmp, ss)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda3 = (undefined, function (f) {
  return (caseScrut) => {
    return lambda$1(f, caseScrut)
  }
});
lambda$ = function lambda$(m, f, s) {
  let tmp, tmp1, tmp2;
  tmp = runtime.safeCall(lambda3(f));
  tmp1 = cryptarithm21.runStateT(m, s);
  tmp2 = NofibPrelude.map(tmp, tmp1);
  return NofibPrelude.concat(tmp2)
};
lambda2 = (undefined, function (m, f) {
  return (s) => {
    return lambda$(m, f, s)
  }
});
lambda1 = (undefined, function (x, y) {
  return x === y
});
lambda = (undefined, function (x) {
  let tmp;
  tmp = NofibPrelude.Cons("\n", NofibPrelude.Nil);
  return NofibPrelude.append(x, tmp)
});
cryptarithm21 = class cryptarithm2 {
  static {
    cryptarithm21 = cryptarithm2;
    let tmp, lambda30, lambda31;
    const Unit$class = class Unit {
      constructor() {}
      toString() { return "Unit"; }
    };
    this.Unit = new Unit$class;
    this.Unit.class = Unit$class;
    this.StateT = function StateT(run1) {
      return new StateT.class(run1);
    };
    this.StateT.class = class StateT {
      constructor(run) {
        this.run = run;
      }
      toString() { return "StateT(" + globalThis.Predef.render(this.run) + ")"; }
    };
    lambda30 = (undefined, function (s) {
      return NofibPrelude.Cons([
        s,
        s
      ], NofibPrelude.Nil)
    });
    tmp = cryptarithm2.StateT(lambda30);
    this.get = tmp;
    this.Digits = function Digits(i1, c1) {
      return new Digits.class(i1, c1);
    };
    this.Digits.class = class Digits {
      constructor(i, c) {
        this.i = i;
        this.c = c;
      }
      toString() { return "Digits(" + globalThis.Predef.render(this.i) + ", " + globalThis.Predef.render(this.c) + ")"; }
    };
    lambda31 = (undefined, function () {
      let tmp1;
      tmp1 = cryptarithm2.testCryptarithm2_nofib(1);
      return runtime.safeCall(tmp1.toString())
    });
    BenchmarkPrelude.benchmark(lambda31)
  }
  static unlines(ls) {
    let tmp;
    tmp = NofibPrelude.map(lambda, ls);
    return NofibPrelude.concat(tmp)
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
        scrut = k === x;
        if (scrut === true) {
          return NofibPrelude.Some(v)
        } else {
          return cryptarithm2.lookup(k, t1)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static delete_(xs, e) {
    return NofibPrelude.deleteBy(lambda1, e, xs)
  } 
  static listDiff(a, ls1) {
    return NofibPrelude.foldl(cryptarithm2.delete_, a, ls1)
  } 
  static runStateT(m, s) {
    let param0, run;
    if (m instanceof cryptarithm2.StateT.class) {
      param0 = m.run;
      run = param0;
      return runtime.safeCall(run(s))
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static bind(m1, f) {
    let tmp;
    tmp = runtime.safeCall(lambda2(m1, f));
    return cryptarithm2.StateT(tmp)
  } 
  static return_(a1) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda4(a1));
    return cryptarithm2.StateT(lambda$this)
  } 
  static mapM(f1, ls2) {
    let tmp, lambda$this;
    tmp = cryptarithm2.return_(NofibPrelude.Nil);
    lambda$this = runtime.safeCall(lambda5(f1));
    return NofibPrelude.foldr(lambda$this, tmp, ls2)
  } 
  static lift(ls3) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda8(ls3));
    return cryptarithm2.StateT(lambda$this)
  } 
  static execStateT(m2, s1) {
    let tmp, tmp1, tmp2;
    tmp = lambda10;
    tmp1 = cryptarithm2.runStateT(m2, s1);
    tmp2 = NofibPrelude.map(tmp, tmp1);
    return NofibPrelude.concat(tmp2)
  } 
  static guard(b) {
    if (b === true) {
      return cryptarithm2.StateT(lambda11)
    } else {
      return cryptarithm2.StateT(lambda12)
    }
  } 
  static put(s2) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda13(s2));
    return cryptarithm2.StateT(lambda$this)
  } 
  static digits(d) {
    let param0, param1, a2, b1;
    if (d instanceof cryptarithm2.Digits.class) {
      param0 = d.i;
      param1 = d.c;
      a2 = param0;
      b1 = param1;
      return a2
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static digitEnv(d1) {
    let param0, param1, a2, b1;
    if (d1 instanceof cryptarithm2.Digits.class) {
      param0 = d1.i;
      param1 = d1.c;
      a2 = param0;
      b1 = param1;
      return b1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static permute(c) {
    let tmp;
    tmp = runtime.safeCall(lambda14(c));
    return cryptarithm2.bind(cryptarithm2.get, tmp)
  } 
  static select(c1) {
    let tmp;
    tmp = runtime.safeCall(lambda18(c1));
    return cryptarithm2.bind(cryptarithm2.get, tmp)
  } 
  static rest(ls4) {
    let param0, param1, x, xs1;
    if (ls4 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls4 instanceof NofibPrelude.Cons.class) {
      param0 = ls4.head;
      param1 = ls4.tail;
      x = param0;
      xs1 = param1;
      return xs1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static solve(tops, bots, carry) {
    let scrut, param0, param1, bot, botss, param01, param11, top, tmp, tmp1, lambda$this, lambda$this1;
    if (bots instanceof NofibPrelude.Cons.class) {
      param0 = bots.head;
      param1 = bots.tail;
      bot = param0;
      botss = param1;
      if (tops instanceof NofibPrelude.Nil.class) {
        tmp = cryptarithm2.return_(carry);
      } else if (tops instanceof NofibPrelude.Cons.class) {
        param01 = tops.head;
        param11 = tops.tail;
        top = param01;
        tmp1 = cryptarithm2.mapM(cryptarithm2.select, top);
        lambda$this = runtime.safeCall(lambda19(carry));
        tmp = cryptarithm2.bind(tmp1, lambda$this);
      } else {
        throw new globalThis.Error("match error");
      }
      lambda$this1 = runtime.safeCall(lambda20(tops, bot, botss));
      return cryptarithm2.bind(tmp, lambda$this1)
    } else if (bots instanceof NofibPrelude.Nil.class) {
      if (tops instanceof NofibPrelude.Nil.class) {
        scrut = carry === 0;
        if (scrut === true) {
          return cryptarithm2.return_(cryptarithm2.Unit)
        } else {
          return cryptarithm2.StateT(lambda23)
        }
      } else {
        return cryptarithm2.StateT(lambda24)
      }
    } else {
      return cryptarithm2.StateT(lambda25)
    }
  } 
  static puzzle(top, bot) {
    let solution, answer, scrut, param0, param1, a2, env, look1, expand1, topVal, botVal, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, lambda$this;
    tmp = NofibPrelude.map(NofibPrelude.reverse, top);
    tmp1 = NofibPrelude.transpose(tmp);
    tmp2 = NofibPrelude.reverse(bot);
    tmp3 = cryptarithm2.solve(tmp1, tmp2, 0);
    solution = tmp3;
    tmp4 = NofibPrelude.enumFromTo(0, 9);
    tmp5 = cryptarithm2.Digits(tmp4, NofibPrelude.Nil);
    scrut = cryptarithm2.execStateT(solution, tmp5);
    if (scrut instanceof NofibPrelude.Cons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      a2 = param0;
      tmp6 = a2;
    } else {
      throw new globalThis.Error("match error");
    }
    answer = tmp6;
    tmp7 = cryptarithm2.digitEnv(answer);
    env = tmp7;
    look1 = runtime.safeCall(look(env));
    expand1 = runtime.safeCall(expand(look1));
    lambda$this = runtime.safeCall(lambda27(expand1));
    tmp8 = NofibPrelude.map(lambda$this, top);
    tmp9 = NofibPrelude.sum(tmp8);
    topVal = tmp9;
    tmp10 = runtime.safeCall(expand1(bot));
    botVal = tmp10;
    tmp11 = NofibPrelude.concat(top);
    tmp12 = NofibPrelude.append(tmp11, bot);
    tmp13 = NofibPrelude.nubBy(lambda28, tmp12);
    tmp14 = NofibPrelude.listLen(tmp13);
    scrut2 = tmp14 > 10;
    if (scrut2 === true) {
      throw globalThis.Error("error");
    } else {
      scrut1 = topVal != botVal;
      if (scrut1 === true) {
        throw globalThis.Error("error");
      } else {
        tmp15 = lambda29;
        tmp16 = NofibPrelude.map(tmp15, env);
        return cryptarithm2.unlines(tmp16)
      }
    }
  } 
  static testCryptarithm2_nofib(n) {
    let args, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
    tmp = NofibPrelude.nofibStringToList("THIRTY");
    tmp1 = NofibPrelude.nofibStringToList("TWELVE");
    tmp2 = NofibPrelude.nofibStringToList("TWELVE");
    tmp3 = NofibPrelude.nofibStringToList("TWELVE");
    tmp4 = NofibPrelude.nofibStringToList("TWELVE");
    tmp5 = NofibPrelude.nofibStringToList("TWELVE");
    scrut = n > 999999;
    if (scrut === true) {
      tmp6 = NofibPrelude.nofibStringToList("1");
    } else {
      tmp6 = NofibPrelude.Nil;
    }
    tmp7 = NofibPrelude.append(tmp5, tmp6);
    tmp8 = NofibPrelude.Cons(tmp7, NofibPrelude.Nil);
    tmp9 = NofibPrelude.Cons(tmp4, tmp8);
    tmp10 = NofibPrelude.Cons(tmp3, tmp9);
    tmp11 = NofibPrelude.Cons(tmp2, tmp10);
    tmp12 = NofibPrelude.Cons(tmp1, tmp11);
    tmp13 = NofibPrelude.Cons(tmp, tmp12);
    args = tmp13;
    tmp14 = NofibPrelude.nofibStringToList("NINETY");
    return cryptarithm2.puzzle(args, tmp14)
  }
  static toString() { return "cryptarithm2"; }
};
let cryptarithm2 = cryptarithm21; export default cryptarithm2;
