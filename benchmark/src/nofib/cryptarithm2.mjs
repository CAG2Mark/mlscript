import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let lookup, listDiff, mapM, puzzle, select, execStateT, put, lift, digitEnv, delete_, return_, solve, Digits1, permute, StateT1, rest, digits, unlines, bind, testCryptarithm2_nofib, guard, runStateT, Unit1, get, tmp, lambda, lambda1;
unlines = function unlines(ls) {
  let tmp1, lambda2;
  lambda2 = (undefined, function (x) {
    let tmp2;
    tmp2 = NofibPrelude.Cons("\n", NofibPrelude.Nil);
    return NofibPrelude.append(x, tmp2)
  });
  tmp1 = NofibPrelude.map(lambda2, ls);
  return NofibPrelude.concat(tmp1)
};
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
      scrut = k === x;
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
delete_ = function delete_(xs, e) {
  let lambda2;
  lambda2 = (undefined, function (x, y) {
    return x === y
  });
  return NofibPrelude.deleteBy(lambda2, e, xs)
};
listDiff = function listDiff(a, ls) {
  return NofibPrelude.foldl(delete_, a, ls)
};
runStateT = function runStateT(m, s) {
  let param0, run;
  if (m instanceof StateT1.class) {
    param0 = m.run;
    run = param0;
    return runtime.safeCall(run(s))
  } else {
    throw new globalThis.Error("match error");
  }
};
bind = function bind(m, f) {
  let tmp1, lambda2;
  lambda2 = (undefined, function (s) {
    let tmp2, tmp3, tmp4, lambda3;
    lambda3 = (undefined, function (caseScrut) {
      let first1, first0, a, ss, tmp5;
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        a = first0;
        ss = first1;
        tmp5 = runtime.safeCall(f(a));
        return runStateT(tmp5, ss)
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp2 = lambda3;
    tmp3 = runStateT(m, s);
    tmp4 = NofibPrelude.map(tmp2, tmp3);
    return NofibPrelude.concat(tmp4)
  });
  tmp1 = lambda2;
  return StateT1(tmp1)
};
return_ = function return_(a) {
  let lambda2;
  lambda2 = (undefined, function (s) {
    return NofibPrelude.Cons([
      a,
      s
    ], NofibPrelude.Nil)
  });
  return StateT1(lambda2)
};
mapM = function mapM(f, ls) {
  let tmp1, lambda2;
  tmp1 = return_(NofibPrelude.Nil);
  lambda2 = (undefined, function (a, r) {
    let tmp2, lambda3;
    tmp2 = runtime.safeCall(f(a));
    lambda3 = (undefined, function (x) {
      let lambda4;
      lambda4 = (undefined, function (xs) {
        let tmp3;
        tmp3 = NofibPrelude.Cons(x, xs);
        return return_(tmp3)
      });
      return bind(r, lambda4)
    });
    return bind(tmp2, lambda3)
  });
  return NofibPrelude.foldr(lambda2, tmp1, ls)
};
lift = function lift(ls) {
  let lambda2;
  lambda2 = (undefined, function (s) {
    let tmp1, lambda3;
    lambda3 = (undefined, function (x) {
      return NofibPrelude.Cons([
        x,
        s
      ], NofibPrelude.Nil)
    });
    tmp1 = NofibPrelude.map(lambda3, ls);
    return NofibPrelude.concat(tmp1)
  });
  return StateT1(lambda2)
};
execStateT = function execStateT(m, s) {
  let tmp1, tmp2, tmp3, lambda2;
  lambda2 = (undefined, function (caseScrut) {
    let first1, first0, a, s1;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      a = first0;
      s1 = first1;
      return NofibPrelude.Cons(s1, NofibPrelude.Nil)
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp1 = lambda2;
  tmp2 = runStateT(m, s);
  tmp3 = NofibPrelude.map(tmp1, tmp2);
  return NofibPrelude.concat(tmp3)
};
guard = function guard(b) {
  let lambda2, lambda3;
  if (b === true) {
    lambda2 = (undefined, function (s) {
      return NofibPrelude.Cons([
        Unit1,
        s
      ], NofibPrelude.Nil)
    });
    return StateT1(lambda2)
  } else {
    lambda3 = (undefined, function (s) {
      return NofibPrelude.Nil
    });
    return StateT1(lambda3)
  }
};
put = function put(s) {
  let lambda2;
  lambda2 = (undefined, function (x) {
    return NofibPrelude.Cons([
      Unit1,
      s
    ], NofibPrelude.Nil)
  });
  return StateT1(lambda2)
};
digits = function digits(d) {
  let param0, param1, a, b;
  if (d instanceof Digits1.class) {
    param0 = d.i;
    param1 = d.c;
    a = param0;
    b = param1;
    return a
  } else {
    throw new globalThis.Error("match error");
  }
};
digitEnv = function digitEnv(d) {
  let param0, param1, a, b;
  if (d instanceof Digits1.class) {
    param0 = d.i;
    param1 = d.c;
    a = param0;
    b = param1;
    return b
  } else {
    throw new globalThis.Error("match error");
  }
};
permute = function permute(c) {
  let tmp1, lambda2;
  lambda2 = (undefined, function (st) {
    let xs, tmp2, tmp3, tmp4, tmp5, lambda3, lambda4;
    tmp2 = digits(st);
    xs = tmp2;
    lambda3 = (undefined, function (x) {
      let tmp6, tmp7;
      tmp6 = NofibPrelude.Cons(x, NofibPrelude.Nil);
      tmp7 = listDiff(xs, tmp6);
      return [
        x,
        tmp7
      ]
    });
    tmp3 = NofibPrelude.map(lambda3, xs);
    tmp4 = lift(tmp3);
    lambda4 = (undefined, function (iis) {
      let first1, first0, i, iss, tmp6, tmp7, tmp8, tmp9, lambda5;
      if (globalThis.Array.isArray(iis) && iis.length === 2) {
        first0 = iis[0];
        first1 = iis[1];
        i = first0;
        iss = first1;
        tmp6 = digitEnv(st);
        tmp7 = NofibPrelude.Cons([
          c,
          i
        ], tmp6);
        tmp8 = Digits1(iss, tmp7);
        tmp9 = put(tmp8);
        lambda5 = (undefined, function (_p) {
          return return_(i)
        });
        return bind(tmp9, lambda5)
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp5 = lambda4;
    return bind(tmp4, tmp5)
  });
  tmp1 = lambda2;
  return bind(get, tmp1)
};
select = function select(c) {
  let tmp1, lambda2;
  lambda2 = (undefined, function (st) {
    let scrut, param0, r, tmp2;
    tmp2 = digitEnv(st);
    scrut = lookup(c, tmp2);
    if (scrut instanceof NofibPrelude.Some.class) {
      param0 = scrut.x;
      r = param0;
      return return_(r)
    } else if (scrut instanceof NofibPrelude.None.class) {
      return permute(c)
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp1 = lambda2;
  return bind(get, tmp1)
};
rest = function rest(ls) {
  let param0, param1, x, xs;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    x = param0;
    xs = param1;
    return xs
  } else {
    throw new globalThis.Error("match error");
  }
};
solve = function solve(tops, bots, carry) {
  let scrut, param0, param1, bot, botss, param01, param11, top, tmp1, tmp2, lambda2, lambda3, lambda4, lambda5, lambda6;
  if (bots instanceof NofibPrelude.Cons.class) {
    param0 = bots.head;
    param1 = bots.tail;
    bot = param0;
    botss = param1;
    if (tops instanceof NofibPrelude.Nil.class) {
      tmp1 = return_(carry);
    } else if (tops instanceof NofibPrelude.Cons.class) {
      param01 = tops.head;
      param11 = tops.tail;
      top = param01;
      tmp2 = mapM(select, top);
      lambda2 = (undefined, function (topNS) {
        let tmp3, tmp4;
        tmp3 = NofibPrelude.sum(topNS);
        tmp4 = tmp3 + carry;
        return return_(tmp4)
      });
      tmp1 = bind(tmp2, lambda2);
    } else {
      throw new globalThis.Error("match error");
    }
    lambda3 = (undefined, function (topN) {
      let tmp3, tmp4, lambda7;
      tmp3 = select(bot);
      lambda7 = (undefined, function (botN) {
        let tmp5, tmp6, tmp7, tmp8, lambda8;
        tmp5 = NofibPrelude.intMod(topN, 10);
        tmp6 = tmp5 === botN;
        tmp7 = guard(tmp6);
        lambda8 = (undefined, function (_s) {
          let tmp9, tmp10;
          tmp9 = rest(tops);
          tmp10 = NofibPrelude.intDiv(topN, 10);
          return solve(tmp9, botss, tmp10)
        });
        tmp8 = lambda8;
        return bind(tmp7, tmp8)
      });
      tmp4 = lambda7;
      return bind(tmp3, tmp4)
    });
    return bind(tmp1, lambda3)
  } else if (bots instanceof NofibPrelude.Nil.class) {
    if (tops instanceof NofibPrelude.Nil.class) {
      scrut = carry === 0;
      if (scrut === true) {
        return return_(Unit1)
      } else {
        lambda4 = (undefined, function (_p) {
          return NofibPrelude.Nil
        });
        return StateT1(lambda4)
      }
    } else {
      lambda5 = (undefined, function (_p) {
        return NofibPrelude.Nil
      });
      return StateT1(lambda5)
    }
  } else {
    lambda6 = (undefined, function (_p) {
      return NofibPrelude.Nil
    });
    return StateT1(lambda6)
  }
};
puzzle = function puzzle(top, bot) {
  let solution, answer, scrut, param0, param1, a, env, look, expand, topVal, botVal, scrut1, scrut2, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, look1, expand1, lambda2, lambda3, lambda4;
  tmp1 = NofibPrelude.map(NofibPrelude.reverse, top);
  tmp2 = NofibPrelude.transpose(tmp1);
  tmp3 = NofibPrelude.reverse(bot);
  tmp4 = solve(tmp2, tmp3, 0);
  solution = tmp4;
  tmp5 = NofibPrelude.enumFromTo(0, 9);
  tmp6 = Digits1(tmp5, NofibPrelude.Nil);
  scrut = execStateT(solution, tmp6);
  if (scrut instanceof NofibPrelude.Cons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    a = param0;
    tmp7 = a;
  } else {
    throw new globalThis.Error("match error");
  }
  answer = tmp7;
  tmp8 = digitEnv(answer);
  env = tmp8;
  look1 = function look(c) {
    let tmp18;
    tmp18 = lookup(c, env);
    return NofibPrelude.fromSome(tmp18)
  };
  look = look1;
  expand1 = function expand(ls) {
    let lambda5;
    lambda5 = (undefined, function (a1, b) {
      let tmp18, tmp19;
      tmp18 = a1 * 10;
      tmp19 = runtime.safeCall(look(b));
      return tmp18 + tmp19
    });
    return NofibPrelude.foldl(lambda5, 0, ls)
  };
  expand = expand1;
  lambda2 = (undefined, function (xs) {
    return runtime.safeCall(expand(xs))
  });
  tmp9 = NofibPrelude.map(lambda2, top);
  tmp10 = NofibPrelude.sum(tmp9);
  topVal = tmp10;
  tmp11 = runtime.safeCall(expand(bot));
  botVal = tmp11;
  tmp12 = NofibPrelude.concat(top);
  tmp13 = NofibPrelude.append(tmp12, bot);
  lambda3 = (undefined, function (x, y) {
    return x === y
  });
  tmp14 = NofibPrelude.nubBy(lambda3, tmp13);
  tmp15 = NofibPrelude.listLen(tmp14);
  scrut2 = tmp15 > 10;
  if (scrut2 === true) {
    throw globalThis.Error("error");
  } else {
    scrut1 = topVal != botVal;
    if (scrut1 === true) {
      throw globalThis.Error("error");
    } else {
      lambda4 = (undefined, function (caseScrut) {
        let first1, first0, c, i, tmp18, tmp19, tmp20, tmp21;
        if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
          first0 = caseScrut[0];
          first1 = caseScrut[1];
          c = first0;
          i = first1;
          tmp18 = NofibPrelude.nofibStringToList(" => ");
          tmp19 = NofibPrelude.stringOfInt(i);
          tmp20 = NofibPrelude.nofibStringToList(tmp19);
          tmp21 = NofibPrelude.append(tmp18, tmp20);
          return NofibPrelude.Cons(c, tmp21)
        } else {
          throw new globalThis.Error("match error");
        }
      });
      tmp16 = lambda4;
      tmp17 = NofibPrelude.map(tmp16, env);
      return unlines(tmp17)
    }
  }
};
testCryptarithm2_nofib = function testCryptarithm2_nofib(n) {
  let args, scrut, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15;
  tmp1 = NofibPrelude.nofibStringToList("THIRTY");
  tmp2 = NofibPrelude.nofibStringToList("TWELVE");
  tmp3 = NofibPrelude.nofibStringToList("TWELVE");
  tmp4 = NofibPrelude.nofibStringToList("TWELVE");
  tmp5 = NofibPrelude.nofibStringToList("TWELVE");
  tmp6 = NofibPrelude.nofibStringToList("TWELVE");
  scrut = n > 999999;
  if (scrut === true) {
    tmp7 = NofibPrelude.nofibStringToList("1");
  } else {
    tmp7 = NofibPrelude.Nil;
  }
  tmp8 = NofibPrelude.append(tmp6, tmp7);
  tmp9 = NofibPrelude.Cons(tmp8, NofibPrelude.Nil);
  tmp10 = NofibPrelude.Cons(tmp5, tmp9);
  tmp11 = NofibPrelude.Cons(tmp4, tmp10);
  tmp12 = NofibPrelude.Cons(tmp3, tmp11);
  tmp13 = NofibPrelude.Cons(tmp2, tmp12);
  tmp14 = NofibPrelude.Cons(tmp1, tmp13);
  args = tmp14;
  tmp15 = NofibPrelude.nofibStringToList("NINETY");
  return puzzle(args, tmp15)
};
const Unit$class = class Unit {
  constructor() {}
  toString() { return "Unit"; }
}; Unit1 = new Unit$class;
Unit1.class = Unit$class;
StateT1 = function StateT(run1) {
  return new StateT.class(run1);
};
StateT1.class = class StateT {
  constructor(run) {
    this.run = run;
  }
  toString() { return "StateT(" + globalThis.Predef.render(this.run) + ")"; }
};
lambda = (undefined, function (s) {
  return NofibPrelude.Cons([
    s,
    s
  ], NofibPrelude.Nil)
});
tmp = StateT1(lambda);
get = tmp;
Digits1 = function Digits(i1, c1) {
  return new Digits.class(i1, c1);
};
Digits1.class = class Digits {
  constructor(i, c) {
    this.i = i;
    this.c = c;
  }
  toString() { return "Digits(" + globalThis.Predef.render(this.i) + ", " + globalThis.Predef.render(this.c) + ")"; }
};
lambda1 = (undefined, function () {
  let tmp1;
  tmp1 = testCryptarithm2_nofib(1);
  return runtime.safeCall(tmp1.toString())
});
BenchmarkPrelude.benchmark(lambda1)