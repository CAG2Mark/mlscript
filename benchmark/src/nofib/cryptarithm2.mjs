import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let cryptarithm21;
cryptarithm21 = class cryptarithm2 {
  static {
    cryptarithm21 = cryptarithm2;
    let tmp, lambda, lambda1;
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
    lambda = (undefined, function (s) {
      return NofibPrelude.Cons([
        s,
        s
      ], NofibPrelude.Nil)
    });
    tmp = cryptarithm2.StateT(lambda);
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
    lambda1 = (undefined, function () {
      let tmp1;
      tmp1 = cryptarithm2.testCryptarithm2_nofib(1);
      return runtime.safeCall(tmp1.toString())
    });
    BenchmarkPrelude.benchmark(lambda1)
  }
  static unlines(ls) {
    let tmp, lambda;
    lambda = (undefined, function (x) {
      let tmp1;
      tmp1 = NofibPrelude.Cons("\n", NofibPrelude.Nil);
      return NofibPrelude.append(x, tmp1)
    });
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
    let lambda;
    lambda = (undefined, function (x, y) {
      return x === y
    });
    return NofibPrelude.deleteBy(lambda, e, xs)
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
    let tmp, lambda;
    lambda = (undefined, function (s1) {
      let tmp1, tmp2, tmp3, lambda1;
      lambda1 = (undefined, function (caseScrut) {
        let first1, first0, a1, ss, tmp4;
        if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
          first0 = caseScrut[0];
          first1 = caseScrut[1];
          a1 = first0;
          ss = first1;
          tmp4 = runtime.safeCall(f(a1));
          return cryptarithm2.runStateT(tmp4, ss)
        } else {
          throw new globalThis.Error("match error");
        }
      });
      tmp1 = lambda1;
      tmp2 = cryptarithm2.runStateT(m1, s1);
      tmp3 = NofibPrelude.map(tmp1, tmp2);
      return NofibPrelude.concat(tmp3)
    });
    tmp = lambda;
    return cryptarithm2.StateT(tmp)
  } 
  static return_(a1) {
    let lambda;
    lambda = (undefined, function (s1) {
      return NofibPrelude.Cons([
        a1,
        s1
      ], NofibPrelude.Nil)
    });
    return cryptarithm2.StateT(lambda)
  } 
  static mapM(f1, ls2) {
    let tmp, lambda;
    tmp = cryptarithm2.return_(NofibPrelude.Nil);
    lambda = (undefined, function (a2, r) {
      let tmp1, lambda1;
      tmp1 = runtime.safeCall(f1(a2));
      lambda1 = (undefined, function (x) {
        let lambda2;
        lambda2 = (undefined, function (xs1) {
          let tmp2;
          tmp2 = NofibPrelude.Cons(x, xs1);
          return cryptarithm2.return_(tmp2)
        });
        return cryptarithm2.bind(r, lambda2)
      });
      return cryptarithm2.bind(tmp1, lambda1)
    });
    return NofibPrelude.foldr(lambda, tmp, ls2)
  } 
  static lift(ls3) {
    let lambda;
    lambda = (undefined, function (s1) {
      let tmp, lambda1;
      lambda1 = (undefined, function (x) {
        return NofibPrelude.Cons([
          x,
          s1
        ], NofibPrelude.Nil)
      });
      tmp = NofibPrelude.map(lambda1, ls3);
      return NofibPrelude.concat(tmp)
    });
    return cryptarithm2.StateT(lambda)
  } 
  static execStateT(m2, s1) {
    let tmp, tmp1, tmp2, lambda;
    lambda = (undefined, function (caseScrut) {
      let first1, first0, a2, s2;
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        a2 = first0;
        s2 = first1;
        return NofibPrelude.Cons(s2, NofibPrelude.Nil)
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    tmp1 = cryptarithm2.runStateT(m2, s1);
    tmp2 = NofibPrelude.map(tmp, tmp1);
    return NofibPrelude.concat(tmp2)
  } 
  static guard(b) {
    let lambda, lambda1;
    if (b === true) {
      lambda = (undefined, function (s2) {
        return NofibPrelude.Cons([
          cryptarithm2.Unit,
          s2
        ], NofibPrelude.Nil)
      });
      return cryptarithm2.StateT(lambda)
    } else {
      lambda1 = (undefined, function (s2) {
        return NofibPrelude.Nil
      });
      return cryptarithm2.StateT(lambda1)
    }
  } 
  static put(s2) {
    let lambda;
    lambda = (undefined, function (x) {
      return NofibPrelude.Cons([
        cryptarithm2.Unit,
        s2
      ], NofibPrelude.Nil)
    });
    return cryptarithm2.StateT(lambda)
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
    let tmp, lambda;
    lambda = (undefined, function (st) {
      let xs1, tmp1, tmp2, tmp3, tmp4, tmp5, lambda1, lambda2;
      tmp1 = cryptarithm2.digits(st);
      xs1 = tmp1;
      lambda1 = (undefined, function (x) {
        let tmp6, tmp7;
        tmp6 = NofibPrelude.Cons(x, NofibPrelude.Nil);
        tmp7 = cryptarithm2.listDiff(xs1, tmp6);
        return [
          x,
          tmp7
        ]
      });
      tmp2 = lambda1;
      tmp3 = NofibPrelude.map(tmp2, xs1);
      tmp4 = cryptarithm2.lift(tmp3);
      lambda2 = (undefined, function (iis) {
        let first1, first0, i, iss, tmp6, tmp7, tmp8, tmp9, lambda3;
        if (globalThis.Array.isArray(iis) && iis.length === 2) {
          first0 = iis[0];
          first1 = iis[1];
          i = first0;
          iss = first1;
          tmp6 = cryptarithm2.digitEnv(st);
          tmp7 = NofibPrelude.Cons([
            c,
            i
          ], tmp6);
          tmp8 = cryptarithm2.Digits(iss, tmp7);
          tmp9 = cryptarithm2.put(tmp8);
          lambda3 = (undefined, function (_p) {
            return cryptarithm2.return_(i)
          });
          return cryptarithm2.bind(tmp9, lambda3)
        } else {
          throw new globalThis.Error("match error");
        }
      });
      tmp5 = lambda2;
      return cryptarithm2.bind(tmp4, tmp5)
    });
    tmp = lambda;
    return cryptarithm2.bind(cryptarithm2.get, tmp)
  } 
  static select(c1) {
    let tmp, lambda;
    lambda = (undefined, function (st) {
      let scrut, param0, r, tmp1;
      tmp1 = cryptarithm2.digitEnv(st);
      scrut = cryptarithm2.lookup(c1, tmp1);
      if (scrut instanceof NofibPrelude.Some.class) {
        param0 = scrut.x;
        r = param0;
        return cryptarithm2.return_(r)
      } else if (scrut instanceof NofibPrelude.None.class) {
        return cryptarithm2.permute(c1)
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
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
    let scrut, param0, param1, bot, botss, param01, param11, top, tmp, tmp1, lambda, lambda1, lambda2, lambda3, lambda4;
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
        lambda = (undefined, function (topNS) {
          let tmp2, tmp3;
          tmp2 = NofibPrelude.sum(topNS);
          tmp3 = tmp2 + carry;
          return cryptarithm2.return_(tmp3)
        });
        tmp = cryptarithm2.bind(tmp1, lambda);
      } else {
        throw new globalThis.Error("match error");
      }
      lambda1 = (undefined, function (topN) {
        let tmp2, tmp3, lambda5;
        tmp2 = cryptarithm2.select(bot);
        lambda5 = (undefined, function (botN) {
          let tmp4, tmp5, tmp6, tmp7, lambda6;
          tmp4 = NofibPrelude.intMod(topN, 10);
          tmp5 = tmp4 === botN;
          tmp6 = cryptarithm2.guard(tmp5);
          lambda6 = (undefined, function (_s) {
            let tmp8, tmp9;
            tmp8 = cryptarithm2.rest(tops);
            tmp9 = NofibPrelude.intDiv(topN, 10);
            return cryptarithm2.solve(tmp8, botss, tmp9)
          });
          tmp7 = lambda6;
          return cryptarithm2.bind(tmp6, tmp7)
        });
        tmp3 = lambda5;
        return cryptarithm2.bind(tmp2, tmp3)
      });
      return cryptarithm2.bind(tmp, lambda1)
    } else if (bots instanceof NofibPrelude.Nil.class) {
      if (tops instanceof NofibPrelude.Nil.class) {
        scrut = carry === 0;
        if (scrut === true) {
          return cryptarithm2.return_(cryptarithm2.Unit)
        } else {
          lambda2 = (undefined, function (_p) {
            return NofibPrelude.Nil
          });
          return cryptarithm2.StateT(lambda2)
        }
      } else {
        lambda3 = (undefined, function (_p) {
          return NofibPrelude.Nil
        });
        return cryptarithm2.StateT(lambda3)
      }
    } else {
      lambda4 = (undefined, function (_p) {
        return NofibPrelude.Nil
      });
      return cryptarithm2.StateT(lambda4)
    }
  } 
  static puzzle(top, bot) {
    let solution, answer, scrut, param0, param1, a2, env, look, expand, topVal, botVal, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, look1, expand1, lambda, lambda1, lambda2;
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
    look1 = function look(c2) {
      let tmp17;
      tmp17 = cryptarithm2.lookup(c2, env);
      return NofibPrelude.fromSome(tmp17)
    };
    look = look1;
    expand1 = function expand(ls5) {
      let lambda3;
      lambda3 = (undefined, function (a3, b1) {
        let tmp17, tmp18;
        tmp17 = a3 * 10;
        tmp18 = runtime.safeCall(look(b1));
        return tmp17 + tmp18
      });
      return NofibPrelude.foldl(lambda3, 0, ls5)
    };
    expand = expand1;
    lambda = (undefined, function (xs1) {
      return runtime.safeCall(expand(xs1))
    });
    tmp8 = NofibPrelude.map(lambda, top);
    tmp9 = NofibPrelude.sum(tmp8);
    topVal = tmp9;
    tmp10 = runtime.safeCall(expand(bot));
    botVal = tmp10;
    tmp11 = NofibPrelude.concat(top);
    tmp12 = NofibPrelude.append(tmp11, bot);
    lambda1 = (undefined, function (x, y) {
      return x === y
    });
    tmp13 = NofibPrelude.nubBy(lambda1, tmp12);
    tmp14 = NofibPrelude.listLen(tmp13);
    scrut2 = tmp14 > 10;
    if (scrut2 === true) {
      throw globalThis.Error("error");
    } else {
      scrut1 = topVal != botVal;
      if (scrut1 === true) {
        throw globalThis.Error("error");
      } else {
        lambda2 = (undefined, function (caseScrut) {
          let first1, first0, c2, i, tmp17, tmp18, tmp19, tmp20;
          if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
            first0 = caseScrut[0];
            first1 = caseScrut[1];
            c2 = first0;
            i = first1;
            tmp17 = NofibPrelude.nofibStringToList(" => ");
            tmp18 = NofibPrelude.stringOfInt(i);
            tmp19 = NofibPrelude.nofibStringToList(tmp18);
            tmp20 = NofibPrelude.append(tmp17, tmp19);
            return NofibPrelude.Cons(c2, tmp20)
          } else {
            throw new globalThis.Error("match error");
          }
        });
        tmp15 = lambda2;
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
