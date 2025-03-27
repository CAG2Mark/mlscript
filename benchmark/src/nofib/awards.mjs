import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let award, atleast, awards1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda$, award$, lambda$1, atleast$, lambda$2;
lambda13 = (undefined, function (x) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.intMod(x, 100);
  tmp1 = awards1.competitors(tmp);
  tmp2 = awards1.findallawards(tmp1);
  return BenchmarkPrelude.print(tmp2)
});
lambda12 = (undefined, function (caseScrut) {
  let first1, first0, name, scores, tmp;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    name = first0;
    scores = first1;
    tmp = awards1.findawards(scores);
    return [
      name,
      tmp
    ]
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda$2 = function lambda$(threshold, caseScrut) {
  let first1, first0, sum_, p;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    sum_ = first0;
    p = first1;
    return sum_ >= threshold
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda9 = (undefined, function (threshold) {
  return (caseScrut) => {
    return lambda$2(threshold, caseScrut)
  }
});
atleast$ = function atleast$(sumscores, threshold) {
  let tmp;
  tmp = runtime.safeCall(lambda9(threshold));
  return NofibPrelude.filter(tmp, sumscores)
};
atleast = function atleast(sumscores) {
  return (threshold) => {
    return atleast$(sumscores, threshold)
  }
};
lambda$1 = function lambda$(name, ps) {
  return [
    name,
    ps
  ]
};
lambda10 = (undefined, function (name) {
  return (ps) => {
    return lambda$1(name, ps)
  }
});
award$ = function award$(sumscores, name_threshold) {
  let first1, first0, name, threshold, tmp, tmp1, lambda$this;
  if (globalThis.Array.isArray(name_threshold) && name_threshold.length === 2) {
    first0 = name_threshold[0];
    first1 = name_threshold[1];
    name = first0;
    threshold = first1;
    tmp = atleast$(sumscores, threshold);
    tmp1 = awards1.sort(tmp);
    lambda$this = runtime.safeCall(lambda10(name));
    return NofibPrelude.map(lambda$this, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
award = function award(sumscores) {
  return (name_threshold) => {
    return award$(sumscores, name_threshold)
  }
};
lambda11 = (undefined, function (p) {
  let tmp;
  tmp = NofibPrelude.sum(p);
  return [
    tmp,
    p
  ]
});
lambda7 = (undefined, function (x) {
  return NofibPrelude.Cons(x, NofibPrelude.Nil)
});
lambda$ = function lambda$(n, x) {
  return NofibPrelude.Cons(n, x)
};
lambda8 = (undefined, function (n) {
  return (x) => {
    return lambda$(n, x)
  }
});
lambda2 = (undefined, function (a, b) {
  return a < b
});
lambda3 = (undefined, function (a, b) {
  return a > b
});
lambda5 = (undefined, function (a, b) {
  return a < b
});
lambda6 = (undefined, function (a, b) {
  return a > b
});
lambda4 = (undefined, function (a, b) {
  return NofibPrelude.ltList(a, b, lambda5, lambda6)
});
lambda1 = (undefined, function (a, b) {
  return NofibPrelude.ltTup2(a, b, lambda2, lambda3, lambda4)
});
lambda = (undefined, function (x, y) {
  return x == y
});
awards1 = class awards {
  static {
    awards1 = awards;
    let lambda14;
    lambda14 = (undefined, function () {
      return awards.testAwards_nofib(100)
    });
    BenchmarkPrelude.benchmark(lambda14)
  }
  static delete_(xs, e) {
    return NofibPrelude.deleteBy(lambda, e, xs)
  } 
  static listDiff(a, ls) {
    return NofibPrelude.foldl(awards.delete_, a, ls)
  } 
  static qsort(le, ls1, r) {
    let param0, param1, x, xs1, x1;
    if (ls1 instanceof NofibPrelude.Nil.class) {
      return r
    } else if (ls1 instanceof NofibPrelude.Cons.class) {
      param0 = ls1.head;
      param1 = ls1.tail;
      x1 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Cons(x1, r)
      } else {
        x = param0;
        xs1 = param1;
        return awards.qpart(le, x, xs1, NofibPrelude.Nil, NofibPrelude.Nil, r)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static qpart(le1, x, ys, rlt, rge, r1) {
    let param0, param1, y, ys1, scrut, tmp, tmp1, tmp2, tmp3;
    if (ys instanceof NofibPrelude.Nil.class) {
      tmp = awards.rqsort(le1, rge, r1);
      tmp1 = NofibPrelude.Cons(x, tmp);
      return awards.rqsort(le1, rlt, tmp1)
    } else if (ys instanceof NofibPrelude.Cons.class) {
      param0 = ys.head;
      param1 = ys.tail;
      y = param0;
      ys1 = param1;
      scrut = runtime.safeCall(le1(x, y));
      if (scrut === true) {
        tmp2 = NofibPrelude.Cons(y, rge);
        return awards.qpart(le1, x, ys1, rlt, tmp2, r1)
      } else {
        tmp3 = NofibPrelude.Cons(y, rlt);
        return awards.qpart(le1, x, ys1, tmp3, rge, r1)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static rqsort(le2, ls2, r2) {
    let param0, param1, x1, xs1, x2;
    if (ls2 instanceof NofibPrelude.Nil.class) {
      return r2
    } else if (ls2 instanceof NofibPrelude.Cons.class) {
      param0 = ls2.head;
      param1 = ls2.tail;
      x2 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Cons(x2, r2)
      } else {
        x1 = param0;
        xs1 = param1;
        return awards.rqpart(le2, x1, xs1, NofibPrelude.Nil, NofibPrelude.Nil, r2)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static rqpart(le3, x1, yss, rle, rgt, r3) {
    let param0, param1, y, ys1, scrut, tmp, tmp1, tmp2, tmp3;
    if (yss instanceof NofibPrelude.Nil.class) {
      tmp = awards.qsort(le3, rgt, r3);
      tmp1 = NofibPrelude.Cons(x1, tmp);
      return awards.qsort(le3, rle, tmp1)
    } else if (yss instanceof NofibPrelude.Cons.class) {
      param0 = yss.head;
      param1 = yss.tail;
      y = param0;
      ys1 = param1;
      scrut = runtime.safeCall(le3(y, x1));
      if (scrut === true) {
        tmp2 = NofibPrelude.Cons(y, rle);
        return awards.rqpart(le3, x1, ys1, tmp2, rgt, r3)
      } else {
        tmp3 = NofibPrelude.Cons(y, rgt);
        return awards.rqpart(le3, x1, ys1, rle, tmp3, r3)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static sort(l) {
    return awards.qsort(lambda1, l, NofibPrelude.Nil)
  } 
  static perms(m, nns) {
    let param0, param1, n, ns, scrut, tmp, tmp1, tmp2, tmp3, lambda$this;
    if (nns instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      scrut = m == 1;
      if (scrut === true) {
        return NofibPrelude.map(lambda7, nns)
      } else {
        if (nns instanceof NofibPrelude.Cons.class) {
          param0 = nns.head;
          param1 = nns.tail;
          n = param0;
          ns = param1;
          tmp = m - 1;
          tmp1 = awards.perms(tmp, ns);
          lambda$this = runtime.safeCall(lambda8(n));
          tmp2 = NofibPrelude.map(lambda$this, tmp1);
          tmp3 = awards.perms(m, ns);
          return NofibPrelude.append(tmp2, tmp3)
        } else {
          throw new globalThis.Error("match error");
        }
      }
    }
  } 
  static awards(scores) {
    let sumscores, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = awards.perms(3, scores);
    tmp1 = NofibPrelude.map(lambda11, tmp);
    sumscores = tmp1;
    tmp2 = award$(sumscores, [
      "Gold",
      70
    ]);
    tmp3 = award$(sumscores, [
      "Silver",
      60
    ]);
    tmp4 = award$(sumscores, [
      "Bronze",
      50
    ]);
    tmp5 = NofibPrelude.append(tmp3, tmp4);
    return NofibPrelude.append(tmp2, tmp5)
  } 
  static findawards(scores1) {
    let scrut, param0, param1, head_, tail_, first1, first0, award1, first11, first01, sum_, perm, tmp, tmp1;
    scrut = awards.awards(scores1);
    if (scrut instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (scrut instanceof NofibPrelude.Cons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      head_ = param0;
      tail_ = param1;
      if (globalThis.Array.isArray(head_) && head_.length === 2) {
        first0 = head_[0];
        first1 = head_[1];
        award1 = first0;
        if (globalThis.Array.isArray(first1) && first1.length === 2) {
          first01 = first1[0];
          first11 = first1[1];
          sum_ = first01;
          perm = first11;
          tmp = awards.listDiff(scores1, perm);
          tmp1 = awards.findawards(tmp);
          return NofibPrelude.Cons([
            award1,
            [
              sum_,
              perm
            ]
          ], tmp1)
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
  static findallawards(competitors) {
    let tmp;
    tmp = lambda12;
    return NofibPrelude.map(tmp, competitors)
  } 
  static competitors(i) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = NofibPrelude.list(35, 27, 40, i, 34, 21);
    tmp1 = NofibPrelude.list(23, 19, 45, i, 17, 10, 5, 8, 14);
    tmp2 = NofibPrelude.list(1, 18, i, 20, 21, 19, 34, 8, 16, 21);
    tmp3 = NofibPrelude.list(9, 23, 17, 54, i, 41, 9, 18, 14);
    return NofibPrelude.list([
      "Simon",
      tmp
    ], [
      "Hans",
      tmp1
    ], [
      "Phil",
      tmp2
    ], [
      "Kevin",
      tmp3
    ])
  } 
  static testAwards_nofib(n) {
    let tmp, tmp1;
    tmp = lambda13;
    tmp1 = NofibPrelude.enumFromTo(1, n);
    return NofibPrelude.map(tmp, tmp1)
  }
  static toString() { return "awards"; }
};
let awards = awards1; export default awards;
