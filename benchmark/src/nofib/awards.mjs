import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let awards1;
awards1 = class awards {
  static {
    awards1 = awards;
    let lambda;
    lambda = (undefined, function () {
      return awards.testAwards_nofib(100)
    });
    BenchmarkPrelude.benchmark(lambda)
  }
  static delete_(xs, e) {
    let lambda;
    lambda = (undefined, function (x, y) {
      return x == y
    });
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
    let lambda;
    lambda = (undefined, function (a1, b) {
      let lambda1, lambda2, lambda3;
      lambda1 = (undefined, function (a2, b1) {
        return a2 < b1
      });
      lambda2 = (undefined, function (a2, b1) {
        return a2 > b1
      });
      lambda3 = (undefined, function (a2, b1) {
        let lambda4, lambda5;
        lambda4 = (undefined, function (a3, b2) {
          return a3 < b2
        });
        lambda5 = (undefined, function (a3, b2) {
          return a3 > b2
        });
        return NofibPrelude.ltList(a2, b1, lambda4, lambda5)
      });
      return NofibPrelude.ltTup2(a1, b, lambda1, lambda2, lambda3)
    });
    return awards.qsort(lambda, l, NofibPrelude.Nil)
  } 
  static perms(m, nns) {
    let param0, param1, n, ns, scrut, tmp, tmp1, tmp2, tmp3, lambda, lambda1;
    if (nns instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      scrut = m == 1;
      if (scrut === true) {
        lambda = (undefined, function (x2) {
          return NofibPrelude.Cons(x2, NofibPrelude.Nil)
        });
        return NofibPrelude.map(lambda, nns)
      } else {
        if (nns instanceof NofibPrelude.Cons.class) {
          param0 = nns.head;
          param1 = nns.tail;
          n = param0;
          ns = param1;
          tmp = m - 1;
          tmp1 = awards.perms(tmp, ns);
          lambda1 = (undefined, function (x2) {
            return NofibPrelude.Cons(n, x2)
          });
          tmp2 = NofibPrelude.map(lambda1, tmp1);
          tmp3 = awards.perms(m, ns);
          return NofibPrelude.append(tmp2, tmp3)
        } else {
          throw new globalThis.Error("match error");
        }
      }
    }
  } 
  static awards(scores) {
    let award, atleast, sumscores, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, lambda;
    atleast = function atleast(threshold) {
      let tmp6, lambda1;
      lambda1 = (undefined, function (caseScrut) {
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
      });
      tmp6 = lambda1;
      return NofibPrelude.filter(tmp6, sumscores)
    };
    award = function award(name_threshold) {
      let first1, first0, name, threshold, tmp6, tmp7, lambda1;
      if (globalThis.Array.isArray(name_threshold) && name_threshold.length === 2) {
        first0 = name_threshold[0];
        first1 = name_threshold[1];
        name = first0;
        threshold = first1;
        tmp6 = atleast(threshold);
        tmp7 = awards.sort(tmp6);
        lambda1 = (undefined, function (ps) {
          return [
            name,
            ps
          ]
        });
        return NofibPrelude.map(lambda1, tmp7)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = awards.perms(3, scores);
    lambda = (undefined, function (p) {
      let tmp6;
      tmp6 = NofibPrelude.sum(p);
      return [
        tmp6,
        p
      ]
    });
    tmp1 = NofibPrelude.map(lambda, tmp);
    sumscores = tmp1;
    tmp2 = award([
      "Gold",
      70
    ]);
    tmp3 = award([
      "Silver",
      60
    ]);
    tmp4 = award([
      "Bronze",
      50
    ]);
    tmp5 = NofibPrelude.append(tmp3, tmp4);
    return NofibPrelude.append(tmp2, tmp5)
  } 
  static findawards(scores1) {
    let scrut, param0, param1, head_, tail_, first1, first0, award, first11, first01, sum_, perm, tmp, tmp1;
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
        award = first0;
        if (globalThis.Array.isArray(first1) && first1.length === 2) {
          first01 = first1[0];
          first11 = first1[1];
          sum_ = first01;
          perm = first11;
          tmp = awards.listDiff(scores1, perm);
          tmp1 = awards.findawards(tmp);
          return NofibPrelude.Cons([
            award,
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
    let tmp, lambda;
    lambda = (undefined, function (caseScrut) {
      let first1, first0, name, scores2, tmp1;
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        name = first0;
        scores2 = first1;
        tmp1 = awards.findawards(scores2);
        return [
          name,
          tmp1
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
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
    let tmp, tmp1, lambda;
    lambda = (undefined, function (x2) {
      let tmp2, tmp3, tmp4;
      tmp2 = NofibPrelude.intMod(x2, 100);
      tmp3 = awards.competitors(tmp2);
      tmp4 = awards.findallawards(tmp3);
      return BenchmarkPrelude.print(tmp4)
    });
    tmp = lambda;
    tmp1 = NofibPrelude.enumFromTo(1, n);
    return NofibPrelude.map(tmp, tmp1)
  }
  static toString() { return "awards"; }
};
let awards = awards1; export default awards;
