import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let delete_, findallawards, qpart, qsort, competitors, rqpart, listDiff, testAwards_nofib, perms, rqsort, awards_, sort, findawards, lambda;
delete_ = function delete_(xs, e) {
  let lambda1;
  lambda1 = (undefined, function (x, y) {
    return x == y
  });
  return NofibPrelude.deleteBy(lambda1, e, xs)
};
listDiff = function listDiff(a, ls) {
  return NofibPrelude.foldl(delete_, a, ls)
};
qsort = function qsort(le, ls, r) {
  let param0, param1, x, xs, x1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return r
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    x1 = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(x1, r)
    } else {
      x = param0;
      xs = param1;
      return qpart(le, x, xs, NofibPrelude.Nil, NofibPrelude.Nil, r)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
qpart = function qpart(le, x, ys, rlt, rge, r) {
  let param0, param1, y, ys1, scrut, tmp, tmp1, tmp2, tmp3;
  if (ys instanceof NofibPrelude.Nil.class) {
    tmp = rqsort(le, rge, r);
    tmp1 = NofibPrelude.Cons(x, tmp);
    return rqsort(le, rlt, tmp1)
  } else if (ys instanceof NofibPrelude.Cons.class) {
    param0 = ys.head;
    param1 = ys.tail;
    y = param0;
    ys1 = param1;
    scrut = runtime.safeCall(le(x, y));
    if (scrut === true) {
      tmp2 = NofibPrelude.Cons(y, rge);
      return qpart(le, x, ys1, rlt, tmp2, r)
    } else {
      tmp3 = NofibPrelude.Cons(y, rlt);
      return qpart(le, x, ys1, tmp3, rge, r)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
rqsort = function rqsort(le, ls, r) {
  let param0, param1, x, xs, x1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return r
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    x1 = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(x1, r)
    } else {
      x = param0;
      xs = param1;
      return rqpart(le, x, xs, NofibPrelude.Nil, NofibPrelude.Nil, r)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
rqpart = function rqpart(le, x, yss, rle, rgt, r) {
  let param0, param1, y, ys, scrut, tmp, tmp1, tmp2, tmp3;
  if (yss instanceof NofibPrelude.Nil.class) {
    tmp = qsort(le, rgt, r);
    tmp1 = NofibPrelude.Cons(x, tmp);
    return qsort(le, rle, tmp1)
  } else if (yss instanceof NofibPrelude.Cons.class) {
    param0 = yss.head;
    param1 = yss.tail;
    y = param0;
    ys = param1;
    scrut = runtime.safeCall(le(y, x));
    if (scrut === true) {
      tmp2 = NofibPrelude.Cons(y, rle);
      return rqpart(le, x, ys, tmp2, rgt, r)
    } else {
      tmp3 = NofibPrelude.Cons(y, rgt);
      return rqpart(le, x, ys, rle, tmp3, r)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
sort = function sort(l) {
  let lambda1;
  lambda1 = (undefined, function (a, b) {
    let lambda2, lambda3, lambda4;
    lambda2 = (undefined, function (a1, b1) {
      return a1 < b1
    });
    lambda3 = (undefined, function (a1, b1) {
      return a1 > b1
    });
    lambda4 = (undefined, function (a1, b1) {
      let lambda5, lambda6;
      lambda5 = (undefined, function (a2, b2) {
        return a2 < b2
      });
      lambda6 = (undefined, function (a2, b2) {
        return a2 > b2
      });
      return NofibPrelude.ltList(a1, b1, lambda5, lambda6)
    });
    return NofibPrelude.ltTup2(a, b, lambda2, lambda3, lambda4)
  });
  return qsort(lambda1, l, NofibPrelude.Nil)
};
perms = function perms(m, nns) {
  let param0, param1, n, ns, scrut, tmp, tmp1, tmp2, tmp3, lambda1, lambda2;
  if (nns instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else {
    scrut = m == 1;
    if (scrut === true) {
      lambda1 = (undefined, function (x) {
        return NofibPrelude.Cons(x, NofibPrelude.Nil)
      });
      return NofibPrelude.map(lambda1, nns)
    } else {
      if (nns instanceof NofibPrelude.Cons.class) {
        param0 = nns.head;
        param1 = nns.tail;
        n = param0;
        ns = param1;
        tmp = m - 1;
        tmp1 = perms(tmp, ns);
        lambda2 = (undefined, function (x) {
          return NofibPrelude.Cons(n, x)
        });
        tmp2 = NofibPrelude.map(lambda2, tmp1);
        tmp3 = perms(m, ns);
        return NofibPrelude.append(tmp2, tmp3)
      } else {
        throw new globalThis.Error("match error");
      }
    }
  }
};
awards_ = function awards_(scores) {
  let award, atleast, sumscores, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, lambda1;
  atleast = function atleast(threshold) {
    let tmp6, lambda2;
    lambda2 = (undefined, function (caseScrut) {
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
    tmp6 = lambda2;
    return NofibPrelude.filter(tmp6, sumscores)
  };
  award = function award(name_threshold) {
    let first1, first0, name, threshold, tmp6, tmp7, lambda2;
    if (globalThis.Array.isArray(name_threshold) && name_threshold.length === 2) {
      first0 = name_threshold[0];
      first1 = name_threshold[1];
      name = first0;
      threshold = first1;
      tmp6 = atleast(threshold);
      tmp7 = sort(tmp6);
      lambda2 = (undefined, function (ps) {
        return [
          name,
          ps
        ]
      });
      return NofibPrelude.map(lambda2, tmp7)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp = perms(3, scores);
  lambda1 = (undefined, function (p) {
    let tmp6;
    tmp6 = NofibPrelude.sum(p);
    return [
      tmp6,
      p
    ]
  });
  tmp1 = NofibPrelude.map(lambda1, tmp);
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
};
findawards = function findawards(scores) {
  let scrut, param0, param1, head_, tail_, first1, first0, award, first11, first01, sum_, perm, tmp, tmp1;
  scrut = awards_(scores);
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
        tmp = listDiff(scores, perm);
        tmp1 = findawards(tmp);
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
};
findallawards = function findallawards(competitors1) {
  let tmp, lambda1;
  lambda1 = (undefined, function (caseScrut) {
    let first1, first0, name, scores, tmp1;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      name = first0;
      scores = first1;
      tmp1 = findawards(scores);
      return [
        name,
        tmp1
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp = lambda1;
  return NofibPrelude.map(tmp, competitors1)
};
competitors = function competitors(i) {
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
};
testAwards_nofib = function testAwards_nofib(n) {
  let tmp, tmp1, lambda1;
  lambda1 = (undefined, function (x) {
    let tmp2, tmp3, tmp4;
    tmp2 = NofibPrelude.intMod(x, 100);
    tmp3 = competitors(tmp2);
    tmp4 = findallawards(tmp3);
    return BenchmarkPrelude.print(tmp4)
  });
  tmp = lambda1;
  tmp1 = NofibPrelude.enumFromTo(1, n);
  return NofibPrelude.map(tmp, tmp1)
};
lambda = (undefined, function () {
  return testAwards_nofib(100)
});
BenchmarkPrelude.benchmark(lambda)