import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let null__, stepr, all, unlines, break_, paras, feasible, cons_, fmt, fmtWith, unparas, tile, snoc_, unformat, format, init_, fits, glue, unparse, testPara_nofib, len_tl, scan1, head_, par0, ceildiv, thd3, single, par3, width_tl, tails, cost, startr, last_, parse, tail_, formats, fst3, unwords, words, cost_tl, minWith, single_, isSpace, fold1, new_, fitH, lines, width, snd3, maxw, optw, nil_, test, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, lambda;
unwords = function unwords(ws) {
  let go, param0, param1, w, ws1, tmp21;
  if (ws instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ws instanceof NofibPrelude.Cons.class) {
    param0 = ws.head;
    param1 = ws.tail;
    w = param0;
    ws1 = param1;
    go = function go(vs) {
      let param01, param11, v, vs1, tmp22, tmp23;
      if (vs instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (vs instanceof NofibPrelude.Cons.class) {
        param01 = vs.head;
        param11 = vs.tail;
        v = param01;
        vs1 = param11;
        tmp22 = go(vs1);
        tmp23 = NofibPrelude.append(v, tmp22);
        return NofibPrelude.Cons(" ", tmp23)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp21 = go(ws1);
    return NofibPrelude.append(w, tmp21)
  } else {
    throw new globalThis.Error("match error");
  }
};
break_ = function break_(p, xs) {
  let param0, param1, x, xs1, scrut, first1, first0, ys, zs, scrut1, tmp21, tmp22;
  if (xs instanceof NofibPrelude.Nil.class) {
    return [
      NofibPrelude.Nil,
      NofibPrelude.Nil
    ]
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs1 = param1;
    scrut1 = runtime.safeCall(p(x));
    if (scrut1 === true) {
      tmp21 = NofibPrelude.Cons(x, xs1);
      return [
        NofibPrelude.Nil,
        tmp21
      ]
    } else {
      scrut = NofibPrelude.break_(p, xs1);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        ys = first0;
        zs = first1;
        tmp22 = NofibPrelude.Cons(x, ys);
        return [
          tmp22,
          zs
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
isSpace = function isSpace(c) {
  return c === " "
};
words = function words(s) {
  let scrut, param0, param1, h, t, scrut1, first1, first0, w, s_, tmp21, tmp22;
  scrut = NofibPrelude.dropWhile(isSpace, s);
  if (scrut instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (scrut instanceof NofibPrelude.Cons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    h = param0;
    t = param1;
    tmp21 = NofibPrelude.Cons(h, t);
    scrut1 = NofibPrelude.break_(isSpace, tmp21);
    if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
      first0 = scrut1[0];
      first1 = scrut1[1];
      w = first0;
      s_ = first1;
      tmp22 = words(s_);
      return NofibPrelude.Cons(w, tmp22)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lines = function lines(s) {
  let scrut, first1, first0, l, s_, param0, param1, s__, tmp21, lambda1;
  lambda1 = (undefined, function (x) {
    return x === "\n"
  });
  scrut = NofibPrelude.break_(lambda1, s);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    l = first0;
    s_ = first1;
    if (s_ instanceof NofibPrelude.Nil.class) {
      tmp21 = NofibPrelude.Nil;
    } else if (s_ instanceof NofibPrelude.Cons.class) {
      param0 = s_.head;
      param1 = s_.tail;
      s__ = param1;
      tmp21 = lines(s__);
    } else {
      throw new globalThis.Error("match error");
    }
    return NofibPrelude.Cons(l, tmp21)
  } else {
    throw new globalThis.Error("match error");
  }
};
unlines = function unlines(ls) {
  let tmp21, lambda1;
  lambda1 = (undefined, function (l) {
    let tmp22;
    tmp22 = NofibPrelude.nofibStringToList("\n");
    return NofibPrelude.append(l, tmp22)
  });
  tmp21 = NofibPrelude.map(lambda1, ls);
  return NofibPrelude.concat(tmp21)
};
all = function all(p, xs) {
  let param0, param1, x, xs1, tmp21, tmp22;
  if (xs instanceof NofibPrelude.Nil.class) {
    return true
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs1 = param1;
    tmp21 = runtime.safeCall(p(x));
    tmp22 = NofibPrelude.all(p, xs1);
    return tmp21 && tmp22
  } else {
    throw new globalThis.Error("match error");
  }
};
fold1 = function fold1(f, g, xs) {
  let param0, param1, a, x, a1, tmp21;
  if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    a1 = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return runtime.safeCall(g(a1))
    } else {
      a = param0;
      x = param1;
      tmp21 = fold1(f, g, x);
      return runtime.safeCall(f(a, tmp21))
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
scan1 = function scan1(f, g, xs) {
  let tmp21, lambda1, lambda2;
  lambda1 = (undefined, function (a, s) {
    let tmp22, tmp23;
    tmp22 = NofibPrelude.head(s);
    tmp23 = runtime.safeCall(f(a, tmp22));
    return NofibPrelude.Cons(tmp23, s)
  });
  tmp21 = lambda1;
  lambda2 = (undefined, function (a) {
    let tmp22;
    tmp22 = runtime.safeCall(g(a));
    return NofibPrelude.Cons(tmp22, NofibPrelude.Nil)
  });
  return fold1(tmp21, lambda2, xs)
};
tails = function tails(xs) {
  let lambda1, lambda2;
  lambda1 = (undefined, function (a, s) {
    return NofibPrelude.Cons(a, s)
  });
  lambda2 = (undefined, function (a) {
    return NofibPrelude.Cons(a, NofibPrelude.Nil)
  });
  return scan1(lambda1, lambda2, xs)
};
single = function single(xs) {
  let param0, param1, a;
  if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    a = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return true
    } else {
      return false
    }
  } else {
    return false
  }
};
minWith = function minWith(f, xs) {
  let tmp21, lambda1, lambda2;
  lambda1 = (undefined, function (a, b) {
    let scrut, tmp22, tmp23;
    tmp22 = runtime.safeCall(f(a));
    tmp23 = runtime.safeCall(f(b));
    scrut = tmp22 < tmp23;
    if (scrut === true) {
      return a
    } else {
      return b
    }
  });
  tmp21 = lambda1;
  lambda2 = (undefined, function (x) {
    return x
  });
  return fold1(tmp21, lambda2, xs)
};
new_ = function new_(w, ls) {
  let tmp21;
  tmp21 = NofibPrelude.Cons(w, NofibPrelude.Nil);
  return NofibPrelude.Cons(tmp21, ls)
};
glue = function glue(w, ls) {
  let param0, param1, l, ls_, tmp21;
  if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    l = param0;
    ls_ = param1;
    tmp21 = NofibPrelude.Cons(w, l);
    return NofibPrelude.Cons(tmp21, ls_)
  } else {
    throw new globalThis.Error("match error");
  }
};
formats = function formats(txt) {
  let tmp21, tmp22, lambda1, lambda2;
  lambda1 = (undefined, function (w, ps) {
    let tmp23, tmp24, lambda3, lambda4;
    lambda3 = (undefined, function (p) {
      return new_(w, p)
    });
    tmp23 = NofibPrelude.map(lambda3, ps);
    lambda4 = (undefined, function (p) {
      return glue(w, p)
    });
    tmp24 = NofibPrelude.map(lambda4, ps);
    return NofibPrelude.append(tmp23, tmp24)
  });
  tmp21 = lambda1;
  lambda2 = (undefined, function (x) {
    let tmp23, tmp24;
    tmp23 = NofibPrelude.Cons(x, NofibPrelude.Nil);
    tmp24 = NofibPrelude.Cons(tmp23, NofibPrelude.Nil);
    return NofibPrelude.Cons(tmp24, NofibPrelude.Nil)
  });
  tmp22 = lambda2;
  return fold1(tmp21, tmp22, txt)
};
width = function width(ls) {
  let plus;
  plus = function plus(w, n) {
    let tmp21, tmp22;
    tmp21 = NofibPrelude.listLen(w);
    tmp22 = tmp21 + 1;
    return tmp22 + n
  };
  return fold1(plus, NofibPrelude.listLen, ls)
};
fits = function fits(xs) {
  let tmp21;
  tmp21 = width(xs);
  return tmp21 <= maxw
};
feasible = function feasible(a) {
  return NofibPrelude.all(fits, a)
};
cost = function cost(ls) {
  let linc, plus, lambda1;
  linc = function linc(l) {
    let a, tmp21, tmp22;
    tmp21 = width(l);
    tmp22 = optw - tmp21;
    a = tmp22;
    return a * a
  };
  plus = function plus(l, n) {
    let tmp21;
    tmp21 = linc(l);
    return tmp21 + n
  };
  lambda1 = (undefined, function (x) {
    return 0
  });
  return fold1(plus, lambda1, ls)
};
par0 = function par0(x) {
  let tmp21, tmp22;
  tmp21 = formats(x);
  tmp22 = NofibPrelude.filter(feasible, tmp21);
  return minWith(cost, tmp22)
};
fitH = function fitH(ls) {
  let tmp21;
  tmp21 = NofibPrelude.head(ls);
  return fits(tmp21)
};
fst3 = function fst3(a_b_c) {
  let first2, first1, first0, a, b, c;
  if (globalThis.Array.isArray(a_b_c) && a_b_c.length === 3) {
    first0 = a_b_c[0];
    first1 = a_b_c[1];
    first2 = a_b_c[2];
    a = first0;
    b = first1;
    c = first2;
    return a
  } else {
    throw new globalThis.Error("match error");
  }
};
snd3 = function snd3(a_b_c) {
  let first2, first1, first0, a, b, c;
  if (globalThis.Array.isArray(a_b_c) && a_b_c.length === 3) {
    first0 = a_b_c[0];
    first1 = a_b_c[1];
    first2 = a_b_c[2];
    a = first0;
    b = first1;
    c = first2;
    return b
  } else {
    throw new globalThis.Error("match error");
  }
};
thd3 = function thd3(a_b_c) {
  let first2, first1, first0, a, b, c;
  if (globalThis.Array.isArray(a_b_c) && a_b_c.length === 3) {
    first0 = a_b_c[0];
    first1 = a_b_c[1];
    first2 = a_b_c[2];
    a = first0;
    b = first1;
    c = first2;
    return c
  } else {
    throw new globalThis.Error("match error");
  }
};
width_tl = function width_tl(a_b_c) {
  return fst3(a_b_c)
};
cost_tl = function cost_tl(a_b_c) {
  return snd3(a_b_c)
};
len_tl = function len_tl(a_b_c) {
  return thd3(a_b_c)
};
tile = function tile(ws, a_b) {
  let first1, first0, param0, param1, m, ms, n, l, scrut, first11, first01, ws1, ws2, n1, tmp21, tmp22, tmp23, tmp24;
  if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
    first0 = a_b[0];
    first1 = a_b[1];
    if (first0 instanceof NofibPrelude.Nil.class) {
      n1 = first1;
      return NofibPrelude.Nil
    } else if (first0 instanceof NofibPrelude.Cons.class) {
      param0 = first0.head;
      param1 = first0.tail;
      m = param0;
      ms = param1;
      n = first1;
      tmp21 = n - m;
      l = tmp21;
      scrut = NofibPrelude.splitAt(l, ws);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first01 = scrut[0];
        first11 = scrut[1];
        ws1 = first01;
        ws2 = first11;
        tmp22 = NofibPrelude.Cons(m, ms);
        tmp23 = NofibPrelude.drop(l, tmp22);
        tmp24 = tile(ws2, [
          tmp23,
          m
        ]);
        return NofibPrelude.Cons(ws1, tmp24)
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
null__ = function null__(a_b) {
  let first1, first0;
  if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
    first0 = a_b[0];
    first1 = a_b[1];
    if (first0 instanceof NofibPrelude.Nil.class) {
      if (first1 instanceof NofibPrelude.Nil.class) {
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
};
single_ = function single_(a_b) {
  let first1, first0, x, y, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26;
  if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
    first0 = a_b[0];
    first1 = a_b[1];
    x = first0;
    y = first1;
    tmp21 = NofibPrelude.null_(x);
    tmp22 = single(y);
    tmp23 = tmp21 && tmp22;
    tmp24 = single(x);
    tmp25 = NofibPrelude.null_(y);
    tmp26 = tmp24 && tmp25;
    return tmp23 || tmp26
  } else {
    throw new globalThis.Error("match error");
  }
};
head_ = function head_(a_b) {
  let first1, first0, x, y, scrut, tmp21;
  if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
    first0 = a_b[0];
    first1 = a_b[1];
    x = first0;
    y = first1;
    tmp21 = NofibPrelude.null_(x);
    scrut = BenchmarkPrelude.not(tmp21);
    if (scrut === true) {
      return NofibPrelude.head(x)
    } else {
      return NofibPrelude.head(y)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
last_ = function last_(a_b) {
  let first1, first0, y, x, scrut, tmp21;
  if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
    first0 = a_b[0];
    first1 = a_b[1];
    y = first0;
    x = first1;
    tmp21 = NofibPrelude.null_(x);
    scrut = BenchmarkPrelude.not(tmp21);
    if (scrut === true) {
      return NofibPrelude.head(x)
    } else {
      return NofibPrelude.head(y)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
cons_ = function cons_(a, a_b) {
  let first1, first0, x, y, scrut, tmp21, tmp22, tmp23;
  if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
    first0 = a_b[0];
    first1 = a_b[1];
    x = first0;
    y = first1;
    tmp21 = NofibPrelude.null_(y);
    scrut = BenchmarkPrelude.not(tmp21);
    if (scrut === true) {
      tmp22 = NofibPrelude.Cons(a, x);
      return [
        tmp22,
        y
      ]
    } else {
      tmp23 = NofibPrelude.Cons(a, NofibPrelude.Nil);
      return [
        tmp23,
        x
      ]
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
snoc_ = function snoc_(a, a_b) {
  let first1, first0, y, x, scrut, tmp21, tmp22, tmp23;
  if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
    first0 = a_b[0];
    first1 = a_b[1];
    y = first0;
    x = first1;
    tmp21 = NofibPrelude.null_(y);
    scrut = BenchmarkPrelude.not(tmp21);
    if (scrut === true) {
      tmp22 = NofibPrelude.Cons(a, x);
      return [
        y,
        tmp22
      ]
    } else {
      tmp23 = NofibPrelude.Cons(a, NofibPrelude.Nil);
      return [
        x,
        tmp23
      ]
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
tail_ = function tail_(a_b) {
  let first1, first0, x, y, scrut, scrut1, first11, first01, y0, y1, scrut2, tmp21, tmp22, tmp23, tmp24, tmp25;
  if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
    first0 = a_b[0];
    first1 = a_b[1];
    x = first0;
    y = first1;
    scrut2 = NofibPrelude.null_(x);
    if (scrut2 === true) {
      return [
        NofibPrelude.Nil,
        NofibPrelude.Nil
      ]
    } else {
      scrut = single(x);
      if (scrut === true) {
        tmp21 = NofibPrelude.listLen(y);
        tmp22 = NofibPrelude.intDiv(tmp21, 2);
        scrut1 = NofibPrelude.splitAt(tmp22, y);
        if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
          first01 = scrut1[0];
          first11 = scrut1[1];
          y0 = first01;
          y1 = first11;
          tmp23 = NofibPrelude.reverse(y1);
          return [
            tmp23,
            y0
          ]
        } else {
          tmp24 = NofibPrelude.tail(x);
          return [
            tmp24,
            y
          ]
        }
      } else {
        tmp25 = NofibPrelude.tail(x);
        return [
          tmp25,
          y
        ]
      }
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
init_ = function init_(a_b) {
  let first1, first0, y, x, scrut, scrut1, first11, first01, y0, y1, scrut2, tmp21, tmp22, tmp23, tmp24, tmp25;
  if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
    first0 = a_b[0];
    first1 = a_b[1];
    y = first0;
    x = first1;
    scrut2 = NofibPrelude.null_(x);
    if (scrut2 === true) {
      return [
        NofibPrelude.Nil,
        NofibPrelude.Nil
      ]
    } else {
      scrut = single(x);
      if (scrut === true) {
        tmp21 = NofibPrelude.listLen(y);
        tmp22 = NofibPrelude.intDiv(tmp21, 2);
        scrut1 = NofibPrelude.splitAt(tmp22, y);
        if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
          first01 = scrut1[0];
          first11 = scrut1[1];
          y0 = first01;
          y1 = first11;
          tmp23 = NofibPrelude.reverse(y1);
          return [
            y0,
            tmp23
          ]
        } else {
          tmp24 = NofibPrelude.tail(x);
          return [
            y,
            tmp24
          ]
        }
      } else {
        tmp25 = NofibPrelude.tail(x);
        return [
          y,
          tmp25
        ]
      }
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
unformat = function unformat(a, l) {
  let tmp21, lambda1, lambda2;
  lambda1 = (undefined, function (xs, ys) {
    let tmp22, tmp23;
    tmp22 = NofibPrelude.Cons(a, NofibPrelude.Nil);
    tmp23 = NofibPrelude.append(tmp22, ys);
    return NofibPrelude.append(xs, tmp23)
  });
  tmp21 = lambda1;
  lambda2 = (undefined, function (x) {
    return x
  });
  return fold1(tmp21, lambda2, l)
};
format = function format(a, x) {
  let start, breakk, unknownEq, lambda1, lambda2;
  if (x instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil)
  } else {
    unknownEq = function unknownEq(a1, b) {
      return a1 === b
    };
    breakk = function breakk(a1, b, xs) {
      let scrut, tmp21, tmp22, tmp23;
      scrut = unknownEq(a1, b);
      if (scrut === true) {
        return NofibPrelude.Cons(NofibPrelude.Nil, xs)
      } else {
        tmp21 = NofibPrelude.head(xs);
        tmp22 = NofibPrelude.Cons(b, tmp21);
        tmp23 = NofibPrelude.tail(xs);
        return NofibPrelude.Cons(tmp22, tmp23)
      }
    };
    start = function start(a1, b) {
      let tmp21;
      tmp21 = NofibPrelude.Cons(NofibPrelude.Nil, NofibPrelude.Nil);
      return breakk(a1, b, tmp21)
    };
    lambda1 = (undefined, function (x1, y) {
      return breakk(a, x1, y)
    });
    lambda2 = (undefined, function (y) {
      return start(a, y)
    });
    return fold1(lambda1, lambda2, x)
  }
};
unparas = function unparas(ls) {
  return unformat(NofibPrelude.Nil, ls)
};
paras = function paras(ls) {
  let tmp21, lambda1;
  tmp21 = format(NofibPrelude.Nil, ls);
  lambda1 = (undefined, function (x) {
    return NofibPrelude.listNeq(NofibPrelude.Nil, x)
  });
  return NofibPrelude.filter(lambda1, tmp21)
};
parse = function parse(ls) {
  let tmp21, tmp22;
  tmp21 = lines(ls);
  tmp22 = NofibPrelude.map(words, tmp21);
  return paras(tmp22)
};
unparse = function unparse(ls) {
  let tmp21, tmp22;
  tmp21 = unparas(ls);
  tmp22 = NofibPrelude.map(unwords, tmp21);
  return unlines(tmp22)
};
startr = function startr(a) {
  let scrut, tmp21;
  scrut = a <= maxw;
  if (scrut === true) {
    tmp21 = cons_([
      0,
      0,
      0
    ], nil_);
    return [
      tmp21,
      a,
      1
    ]
  } else {
    throw globalThis.Error("startr param error");
  }
};
ceildiv = function ceildiv(n, m) {
  let tmp21, tmp22;
  tmp21 = n + m;
  tmp22 = tmp21 - 1;
  return NofibPrelude.intDiv(tmp22, m)
};
fmtWith = function fmtWith(par) {
  let tmp21, tmp22, lambda1;
  tmp21 = parse(par);
  lambda1 = (undefined, function (x) {
    let tmp23;
    tmp23 = NofibPrelude.concat(x);
    return runtime.safeCall(par(tmp23))
  });
  tmp22 = NofibPrelude.map(lambda1, tmp21);
  return unparse(tmp22)
};
stepr = function stepr(w, ps_tw_tl) {
  let bf, old_width_hd, width_hd, myAdd, single1, trim, new_1, cost1, drop_nofit, first2, first1, first0, ps, tw, tl, tot_width, tot_len, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28;
  if (globalThis.Array.isArray(ps_tw_tl) && ps_tw_tl.length === 3) {
    first0 = ps_tw_tl[0];
    first1 = ps_tw_tl[1];
    first2 = ps_tw_tl[2];
    ps = first0;
    tw = first1;
    tl = first2;
    single1 = function single(p) {
      let tmp29;
      tmp29 = len_tl(p);
      return tmp29 === 0
    };
    width_hd = function width_hd(p) {
      let scrut, tmp29, tmp30;
      scrut = single1(p);
      if (scrut === true) {
        return tot_width
      } else {
        tmp29 = width_tl(p);
        tmp30 = tot_width - tmp29;
        return tmp30 - 1
      }
    };
    cost1 = function cost(p) {
      let a, scrut, tmp29, tmp30, tmp31, tmp32;
      scrut = single1(p);
      if (scrut === true) {
        return 0
      } else {
        tmp29 = cost_tl(p);
        tmp30 = width_hd(p);
        tmp31 = optw - tmp30;
        a = tmp31;
        tmp32 = a * a;
        return tmp29 + tmp32
      }
    };
    old_width_hd = function old_width_hd(p) {
      let scrut, tmp29, tmp30;
      scrut = single1(p);
      if (scrut === true) {
        return tw
      } else {
        tmp29 = width_tl(p);
        tmp30 = tw - tmp29;
        return tmp30 - 1
      }
    };
    new_1 = function new_(p) {
      let x, scrut, tmp29, tmp30, tmp31, tmp32, tmp33;
      scrut = single1(p);
      if (scrut === true) {
        return [
          tw,
          0,
          tl
        ]
      } else {
        tmp29 = cost_tl(p);
        tmp30 = old_width_hd(p);
        tmp31 = optw - tmp30;
        x = tmp31;
        tmp32 = x * x;
        tmp33 = tmp29 + tmp32;
        return [
          tw,
          tmp33,
          tl
        ]
      }
    };
    trim = function trim(ps_pq) {
      let ps_p, q, p, scrut, scrut1, scrut2, tmp29, tmp30;
      scrut2 = null__(ps_pq);
      if (scrut2 === true) {
        return ps_pq
      } else {
        scrut1 = single_(ps_pq);
        if (scrut1 === true) {
          return ps_pq
        } else {
          ps_p = init_(ps_pq);
          q = last_(ps_pq);
          p = last_(ps_p);
          tmp29 = cost1(p);
          tmp30 = cost1(q);
          scrut = tmp29 <= tmp30;
          if (scrut === true) {
            return trim(ps_p)
          } else {
            return ps_pq
          }
        }
      }
    };
    drop_nofit = function drop_nofit(ps_p) {
      let scrut, scrut1, tmp29, tmp30, tmp31;
      scrut1 = null__(ps_p);
      if (scrut1 === true) {
        return ps_p
      } else {
        tmp29 = last_(ps_p);
        tmp30 = width_hd(tmp29);
        scrut = tmp30 > maxw;
        if (scrut === true) {
          tmp31 = init_(ps_p);
          return drop_nofit(tmp31)
        } else {
          return ps_p
        }
      }
    };
    bf = function bf(p, q) {
      let wqh, rqh, scrut, scrut1, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43;
      tmp29 = width_hd(q);
      wqh = tmp29;
      tmp30 = maxw - wqh;
      tmp31 = tmp30 + 1;
      rqh = tmp31;
      tmp32 = single1(q);
      tmp33 = cost_tl(p);
      tmp34 = tmp33 === 0;
      scrut1 = tmp32 && tmp34;
      if (scrut1 === true) {
        tmp35 = width_hd(p);
        tmp36 = optw - tmp35;
        return NofibPrelude.min(tmp36, rqh)
      } else {
        scrut = single1(q);
        if (scrut === true) {
          return rqh
        } else {
          tmp37 = cost1(p);
          tmp38 = cost1(q);
          tmp39 = tmp37 - tmp38;
          tmp40 = width_hd(p);
          tmp41 = wqh - tmp40;
          tmp42 = 2 * tmp41;
          tmp43 = ceildiv(tmp39, tmp42);
          return NofibPrelude.min(tmp43, rqh)
        }
      }
    };
    myAdd = function myAdd(p, qr_rs) {
      let q, r_rs, r, scrut, scrut1, tmp29, tmp30, tmp31, tmp32;
      tmp29 = single_(qr_rs);
      tmp30 = null__(qr_rs);
      scrut1 = tmp29 || tmp30;
      if (scrut1 === true) {
        return cons_(p, qr_rs)
      } else {
        q = head_(qr_rs);
        r_rs = tail_(qr_rs);
        r = head_(r_rs);
        tmp31 = bf(p, q);
        tmp32 = bf(q, r);
        scrut = tmp31 <= tmp32;
        if (scrut === true) {
          return myAdd(p, r_rs)
        } else {
          return cons_(p, qr_rs)
        }
      }
    };
    tmp21 = w + 1;
    tmp22 = tmp21 + tw;
    tot_width = tmp22;
    tmp23 = 1 + tl;
    tot_len = tmp23;
    tmp24 = last_(ps);
    tmp25 = new_1(tmp24);
    tmp26 = myAdd(tmp25, ps);
    tmp27 = drop_nofit(tmp26);
    tmp28 = trim(tmp27);
    return [
      tmp28,
      tot_width,
      tot_len
    ]
  } else {
    throw new globalThis.Error("match error");
  }
};
par3 = function par3(ws) {
  let zs, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, lambda1;
  tmp21 = NofibPrelude.map(NofibPrelude.listLen, ws);
  tmp22 = scan1(stepr, startr, tmp21);
  zs = tmp22;
  lambda1 = (undefined, function (x) {
    let tmp27, tmp28;
    tmp27 = fst3(x);
    tmp28 = last_(tmp27);
    return len_tl(tmp28)
  });
  tmp23 = lambda1;
  tmp24 = NofibPrelude.map(tmp23, zs);
  tmp25 = NofibPrelude.head(zs);
  tmp26 = thd3(tmp25);
  return tile(ws, [
    tmp24,
    tmp26
  ])
};
fmt = function fmt(x) {
  let tmp21, tmp22, tmp23;
  tmp21 = parse(x);
  tmp22 = NofibPrelude.concat(tmp21);
  tmp23 = NofibPrelude.map(par3, tmp22);
  return unparse(tmp23)
};
testPara_nofib = function testPara_nofib() {
  let scrut;
  scrut = NofibPrelude.null_(test);
  if (scrut === true) {
    return NofibPrelude.Nil
  } else {
    return fmt(test)
  }
};
maxw = 70;
optw = 63;
nil_ = [
  NofibPrelude.Nil,
  NofibPrelude.Nil
];
tmp = NofibPrelude.nofibStringToList("In the constructive programming community it is commonplace to see ");
tmp1 = NofibPrelude.nofibStringToList("formal developments of textbook algorithms. In the algorithm design ");
tmp2 = NofibPrelude.nofibStringToList("community, on the other hand, it may be well known that the textbook ");
tmp3 = NofibPrelude.nofibStringToList("solution to a problem is not the most efficient possible. However, in ");
tmp4 = NofibPrelude.nofibStringToList("presenting the more efficient solution, the algorithm designer will ");
tmp5 = NofibPrelude.nofibStringToList("usually omit some of the implementation details, this creating an ");
tmp6 = NofibPrelude.nofibStringToList("algorithm gap between the abstract algorithm and its concrete ");
tmp7 = NofibPrelude.nofibStringToList("implementation. This is in contrast to the formal development, which ");
tmp8 = NofibPrelude.nofibStringToList("usually presents the complete concrete implementation of the less ");
tmp9 = NofibPrelude.nofibStringToList("efficient solution.\n\n");
tmp10 = NofibPrelude.Cons(tmp9, NofibPrelude.Nil);
tmp11 = NofibPrelude.Cons(tmp8, tmp10);
tmp12 = NofibPrelude.Cons(tmp7, tmp11);
tmp13 = NofibPrelude.Cons(tmp6, tmp12);
tmp14 = NofibPrelude.Cons(tmp5, tmp13);
tmp15 = NofibPrelude.Cons(tmp4, tmp14);
tmp16 = NofibPrelude.Cons(tmp3, tmp15);
tmp17 = NofibPrelude.Cons(tmp2, tmp16);
tmp18 = NofibPrelude.Cons(tmp1, tmp17);
tmp19 = NofibPrelude.Cons(tmp, tmp18);
tmp20 = NofibPrelude.concat(tmp19);
test = tmp20;
lambda = (undefined, function () {
  let tmp21;
  tmp21 = testPara_nofib();
  return NofibPrelude.nofibListToString(tmp21)
});
BenchmarkPrelude.benchmark(lambda)