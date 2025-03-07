import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let tab, rqpart, showColour, showMovesAfter, tryMove, comment, sift, pieceToChar, rawmoves, maybe, showSquare, Knight1, any, MoveInFull1, parseSquare, Solution1, qpart, pieceAt, onboard, King1, isLower, qsort, parseGoal, Board1, solve, isUpper, kindToChar, readProblem, kingSquare, unlines, emptyAtAll, pawnmoves, White1, Bishop1, toLower, Colour1, Black1, rPa, last, putPieceAt, kSq, insertCompact, foldr_lz, showMoveInFull, solution, kindOf, testMate_nofib, rmPieceAt, showSoln, showMoves, Move1, showPiece, Queen1, parseRank, intOfString, kingmoves, showResult, kingincheck, moveDetailsFor, Rook1, moveLine, words, rqsort, opponent, showMove, parseProblem, Soln1, Pawn1, queenmoves, Kind1, replies, knightmoves, sort, lines, showBoard, colourOf, forcesColoured, rookmoves, parseBoard, compact, showReplies, bishopmoves, emptyBoard, tmp, tmp1, lambda;
rqpart = function rqpart(le, x, ys, rle, rgt, r) {
  let param0, param1, y, ys1, scrut, tmp2, tmp3, tmp4, tmp5;
  if (ys instanceof NofibPrelude.Nil.class) {
    tmp2 = qsort(le, rgt, r);
    tmp3 = NofibPrelude.Cons(x, tmp2);
    return qsort(le, rle, tmp3)
  } else if (ys instanceof NofibPrelude.Cons.class) {
    param0 = ys.head;
    param1 = ys.tail;
    y = param0;
    ys1 = param1;
    scrut = runtime.safeCall(le(y, x));
    if (scrut === true) {
      tmp4 = NofibPrelude.Cons(y, rle);
      return rqpart(le, x, ys1, tmp4, rgt, r)
    } else {
      tmp5 = NofibPrelude.Cons(y, rgt);
      return rqpart(le, x, ys1, rle, tmp5, r)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
rqsort = function rqsort(le, xs, r) {
  let param0, param1, x, xs1, x1;
  if (xs instanceof NofibPrelude.Nil.class) {
    return r
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x1 = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(x1, r)
    } else {
      x = param0;
      xs1 = param1;
      return rqpart(le, x, xs1, NofibPrelude.Nil, NofibPrelude.Nil, r)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
qpart = function qpart(le, x, ys, rlt, rge, r) {
  let param0, param1, y, ys1, scrut, tmp2, tmp3, tmp4, tmp5;
  if (ys instanceof NofibPrelude.Nil.class) {
    tmp2 = rqsort(le, rge, r);
    tmp3 = NofibPrelude.Cons(x, tmp2);
    return rqsort(le, rlt, tmp3)
  } else if (ys instanceof NofibPrelude.Cons.class) {
    param0 = ys.head;
    param1 = ys.tail;
    y = param0;
    ys1 = param1;
    scrut = runtime.safeCall(le(x, y));
    if (scrut === true) {
      tmp4 = NofibPrelude.Cons(y, rge);
      return qpart(le, x, ys1, rlt, tmp4, r)
    } else {
      tmp5 = NofibPrelude.Cons(y, rlt);
      return qpart(le, x, ys1, tmp5, rge, r)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
qsort = function qsort(le, xs, r) {
  let param0, param1, x, xs1, x1;
  if (xs instanceof NofibPrelude.Nil.class) {
    return r
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x1 = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(x1, r)
    } else {
      x = param0;
      xs1 = param1;
      return qpart(le, x, xs1, NofibPrelude.Nil, NofibPrelude.Nil, r)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
sort = function sort(l) {
  let tmp2, lambda1;
  lambda1 = (undefined, function (a, b) {
    let first1, first0, aa, first11, first01, bb, tmp3, tmp4;
    if (globalThis.Array.isArray(a) && a.length === 2) {
      first0 = a[0];
      first1 = a[1];
      aa = first0;
      if (globalThis.Array.isArray(b) && b.length === 2) {
        first01 = b[0];
        first11 = b[1];
        bb = first01;
        tmp3 = NofibPrelude.listLen(aa);
        tmp4 = NofibPrelude.listLen(bb);
        return tmp3 <= tmp4
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp2 = lambda1;
  return qsort(tmp2, l, NofibPrelude.Nil)
};
maybe = function maybe(d, f, x) {
  let param0, x1;
  if (x instanceof NofibPrelude.None.class) {
    return d
  } else if (x instanceof NofibPrelude.Some.class) {
    param0 = x.x;
    x1 = param0;
    return runtime.safeCall(f(x1))
  } else {
    throw new globalThis.Error("match error");
  }
};
isUpper = function isUpper(c) {
  let x, scrut, scrut1, tmp2;
  tmp2 = runtime.safeCall(c.charCodeAt(0));
  x = tmp2;
  scrut = x >= 65;
  if (scrut === true) {
    scrut1 = x <= 90;
    if (scrut1 === true) {
      return true
    } else {
      return false
    }
  } else {
    return false
  }
};
isLower = function isLower(c) {
  let x, scrut, scrut1, tmp2;
  tmp2 = runtime.safeCall(c.charCodeAt(0));
  x = tmp2;
  scrut = x >= 97;
  if (scrut === true) {
    scrut1 = x <= 122;
    if (scrut1 === true) {
      return true
    } else {
      return false
    }
  } else {
    return false
  }
};
toLower = function toLower(c) {
  let scrut, tmp2, tmp3;
  scrut = isUpper(c);
  if (scrut === true) {
    tmp2 = runtime.safeCall(c.charCodeAt(0));
    tmp3 = tmp2 + 32;
    return runtime.safeCall(globalThis.String.fromCharCode(tmp3))
  } else {
    return c
  }
};
words = function words(s) {
  let scrut, s_, scrut1, first1, first0, w, s__, tmp2, lambda1, lambda2;
  lambda1 = (undefined, function (x) {
    return x === " "
  });
  scrut = NofibPrelude.dropWhile(lambda1, s);
  if (scrut instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else {
    s_ = scrut;
    lambda2 = (undefined, function (x) {
      return x === " "
    });
    scrut1 = NofibPrelude.break_(lambda2, s_);
    if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
      first0 = scrut1[0];
      first1 = scrut1[1];
      w = first0;
      s__ = first1;
      tmp2 = words(s__);
      return NofibPrelude.Cons(w, tmp2)
    } else {
      throw new globalThis.Error("match error");
    }
  }
};
unlines = function unlines(ls) {
  let tmp2, lambda1;
  lambda1 = (undefined, function (l) {
    let tmp3;
    tmp3 = NofibPrelude.Cons("\n", NofibPrelude.Nil);
    return NofibPrelude.append(l, tmp3)
  });
  tmp2 = NofibPrelude.map(lambda1, ls);
  return NofibPrelude.concat(tmp2)
};
lines = function lines(s) {
  let scrut, first1, first0, l, s_, param0, param1, s__, tmp2, lambda1;
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
      tmp2 = NofibPrelude.Nil;
    } else if (s_ instanceof NofibPrelude.Cons.class) {
      param0 = s_.head;
      param1 = s_.tail;
      s__ = param1;
      tmp2 = lines(s__);
    } else {
      throw new globalThis.Error("match error");
    }
    return NofibPrelude.Cons(l, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
any = function any(p, ls) {
  let param0, param1, x, xs, tmp2, tmp3;
  if (ls instanceof NofibPrelude.Nil.class) {
    return false
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    x = param0;
    xs = param1;
    tmp2 = runtime.safeCall(p(x));
    tmp3 = any(p, xs);
    return tmp2 || tmp3
  } else {
    throw new globalThis.Error("match error");
  }
};
showColour = function showColour(c) {
  let tmp2;
  if (c instanceof Black1.class) {
    tmp2 = "Black";
  } else {
    tmp2 = "White";
  }
  return NofibPrelude.nofibStringToList(tmp2)
};
pieceAt = function pieceAt(bd, sq) {
  let pieceAtWith, param0, param1, wkss, bkss, tmp2;
  if (bd instanceof Board1.class) {
    param0 = bd.a;
    param1 = bd.b;
    wkss = param0;
    bkss = param1;
    pieceAtWith = function pieceAtWith(c, n, ls) {
      let param01, param11, first1, first0, k, s, xs, scrut;
      if (ls instanceof NofibPrelude.Nil.class) {
        return n
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param01 = ls.head;
        param11 = ls.tail;
        if (globalThis.Array.isArray(param01) && param01.length === 2) {
          first0 = param01[0];
          first1 = param01[1];
          k = first0;
          s = first1;
          xs = param11;
          scrut = NofibPrelude.eqTup2(s, sq);
          if (scrut === true) {
            return NofibPrelude.Some([
              c,
              k
            ])
          } else {
            return pieceAtWith(c, n, xs)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp2 = pieceAtWith(Black1, NofibPrelude.None, bkss);
    return pieceAtWith(White1, tmp2, wkss)
  } else {
    throw new globalThis.Error("match error");
  }
};
kindToChar = function kindToChar(k) {
  if (k instanceof King1.class) {
    return "K"
  } else if (k instanceof Queen1.class) {
    return "Q"
  } else if (k instanceof Rook1.class) {
    return "R"
  } else if (k instanceof Bishop1.class) {
    return "B"
  } else if (k instanceof Knight1.class) {
    return "N"
  } else if (k instanceof Pawn1.class) {
    return "P"
  } else {
    throw new globalThis.Error("match error");
  }
};
pieceToChar = function pieceToChar(p) {
  let first1, first0, k, k1, tmp2;
  if (globalThis.Array.isArray(p) && p.length === 2) {
    first0 = p[0];
    first1 = p[1];
    if (first0 instanceof Black1.class) {
      k1 = first1;
      return kindToChar(k1)
    } else if (first0 instanceof White1.class) {
      k = first1;
      tmp2 = kindToChar(k);
      return toLower(tmp2)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
showBoard = function showBoard(bd) {
  let showRank, tmp2, tmp3, tmp4;
  showRank = function showRank(r) {
    let consFile, tmp5;
    consFile = function consFile(f, s) {
      let scrut, param0, p, tmp6, tmp7, tmp8;
      scrut = pieceAt(bd, [
        f,
        r
      ]);
      if (scrut instanceof NofibPrelude.None.class) {
        tmp6 = NofibPrelude.nofibStringToList(" -");
        return NofibPrelude.append(tmp6, s)
      } else if (scrut instanceof NofibPrelude.Some.class) {
        param0 = scrut.x;
        p = param0;
        tmp7 = pieceToChar(p);
        tmp8 = NofibPrelude.Cons(tmp7, s);
        return NofibPrelude.Cons(" ", tmp8)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp5 = NofibPrelude.enumFromTo(1, 8);
    return NofibPrelude.foldr(consFile, NofibPrelude.Nil, tmp5)
  };
  tmp2 = NofibPrelude.enumFromTo(1, 8);
  tmp3 = NofibPrelude.reverse(tmp2);
  tmp4 = NofibPrelude.map(showRank, tmp3);
  return unlines(tmp4)
};
showPiece = function showPiece(p) {
  let first1, first0, c, k, tmp2;
  if (globalThis.Array.isArray(p) && p.length === 2) {
    first0 = p[0];
    first1 = p[1];
    c = first0;
    k = first1;
    tmp2 = kindToChar(k);
    return NofibPrelude.Cons(tmp2, NofibPrelude.Nil)
  } else {
    throw new globalThis.Error("match error");
  }
};
showSquare = function showSquare(c, x_y) {
  let first1, first0, x, y, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22;
  if (globalThis.Array.isArray(x_y) && x_y.length === 2) {
    first0 = x_y[0];
    first1 = x_y[1];
    x = first0;
    y = first1;
    tmp2 = x - 1;
    tmp3 = NofibPrelude.nofibStringToList("QR");
    tmp4 = NofibPrelude.nofibStringToList("QN");
    tmp5 = NofibPrelude.nofibStringToList("QB");
    tmp6 = NofibPrelude.nofibStringToList("Q");
    tmp7 = NofibPrelude.nofibStringToList("K");
    tmp8 = NofibPrelude.nofibStringToList("KB");
    tmp9 = NofibPrelude.nofibStringToList("KN");
    tmp10 = NofibPrelude.nofibStringToList("KR");
    tmp11 = NofibPrelude.Cons(tmp10, NofibPrelude.Nil);
    tmp12 = NofibPrelude.Cons(tmp9, tmp11);
    tmp13 = NofibPrelude.Cons(tmp8, tmp12);
    tmp14 = NofibPrelude.Cons(tmp7, tmp13);
    tmp15 = NofibPrelude.Cons(tmp6, tmp14);
    tmp16 = NofibPrelude.Cons(tmp5, tmp15);
    tmp17 = NofibPrelude.Cons(tmp4, tmp16);
    tmp18 = NofibPrelude.Cons(tmp3, tmp17);
    tmp19 = NofibPrelude.atIndex(tmp2, tmp18);
    if (c instanceof Black1.class) {
      tmp20 = 9 - y;
    } else {
      tmp20 = y;
    }
    tmp21 = NofibPrelude.stringOfInt(tmp20);
    tmp22 = NofibPrelude.nofibStringToList(tmp21);
    return NofibPrelude.append(tmp19, tmp22)
  } else {
    throw new globalThis.Error("match error");
  }
};
emptyAtAll = function emptyAtAll(bd, e) {
  let emptyAtAllAnd, param0, param1, wkss, bkss, tmp2;
  if (bd instanceof Board1.class) {
    param0 = bd.a;
    param1 = bd.b;
    wkss = param0;
    bkss = param1;
    emptyAtAllAnd = function emptyAtAllAnd(b, ls) {
      let param01, param11, first1, first0, s, xs, scrut, scrut1, tmp3;
      if (ls instanceof NofibPrelude.Nil.class) {
        return b
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param01 = ls.head;
        param11 = ls.tail;
        if (globalThis.Array.isArray(param01) && param01.length === 2) {
          first0 = param01[0];
          first1 = param01[1];
          s = first1;
          xs = param11;
          tmp3 = runtime.safeCall(e(s));
          scrut = BenchmarkPrelude.not(tmp3);
          if (scrut === true) {
            scrut1 = emptyAtAllAnd(b, xs);
            if (scrut1 === true) {
              return true
            } else {
              return false
            }
          } else {
            return false
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp2 = emptyAtAllAnd(true, bkss);
    return emptyAtAllAnd(tmp2, wkss)
  } else {
    throw new globalThis.Error("match error");
  }
};
rPa = function rPa(sq, kss) {
  let param0, param1, first1, first0, k, s, kss1, scrut, tmp2;
  if (kss instanceof NofibPrelude.Nil.class) {
    throw globalThis.Error("rPa");
  } else if (kss instanceof NofibPrelude.Cons.class) {
    param0 = kss.head;
    param1 = kss.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      k = first0;
      s = first1;
      kss1 = param1;
      scrut = NofibPrelude.eqTup2(s, sq);
      if (scrut === true) {
        return kss1
      } else {
        tmp2 = rPa(sq, kss1);
        return NofibPrelude.Cons([
          k,
          s
        ], tmp2)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
rmPieceAt = function rmPieceAt(c, sq, bd) {
  let param0, param1, wkss, bkss, tmp2, tmp3;
  if (bd instanceof Board1.class) {
    param0 = bd.a;
    param1 = bd.b;
    wkss = param0;
    bkss = param1;
    if (c instanceof White1.class) {
      tmp2 = rPa(sq, wkss);
      return Board1(tmp2, bkss)
    } else if (c instanceof Black1.class) {
      tmp3 = rPa(sq, bkss);
      return Board1(wkss, tmp3)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
putPieceAt = function putPieceAt(sq, c_k, bd) {
  let first1, first0, c, k, param0, param1, wkss, bkss, tmp2, tmp3;
  if (globalThis.Array.isArray(c_k) && c_k.length === 2) {
    first0 = c_k[0];
    first1 = c_k[1];
    c = first0;
    k = first1;
    if (bd instanceof Board1.class) {
      param0 = bd.a;
      param1 = bd.b;
      wkss = param0;
      bkss = param1;
      if (c instanceof White1.class) {
        tmp2 = NofibPrelude.Cons([
          k,
          sq
        ], wkss);
        return Board1(tmp2, bkss)
      } else if (c instanceof Black1.class) {
        tmp3 = NofibPrelude.Cons([
          k,
          sq
        ], bkss);
        return Board1(wkss, tmp3)
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
kSq = function kSq(kss) {
  let param0, param1, kss1, first1, first0, s;
  if (kss instanceof NofibPrelude.Cons.class) {
    param0 = kss.head;
    param1 = kss.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      if (first0 instanceof King1.class) {
        s = first1;
        return s
      } else {
        kss1 = param1;
        return kSq(kss1)
      }
    } else {
      kss1 = param1;
      return kSq(kss1)
    }
  } else if (kss instanceof NofibPrelude.Nil.class) {
    throw globalThis.Error("kSq");
  } else {
    throw new globalThis.Error("match error");
  }
};
kingSquare = function kingSquare(c, bd) {
  let param0, param1, wkss, bkss;
  if (bd instanceof Board1.class) {
    param0 = bd.a;
    param1 = bd.b;
    wkss = param0;
    bkss = param1;
    if (c instanceof White1.class) {
      return kSq(wkss)
    } else if (c instanceof Black1.class) {
      return kSq(bkss)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
opponent = function opponent(c) {
  if (c instanceof White1.class) {
    return Black1
  } else {
    return White1
  }
};
colourOf = function colourOf(c_k) {
  let first1, first0, c;
  if (globalThis.Array.isArray(c_k) && c_k.length === 2) {
    first0 = c_k[0];
    first1 = c_k[1];
    c = first0;
    return c
  } else {
    throw new globalThis.Error("match error");
  }
};
kindOf = function kindOf(c_k) {
  let first1, first0, k;
  if (globalThis.Array.isArray(c_k) && c_k.length === 2) {
    first0 = c_k[0];
    first1 = c_k[1];
    k = first1;
    return k
  } else {
    throw new globalThis.Error("match error");
  }
};
onboard = function onboard(p_q) {
  let first1, first0, p, q, scrut, scrut1, scrut2, scrut3, scrut4, scrut5, tmp2, tmp3;
  if (globalThis.Array.isArray(p_q) && p_q.length === 2) {
    first0 = p_q[0];
    first1 = p_q[1];
    p = first0;
    q = first1;
    scrut = p >= 1;
    if (scrut === true) {
      scrut1 = p <= 8;
      if (scrut1 === true) {
        tmp2 = true;
      } else {
        tmp2 = false;
      }
    } else {
      tmp2 = false;
    }
    scrut2 = tmp2;
    if (scrut2 === true) {
      scrut3 = q >= 1;
      if (scrut3 === true) {
        scrut4 = q <= 8;
        if (scrut4 === true) {
          tmp3 = true;
        } else {
          tmp3 = false;
        }
      } else {
        tmp3 = false;
      }
      scrut5 = tmp3;
      if (scrut5 === true) {
        return true
      } else {
        return false
      }
    } else {
      return false
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
forcesColoured = function forcesColoured(c, bd) {
  let param0, param1, wkss, bkss;
  if (bd instanceof Board1.class) {
    param0 = bd.a;
    param1 = bd.b;
    wkss = param0;
    bkss = param1;
    if (c instanceof White1.class) {
      return wkss
    } else if (c instanceof Black1.class) {
      return bkss
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
showMove = function showMove(withPiece, m) {
  let param0, param1, param2, first1, first0, c, k, sq, param01, param11, param21, sq_, mcp, mpp, capt, param02, prom, param03, scrut, scrut1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, lambda1, lambda2;
  if (m instanceof MoveInFull1.class) {
    param0 = m.a;
    param1 = m.b;
    param2 = m.c;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      c = first0;
      k = first1;
      sq = param1;
      if (param2 instanceof Move1.class) {
        param01 = param2.a;
        param11 = param2.b;
        param21 = param2.c;
        sq_ = param01;
        mcp = param11;
        mpp = param21;
        if (mcp instanceof NofibPrelude.Some.class) {
          param02 = mcp.x;
          tmp2 = true;
        } else {
          tmp2 = false;
        }
        capt = tmp2;
        if (mpp instanceof NofibPrelude.Some.class) {
          param03 = mpp.x;
          tmp3 = true;
        } else {
          tmp3 = false;
        }
        prom = tmp3;
        if (withPiece === true) {
          tmp4 = showPiece([
            c,
            k
          ]);
          tmp5 = k === King1;
          if (k instanceof Pawn1.class) {
            tmp6 = capt || prom;
            scrut = BenchmarkPrelude.not(tmp6);
            if (scrut === true) {
              tmp7 = true;
            } else {
              tmp7 = false;
            }
          } else {
            tmp7 = false;
          }
          scrut1 = tmp5 || tmp7;
          if (scrut1 === true) {
            tmp8 = NofibPrelude.Nil;
          } else {
            tmp9 = showSquare(c, sq);
            tmp8 = NofibPrelude.Cons("/", tmp9);
          }
          tmp10 = NofibPrelude.append(tmp4, tmp8);
        } else {
          tmp10 = NofibPrelude.Nil;
        }
        tmp11 = NofibPrelude.Cons("-", NofibPrelude.Nil);
        lambda1 = (undefined, function (cp) {
          let tmp19, tmp20, tmp21;
          tmp19 = showPiece(cp);
          tmp20 = NofibPrelude.Cons("/", NofibPrelude.Nil);
          tmp21 = NofibPrelude.append(tmp19, tmp20);
          return NofibPrelude.Cons("x", tmp21)
        });
        tmp12 = lambda1;
        tmp13 = maybe(tmp11, tmp12, mcp);
        tmp14 = showSquare(c, sq_);
        lambda2 = (undefined, function (pp) {
          let tmp19, tmp20, tmp21;
          tmp19 = showPiece(pp);
          tmp20 = NofibPrelude.Cons(")", NofibPrelude.Nil);
          tmp21 = NofibPrelude.append(tmp19, tmp20);
          return NofibPrelude.Cons("(", tmp21)
        });
        tmp15 = lambda2;
        tmp16 = maybe(NofibPrelude.Nil, tmp15, mpp);
        tmp17 = NofibPrelude.append(tmp14, tmp16);
        tmp18 = NofibPrelude.append(tmp13, tmp17);
        return NofibPrelude.append(tmp10, tmp18)
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
showMoveInFull = function showMoveInFull(a) {
  return showMove(true, a)
};
showMovesAfter = function showMovesAfter(p_, mifs) {
  let param0, param1, param01, param11, param2, p, sq, d_, mifs1, param02, param12, param21, p_1, sq_, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12;
  if (mifs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (mifs instanceof NofibPrelude.Cons.class) {
    param0 = mifs.head;
    param1 = mifs.tail;
    if (param0 instanceof MoveInFull1.class) {
      param01 = param0.a;
      param11 = param0.b;
      param2 = param0.c;
      p = param01;
      sq = param11;
      d_ = param2;
      mifs1 = param1;
      if (p_ instanceof MoveInFull1.class) {
        param02 = p_.a;
        param12 = p_.b;
        param21 = p_.c;
        p_1 = param02;
        sq_ = param12;
        tmp2 = NofibPrelude.nofibStringToList(", ");
        tmp3 = NofibPrelude.eqTup2(p, p_1);
        tmp4 = BenchmarkPrelude.not(tmp3);
        tmp5 = NofibPrelude.eqTup2(sq, sq_);
        tmp6 = BenchmarkPrelude.not(tmp5);
        tmp7 = tmp4 || tmp6;
        tmp8 = MoveInFull1(p, sq, d_);
        tmp9 = showMove(tmp7, tmp8);
        tmp10 = MoveInFull1(p, sq, d_);
        tmp11 = showMovesAfter(tmp10, mifs1);
        tmp12 = NofibPrelude.append(tmp9, tmp11);
        return NofibPrelude.append(tmp2, tmp12)
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
showMoves = function showMoves(mifs) {
  let param0, param1, mif, mifs1, tmp2, tmp3;
  if (mifs instanceof NofibPrelude.Nil.class) {
    throw globalThis.Error("showMoves");
  } else if (mifs instanceof NofibPrelude.Cons.class) {
    param0 = mifs.head;
    param1 = mifs.tail;
    mif = param0;
    mifs1 = param1;
    tmp2 = showMoveInFull(mif);
    tmp3 = showMovesAfter(mif, mifs1);
    return NofibPrelude.append(tmp2, tmp3)
  } else {
    throw new globalThis.Error("match error");
  }
};
sift = function sift(c, bd, ms, sqs) {
  let param0, param1, sq, sqs1, scrut, scrut1, param01, p_, scrut2, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  if (sqs instanceof NofibPrelude.Nil.class) {
    return ms
  } else if (sqs instanceof NofibPrelude.Cons.class) {
    param0 = sqs.head;
    param1 = sqs.tail;
    sq = param0;
    sqs1 = param1;
    scrut = onboard(sq);
    if (scrut === true) {
      scrut1 = pieceAt(bd, sq);
      if (scrut1 instanceof NofibPrelude.None.class) {
        tmp2 = Move1(sq, NofibPrelude.None, NofibPrelude.None);
        tmp3 = NofibPrelude.Cons(tmp2, ms);
        return sift(c, bd, tmp3, sqs1)
      } else if (scrut1 instanceof NofibPrelude.Some.class) {
        param01 = scrut1.x;
        p_ = param01;
        tmp4 = colourOf(p_);
        scrut2 = tmp4 === c;
        if (scrut2 === true) {
          return sift(c, bd, ms, sqs1)
        } else {
          tmp5 = NofibPrelude.Some(p_);
          tmp6 = Move1(sq, tmp5, NofibPrelude.None);
          tmp7 = NofibPrelude.Cons(tmp6, ms);
          return sift(c, bd, tmp7, sqs1)
        }
      } else {
        return sift(c, bd, ms, sqs1)
      }
    } else {
      return sift(c, bd, ms, sqs1)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
moveLine = function moveLine(bd, c, sq, inc, cont) {
  let ml, lambda1;
  ml = function ml(sq1, ms) {
    let sq_, scrut, scrut1, param0, p_, scrut2, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    tmp2 = runtime.safeCall(inc(sq1));
    sq_ = tmp2;
    scrut = onboard(sq_);
    if (scrut === true) {
      scrut1 = pieceAt(bd, sq_);
      if (scrut1 instanceof NofibPrelude.None.class) {
        tmp3 = Move1(sq_, NofibPrelude.None, NofibPrelude.None);
        tmp4 = NofibPrelude.Cons(tmp3, ms);
        return ml(sq_, tmp4)
      } else if (scrut1 instanceof NofibPrelude.Some.class) {
        param0 = scrut1.x;
        p_ = param0;
        tmp5 = colourOf(p_);
        tmp6 = tmp5 === c;
        scrut2 = BenchmarkPrelude.not(tmp6);
        if (scrut2 === true) {
          tmp7 = NofibPrelude.Some(p_);
          tmp8 = Move1(sq_, tmp7, NofibPrelude.None);
          tmp9 = NofibPrelude.Cons(tmp8, ms);
          return runtime.safeCall(cont(tmp9))
        } else {
          return runtime.safeCall(cont(ms))
        }
      } else {
        return runtime.safeCall(cont(ms))
      }
    } else {
      return runtime.safeCall(cont(ms))
    }
  };
  lambda1 = (undefined, function (ms) {
    return ml(sq, ms)
  });
  return lambda1
};
bishopmoves = function bishopmoves(c, sq, bd) {
  let tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, lambda1, lambda2, lambda3, lambda4, lambda5;
  lambda1 = (undefined, function (caseScrut) {
    let first1, first0, x, y, tmp10, tmp11;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      x = first0;
      y = first1;
      tmp10 = x - 1;
      tmp11 = y + 1;
      return [
        tmp10,
        tmp11
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp2 = lambda1;
  lambda2 = (undefined, function (caseScrut) {
    let first1, first0, x, y, tmp10, tmp11;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      x = first0;
      y = first1;
      tmp10 = x + 1;
      tmp11 = y + 1;
      return [
        tmp10,
        tmp11
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp3 = lambda2;
  lambda3 = (undefined, function (caseScrut) {
    let first1, first0, x, y, tmp10, tmp11;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      x = first0;
      y = first1;
      tmp10 = x - 1;
      tmp11 = y - 1;
      return [
        tmp10,
        tmp11
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp4 = lambda3;
  lambda4 = (undefined, function (caseScrut) {
    let first1, first0, x, y, tmp10, tmp11;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      x = first0;
      y = first1;
      tmp10 = x + 1;
      tmp11 = y - 1;
      return [
        tmp10,
        tmp11
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp5 = lambda4;
  lambda5 = (undefined, function (x) {
    return x
  });
  tmp6 = moveLine(bd, c, sq, tmp5, lambda5);
  tmp7 = moveLine(bd, c, sq, tmp4, tmp6);
  tmp8 = moveLine(bd, c, sq, tmp3, tmp7);
  tmp9 = moveLine(bd, c, sq, tmp2, tmp8);
  return runtime.safeCall(tmp9(NofibPrelude.Nil))
};
rookmoves = function rookmoves(c, sq, bd) {
  let tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, lambda1, lambda2, lambda3, lambda4, lambda5;
  lambda1 = (undefined, function (caseScrut) {
    let first1, first0, x, y, tmp10;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      x = first0;
      y = first1;
      tmp10 = x - 1;
      return [
        tmp10,
        y
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp2 = lambda1;
  lambda2 = (undefined, function (caseScrut) {
    let first1, first0, x, y, tmp10;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      x = first0;
      y = first1;
      tmp10 = x + 1;
      return [
        tmp10,
        y
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp3 = lambda2;
  lambda3 = (undefined, function (caseScrut) {
    let first1, first0, x, y, tmp10;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      x = first0;
      y = first1;
      tmp10 = y - 1;
      return [
        x,
        tmp10
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp4 = lambda3;
  lambda4 = (undefined, function (caseScrut) {
    let first1, first0, x, y, tmp10;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      x = first0;
      y = first1;
      tmp10 = y + 1;
      return [
        x,
        tmp10
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp5 = lambda4;
  lambda5 = (undefined, function (x) {
    return x
  });
  tmp6 = moveLine(bd, c, sq, tmp5, lambda5);
  tmp7 = moveLine(bd, c, sq, tmp4, tmp6);
  tmp8 = moveLine(bd, c, sq, tmp3, tmp7);
  tmp9 = moveLine(bd, c, sq, tmp2, tmp8);
  return runtime.safeCall(tmp9(NofibPrelude.Nil))
};
kingmoves = function kingmoves(c, pq, bd) {
  let first1, first0, p, q, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21;
  if (globalThis.Array.isArray(pq) && pq.length === 2) {
    first0 = pq[0];
    first1 = pq[1];
    p = first0;
    q = first1;
    tmp2 = p - 1;
    tmp3 = q + 1;
    tmp4 = q + 1;
    tmp5 = p + 1;
    tmp6 = q + 1;
    tmp7 = p - 1;
    tmp8 = p + 1;
    tmp9 = p - 1;
    tmp10 = q - 1;
    tmp11 = q - 1;
    tmp12 = p + 1;
    tmp13 = q - 1;
    tmp14 = NofibPrelude.Cons([
      tmp12,
      tmp13
    ], NofibPrelude.Nil);
    tmp15 = NofibPrelude.Cons([
      p,
      tmp11
    ], tmp14);
    tmp16 = NofibPrelude.Cons([
      tmp9,
      tmp10
    ], tmp15);
    tmp17 = NofibPrelude.Cons([
      tmp8,
      q
    ], tmp16);
    tmp18 = NofibPrelude.Cons([
      tmp7,
      q
    ], tmp17);
    tmp19 = NofibPrelude.Cons([
      tmp5,
      tmp6
    ], tmp18);
    tmp20 = NofibPrelude.Cons([
      p,
      tmp4
    ], tmp19);
    tmp21 = NofibPrelude.Cons([
      tmp2,
      tmp3
    ], tmp20);
    return sift(c, bd, NofibPrelude.Nil, tmp21)
  } else {
    throw new globalThis.Error("match error");
  }
};
knightmoves = function knightmoves(c, pq, bd) {
  let first1, first0, p, q, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25;
  if (globalThis.Array.isArray(pq) && pq.length === 2) {
    first0 = pq[0];
    first1 = pq[1];
    p = first0;
    q = first1;
    tmp2 = p - 1;
    tmp3 = q + 2;
    tmp4 = p + 1;
    tmp5 = q + 2;
    tmp6 = p - 2;
    tmp7 = q + 1;
    tmp8 = p + 2;
    tmp9 = q + 1;
    tmp10 = p - 2;
    tmp11 = q - 1;
    tmp12 = p + 2;
    tmp13 = q - 1;
    tmp14 = p - 1;
    tmp15 = q - 2;
    tmp16 = p + 1;
    tmp17 = q - 2;
    tmp18 = NofibPrelude.Cons([
      tmp16,
      tmp17
    ], NofibPrelude.Nil);
    tmp19 = NofibPrelude.Cons([
      tmp14,
      tmp15
    ], tmp18);
    tmp20 = NofibPrelude.Cons([
      tmp12,
      tmp13
    ], tmp19);
    tmp21 = NofibPrelude.Cons([
      tmp10,
      tmp11
    ], tmp20);
    tmp22 = NofibPrelude.Cons([
      tmp8,
      tmp9
    ], tmp21);
    tmp23 = NofibPrelude.Cons([
      tmp6,
      tmp7
    ], tmp22);
    tmp24 = NofibPrelude.Cons([
      tmp4,
      tmp5
    ], tmp23);
    tmp25 = NofibPrelude.Cons([
      tmp2,
      tmp3
    ], tmp24);
    return sift(c, bd, NofibPrelude.Nil, tmp25)
  } else {
    throw new globalThis.Error("match error");
  }
};
pawnmoves = function pawnmoves(c, pq, bd) {
  let promote, lscomp1, first1, first0, p, q, fwd, movs, on1, on2, scrut, scrut1, scrut2, scrut3, scrut4, caps, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19;
  if (globalThis.Array.isArray(pq) && pq.length === 2) {
    first0 = pq[0];
    first1 = pq[1];
    p = first0;
    q = first1;
    promote = function promote(xy, mcp) {
      let first11, first01, x, y, scrut5, scrut6, scrut7, scrut8, scrut9, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, lambda1;
      if (globalThis.Array.isArray(xy) && xy.length === 2) {
        first01 = xy[0];
        first11 = xy[1];
        x = first01;
        y = first11;
        if (c instanceof Black1.class) {
          tmp20 = true;
        } else {
          tmp20 = false;
        }
        scrut5 = tmp20;
        if (scrut5 === true) {
          scrut6 = y === 1;
          if (scrut6 === true) {
            tmp21 = true;
          } else {
            tmp21 = false;
          }
        } else {
          tmp21 = false;
        }
        if (c instanceof White1.class) {
          tmp22 = true;
        } else {
          tmp22 = false;
        }
        scrut7 = tmp22;
        if (scrut7 === true) {
          scrut8 = y === 8;
          if (scrut8 === true) {
            tmp23 = true;
          } else {
            tmp23 = false;
          }
        } else {
          tmp23 = false;
        }
        scrut9 = tmp21 || tmp23;
        if (scrut9 === true) {
          tmp24 = NofibPrelude.Cons([
            c,
            Knight1
          ], NofibPrelude.Nil);
          tmp25 = NofibPrelude.Cons([
            c,
            Bishop1
          ], tmp24);
          tmp26 = NofibPrelude.Cons([
            c,
            Rook1
          ], tmp25);
          tmp27 = NofibPrelude.Cons([
            c,
            Queen1
          ], tmp26);
          lambda1 = (undefined, function (param) {
            let tmp29;
            tmp29 = NofibPrelude.Some(param);
            return Move1([
              x,
              y
            ], mcp, tmp29)
          });
          return NofibPrelude.map(lambda1, tmp27)
        } else {
          tmp28 = Move1([
            x,
            y
          ], mcp, NofibPrelude.None);
          return NofibPrelude.Cons(tmp28, NofibPrelude.Nil)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    lscomp1 = function lscomp1(ls) {
      let lscomp2, param0, param1, sq, sqs, tmp20, tmp21;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        sq = param0;
        sqs = param1;
        lscomp2 = function lscomp2(ls1) {
          let param01, param11, h, ls2, param02, p_, scrut5, tmp22, tmp23, tmp24, tmp25, tmp26;
          if (ls1 instanceof NofibPrelude.Nil.class) {
            return lscomp1(sqs)
          } else if (ls1 instanceof NofibPrelude.Cons.class) {
            param01 = ls1.head;
            param11 = ls1.tail;
            h = param01;
            ls2 = param11;
            if (h instanceof NofibPrelude.Some.class) {
              param02 = h.x;
              p_ = param02;
              tmp22 = colourOf(p_);
              tmp23 = tmp22 === c;
              scrut5 = BenchmarkPrelude.not(tmp23);
              if (scrut5 === true) {
                tmp24 = NofibPrelude.Some(p_);
                tmp25 = promote(sq, tmp24);
                tmp26 = lscomp2(ls2);
                return NofibPrelude.Cons(tmp25, tmp26)
              } else {
                return lscomp2(ls2)
              }
            } else {
              return lscomp2(ls2)
            }
          } else {
            throw new globalThis.Error("match error");
          }
        };
        tmp20 = pieceAt(bd, sq);
        tmp21 = NofibPrelude.Cons(tmp20, NofibPrelude.Nil);
        return lscomp2(tmp21)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    if (c instanceof White1.class) {
      tmp2 = 1;
    } else {
      tmp2 = - 1;
    }
    fwd = tmp2;
    tmp3 = q + fwd;
    on1 = [
      p,
      tmp3
    ];
    tmp4 = 2 * fwd;
    tmp5 = q + tmp4;
    on2 = [
      p,
      tmp5
    ];
    scrut = pieceAt(bd, on1);
    if (scrut instanceof NofibPrelude.None.class) {
      tmp6 = promote(on1, NofibPrelude.None);
      scrut1 = q === 2;
      if (scrut1 === true) {
        if (c instanceof White1.class) {
          tmp7 = true;
        } else {
          tmp7 = false;
        }
      } else {
        tmp7 = false;
      }
      scrut2 = q === 7;
      if (scrut2 === true) {
        if (c instanceof Black1.class) {
          tmp8 = true;
        } else {
          tmp8 = false;
        }
      } else {
        tmp8 = false;
      }
      scrut3 = tmp7 || tmp8;
      if (scrut3 === true) {
        scrut4 = pieceAt(bd, on2);
        if (scrut4 instanceof NofibPrelude.None.class) {
          tmp9 = Move1(on2, NofibPrelude.None, NofibPrelude.None);
          tmp10 = NofibPrelude.Cons(tmp9, NofibPrelude.Nil);
        } else {
          tmp10 = NofibPrelude.Nil;
        }
      } else {
        tmp10 = NofibPrelude.Nil;
      }
      tmp11 = NofibPrelude.append(tmp6, tmp10);
    } else {
      tmp11 = NofibPrelude.Nil;
    }
    movs = tmp11;
    tmp12 = p + 1;
    tmp13 = q + fwd;
    tmp14 = p - 1;
    tmp15 = q + fwd;
    tmp16 = NofibPrelude.Cons([
      tmp14,
      tmp15
    ], NofibPrelude.Nil);
    tmp17 = NofibPrelude.Cons([
      tmp12,
      tmp13
    ], tmp16);
    tmp18 = lscomp1(tmp17);
    tmp19 = NofibPrelude.concat(tmp18);
    caps = tmp19;
    return NofibPrelude.append(movs, caps)
  } else {
    throw new globalThis.Error("match error");
  }
};
queenmoves = function queenmoves(c, sq, bd) {
  let tmp2, tmp3;
  tmp2 = bishopmoves(c, sq, bd);
  tmp3 = rookmoves(c, sq, bd);
  return NofibPrelude.append(tmp2, tmp3)
};
kingincheck = function kingincheck(c, bd) {
  let givesCheck, tmp2, tmp3;
  givesCheck = function givesCheck(kxy) {
    let kthreat, first1, first0, k, first11, first01, x, y;
    if (globalThis.Array.isArray(kxy) && kxy.length === 2) {
      first0 = kxy[0];
      first1 = kxy[1];
      k = first0;
      if (globalThis.Array.isArray(first1) && first1.length === 2) {
        first01 = first1[0];
        first11 = first1[1];
        x = first01;
        y = first11;
        kthreat = function kthreat(param) {
          let scrut, first12, first02, xk, yk, scrut1, scrut2, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, lambda1, lambda2, lambda3, lambda4;
          scrut = kingSquare(c, bd);
          if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
            first02 = scrut[0];
            first12 = scrut[1];
            xk = first02;
            yk = first12;
            if (param instanceof King1.class) {
              tmp4 = x - xk;
              tmp5 = NofibPrelude.abs(tmp4);
              scrut1 = tmp5 <= 1;
              if (scrut1 === true) {
                tmp6 = y - yk;
                tmp7 = NofibPrelude.abs(tmp6);
                scrut2 = tmp7 <= 1;
                if (scrut2 === true) {
                  return true
                } else {
                  return false
                }
              } else {
                return false
              }
            } else if (param instanceof Queen1.class) {
              tmp8 = kthreat(Rook1);
              tmp9 = kthreat(Bishop1);
              return tmp8 || tmp9
            } else if (param instanceof Rook1.class) {
              tmp10 = x === xk;
              lambda1 = (undefined, function (caseScrut) {
                let first13, first03, xe, ye, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55;
                if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                  first03 = caseScrut[0];
                  first13 = caseScrut[1];
                  xe = first03;
                  ye = first13;
                  tmp50 = xe === xk;
                  tmp51 = NofibPrelude.min(y, yk);
                  tmp52 = tmp51 < ye;
                  tmp53 = NofibPrelude.max(y, yk);
                  tmp54 = ye < tmp53;
                  tmp55 = tmp52 && tmp54;
                  return tmp50 && tmp55
                } else {
                  throw new globalThis.Error("match error");
                }
              });
              tmp11 = lambda1;
              tmp12 = emptyAtAll(bd, tmp11);
              tmp13 = tmp10 && tmp12;
              tmp14 = y === yk;
              lambda2 = (undefined, function (caseScrut) {
                let first13, first03, xe, ye, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55;
                if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                  first03 = caseScrut[0];
                  first13 = caseScrut[1];
                  xe = first03;
                  ye = first13;
                  tmp50 = ye === yk;
                  tmp51 = NofibPrelude.min(x, xk);
                  tmp52 = tmp51 < xe;
                  tmp53 = NofibPrelude.max(x, xk);
                  tmp54 = xe < tmp53;
                  tmp55 = tmp52 && tmp54;
                  return tmp50 && tmp55
                } else {
                  throw new globalThis.Error("match error");
                }
              });
              tmp15 = lambda2;
              tmp16 = emptyAtAll(bd, tmp15);
              tmp17 = tmp14 && tmp16;
              return tmp13 || tmp17
            } else if (param instanceof Bishop1.class) {
              tmp18 = x + y;
              tmp19 = xk + yk;
              tmp20 = tmp18 === tmp19;
              lambda3 = (undefined, function (caseScrut) {
                let first13, first03, xe, ye, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57;
                if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                  first03 = caseScrut[0];
                  first13 = caseScrut[1];
                  xe = first03;
                  ye = first13;
                  tmp50 = xe + ye;
                  tmp51 = xk + yk;
                  tmp52 = tmp50 === tmp51;
                  tmp53 = NofibPrelude.min(x, xk);
                  tmp54 = tmp53 < xe;
                  tmp55 = NofibPrelude.max(x, xk);
                  tmp56 = xe < tmp55;
                  tmp57 = tmp54 && tmp56;
                  return tmp52 && tmp57
                } else {
                  throw new globalThis.Error("match error");
                }
              });
              tmp21 = lambda3;
              tmp22 = emptyAtAll(bd, tmp21);
              tmp23 = tmp20 && tmp22;
              tmp24 = x - y;
              tmp25 = xk - yk;
              tmp26 = tmp24 === tmp25;
              lambda4 = (undefined, function (caseScrut) {
                let first13, first03, xe, ye, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57;
                if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                  first03 = caseScrut[0];
                  first13 = caseScrut[1];
                  xe = first03;
                  ye = first13;
                  tmp50 = xe - ye;
                  tmp51 = xk - yk;
                  tmp52 = tmp50 === tmp51;
                  tmp53 = NofibPrelude.min(x, xk);
                  tmp54 = tmp53 < xe;
                  tmp55 = NofibPrelude.max(x, xk);
                  tmp56 = xe < tmp55;
                  tmp57 = tmp54 && tmp56;
                  return tmp52 && tmp57
                } else {
                  throw new globalThis.Error("match error");
                }
              });
              tmp27 = lambda4;
              tmp28 = emptyAtAll(bd, tmp27);
              tmp29 = tmp26 && tmp28;
              return tmp23 || tmp29
            } else if (param instanceof Knight1.class) {
              tmp30 = x - xk;
              tmp31 = NofibPrelude.abs(tmp30);
              tmp32 = tmp31 === 2;
              tmp33 = y - yk;
              tmp34 = NofibPrelude.abs(tmp33);
              tmp35 = tmp34 === 1;
              tmp36 = tmp32 && tmp35;
              tmp37 = x - xk;
              tmp38 = NofibPrelude.abs(tmp37);
              tmp39 = tmp38 === 1;
              tmp40 = y - yk;
              tmp41 = NofibPrelude.abs(tmp40);
              tmp42 = tmp41 === 2;
              tmp43 = tmp39 && tmp42;
              return tmp36 || tmp43
            } else if (param instanceof Pawn1.class) {
              tmp44 = x - xk;
              tmp45 = NofibPrelude.abs(tmp44);
              tmp46 = tmp45 === 1;
              if (c instanceof Black1.class) {
                tmp47 = y + 1;
                tmp48 = yk === tmp47;
              } else {
                tmp49 = y - 1;
                tmp48 = yk === tmp49;
              }
              return tmp46 && tmp48
            } else {
              throw new globalThis.Error("match error");
            }
          } else {
            throw new globalThis.Error("match error");
          }
        };
        return kthreat(k)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp2 = opponent(c);
  tmp3 = forcesColoured(tmp2, bd);
  return any(givesCheck, tmp3)
};
tryMove = function tryMove(c, ksq, m, bd) {
  let first1, first0, k, sq, param0, param1, param2, sq_, mcp, mpp, p, bd1, p_, bd2, scrut, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, lambda1, lambda2;
  if (globalThis.Array.isArray(ksq) && ksq.length === 2) {
    first0 = ksq[0];
    first1 = ksq[1];
    k = first0;
    sq = first1;
    if (m instanceof Move1.class) {
      param0 = m.a;
      param1 = m.b;
      param2 = m.c;
      sq_ = param0;
      mcp = param1;
      mpp = param2;
      p = [
        c,
        k
      ];
      tmp2 = rmPieceAt(c, sq, bd);
      bd1 = tmp2;
      lambda1 = (undefined, function (x) {
        return x
      });
      tmp3 = maybe(p, lambda1, mpp);
      p_ = tmp3;
      tmp4 = putPieceAt(sq_, p_, bd1);
      lambda2 = (undefined, function (dummy) {
        let tmp10, tmp11;
        tmp10 = opponent(c);
        tmp11 = rmPieceAt(tmp10, sq_, bd1);
        return putPieceAt(sq_, p_, tmp11)
      });
      tmp5 = lambda2;
      tmp6 = maybe(tmp4, tmp5, mcp);
      bd2 = tmp6;
      tmp7 = kingincheck(c, bd2);
      scrut = BenchmarkPrelude.not(tmp7);
      if (scrut === true) {
        tmp8 = Move1(sq_, mcp, mpp);
        tmp9 = MoveInFull1(p, sq, tmp8);
        return NofibPrelude.Some([
          tmp9,
          bd2
        ])
      } else {
        return NofibPrelude.None
      }
    } else {
      throw globalThis.Error(m);
    }
  } else {
    throw globalThis.Error(m);
  }
};
rawmoves = function rawmoves(c, ksq, bd) {
  let first1, first0, k, sq, m, res, tmp2, tmp3;
  if (globalThis.Array.isArray(ksq) && ksq.length === 2) {
    first0 = ksq[0];
    first1 = ksq[1];
    k = first0;
    sq = first1;
    if (k instanceof King1.class) {
      tmp2 = kingmoves;
    } else if (k instanceof Queen1.class) {
      tmp2 = queenmoves;
    } else if (k instanceof Rook1.class) {
      tmp2 = rookmoves;
    } else if (k instanceof Bishop1.class) {
      tmp2 = bishopmoves;
    } else if (k instanceof Knight1.class) {
      tmp2 = knightmoves;
    } else if (k instanceof Pawn1.class) {
      tmp2 = pawnmoves;
    } else {
      throw new globalThis.Error("match error");
    }
    m = tmp2;
    tmp3 = runtime.safeCall(m(c, sq, bd));
    res = tmp3;
    return res
  } else {
    throw new globalThis.Error("match error");
  }
};
moveDetailsFor = function moveDetailsFor(c, bd) {
  let tmp2, lambda1;
  tmp2 = forcesColoured(c, bd);
  lambda1 = (undefined, function (ksq, ms) {
    let tmp3, tmp4, lambda2;
    lambda2 = (undefined, function (rm, ms_) {
      let tmp5, tmp6, lambda3, lambda4;
      tmp5 = tryMove(c, ksq, rm, bd);
      lambda3 = (undefined, function (x) {
        return x
      });
      lambda4 = (undefined, function (h) {
        let lambda5;
        lambda5 = (undefined, function (t) {
          return NofibPrelude.Cons(h, t)
        });
        return lambda5
      });
      tmp6 = maybe(lambda3, lambda4, tmp5);
      return runtime.safeCall(tmp6(ms_))
    });
    tmp3 = lambda2;
    tmp4 = rawmoves(c, ksq, bd);
    return NofibPrelude.foldr(tmp3, ms, tmp4)
  });
  return NofibPrelude.foldr(lambda1, NofibPrelude.Nil, tmp2)
};
comment = function comment(s) {
  let tmp2, tmp3, tmp4, tmp5;
  if (s instanceof NofibPrelude.Nil.class) {
    tmp2 = true;
  } else {
    tmp2 = false;
  }
  tmp3 = NofibPrelude.take(2, s);
  tmp4 = NofibPrelude.nofibStringToList("--");
  tmp5 = NofibPrelude.listEq(tmp3, tmp4);
  return tmp2 || tmp5
};
last = function last(ls) {
  let param0, param1, h, t, x;
  if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    x = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return x
    } else {
      h = param0;
      t = param1;
      return last(t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
intOfString = function intOfString(s) {
  let tmp2;
  tmp2 = NofibPrelude.nofibListToString(s);
  return runtime.safeCall(globalThis.parseInt(tmp2))
};
parseGoal = function parseGoal(ls) {
  let param0, param1, gltxt, ws, c, scrut, n, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    gltxt = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      tmp2 = words(gltxt);
      ws = tmp2;
      tmp3 = NofibPrelude.head(ws);
      tmp4 = NofibPrelude.nofibStringToList("Black");
      scrut = NofibPrelude.listEq(tmp3, tmp4);
      if (scrut === true) {
        tmp5 = Black1;
      } else {
        tmp5 = White1;
      }
      c = tmp5;
      tmp6 = last(ws);
      tmp7 = intOfString(tmp6);
      n = tmp7;
      return [
        c,
        n
      ]
    } else {
      throw globalThis.Error("parseGoal");
    }
  } else {
    throw globalThis.Error("parseGoal");
  }
};
parseSquare = function parseSquare(r, f, c) {
  let clr, scrut, kin, scrut1, scrut2, scrut3, scrut4, scrut5, scrut6, scrut7, scrut8, tmp2, tmp3;
  scrut8 = c === "-";
  if (scrut8 === true) {
    return NofibPrelude.Nil
  } else {
    scrut = isUpper(c);
    if (scrut === true) {
      tmp2 = Black1;
    } else {
      tmp2 = White1;
    }
    clr = tmp2;
    scrut1 = toLower(c);
    scrut7 = scrut1 === "k";
    if (scrut7 === true) {
      tmp3 = King1;
    } else {
      scrut6 = scrut1 === "q";
      if (scrut6 === true) {
        tmp3 = Queen1;
      } else {
        scrut5 = scrut1 === "r";
        if (scrut5 === true) {
          tmp3 = Rook1;
        } else {
          scrut4 = scrut1 === "b";
          if (scrut4 === true) {
            tmp3 = Bishop1;
          } else {
            scrut3 = scrut1 === "n";
            if (scrut3 === true) {
              tmp3 = Knight1;
            } else {
              scrut2 = scrut1 === "p";
              if (scrut2 === true) {
                tmp3 = Pawn1;
              } else {
                throw new globalThis.Error("match error");
              }
            }
          }
        }
      }
    }
    kin = tmp3;
    return NofibPrelude.Cons([
      [
        clr,
        kin
      ],
      [
        f,
        r
      ]
    ], NofibPrelude.Nil)
  }
};
parseRank = function parseRank(r, x) {
  let tmp2, tmp3, tmp4, lambda1, lambda2;
  tmp2 = NofibPrelude.enumFromTo(1, 8);
  lambda1 = (undefined, function (pp) {
    let tmp5;
    tmp5 = pp === " ";
    return BenchmarkPrelude.not(tmp5)
  });
  tmp3 = NofibPrelude.filter(lambda1, x);
  lambda2 = (undefined, function (a, b) {
    return parseSquare(r, a, b)
  });
  tmp4 = NofibPrelude.zipWith(lambda2, tmp2, tmp3);
  return NofibPrelude.concat(tmp4)
};
parseBoard = function parseBoard(ls) {
  let addPiece, tmp2, tmp3, tmp4, tmp5;
  addPiece = function addPiece(p_sq, x) {
    let first1, first0, p, sq;
    if (globalThis.Array.isArray(p_sq) && p_sq.length === 2) {
      first0 = p_sq[0];
      first1 = p_sq[1];
      p = first0;
      sq = first1;
      return putPieceAt(sq, p, x)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp2 = NofibPrelude.enumFromTo(1, 8);
  tmp3 = NofibPrelude.reverse(tmp2);
  tmp4 = NofibPrelude.zipWith(parseRank, tmp3, ls);
  tmp5 = NofibPrelude.concat(tmp4);
  return NofibPrelude.foldr(addPiece, emptyBoard, tmp5)
};
parseProblem = function parseProblem(s) {
  let bdtxt_gltxt, first1, first0, bdtxt, gltxt, bd, gl, tmp2, tmp3, tmp4, tmp5, lambda1;
  lambda1 = (undefined, function (x) {
    let tmp6;
    tmp6 = comment(x);
    return BenchmarkPrelude.not(tmp6)
  });
  tmp2 = NofibPrelude.filter(lambda1, s);
  tmp3 = NofibPrelude.splitAt(8, tmp2);
  bdtxt_gltxt = tmp3;
  if (globalThis.Array.isArray(bdtxt_gltxt) && bdtxt_gltxt.length === 2) {
    first0 = bdtxt_gltxt[0];
    first1 = bdtxt_gltxt[1];
    bdtxt = first0;
    gltxt = first1;
    tmp4 = parseBoard(bdtxt);
    bd = tmp4;
    tmp5 = parseGoal(gltxt);
    gl = tmp5;
    return [
      bd,
      gl
    ]
  } else {
    throw new globalThis.Error("match error");
  }
};
readProblem = function readProblem(s) {
  let tmp2;
  tmp2 = lines(s);
  return parseProblem(tmp2)
};
foldr_lz = function foldr_lz(f, a, x) {
  let param0, param1, h, t, tmp2, lambda1;
  if (x instanceof NofibPrelude.Cons.class) {
    param0 = x.head;
    param1 = x.tail;
    h = param0;
    t = param1;
    lambda1 = (undefined, function () {
      return foldr_lz(f, a, t)
    });
    tmp2 = NofibPrelude.lazy(lambda1);
    return runtime.safeCall(f(h, tmp2))
  } else if (x instanceof NofibPrelude.Nil.class) {
    return a
  } else {
    throw new globalThis.Error("match error");
  }
};
replies = function replies(bd, c, n) {
  let solnAnd, mds, scrut, scrut1, scrut2, tmp2, tmp3;
  solnAnd = function solnAnd(mifb, rest) {
    let first1, first0, mif, b, sm, param0, s, scrut3, param01, ms, tmp4, tmp5, tmp6, tmp7;
    if (globalThis.Array.isArray(mifb) && mifb.length === 2) {
      first0 = mifb[0];
      first1 = mifb[1];
      mif = first0;
      b = first1;
      tmp4 = opponent(c);
      tmp5 = n - 1;
      tmp6 = solution(b, tmp4, tmp5);
      sm = tmp6;
      if (sm instanceof NofibPrelude.None.class) {
        return NofibPrelude.None
      } else if (sm instanceof NofibPrelude.Some.class) {
        param0 = sm.x;
        s = param0;
        scrut3 = NofibPrelude.force(rest);
        if (scrut3 instanceof NofibPrelude.None.class) {
          return NofibPrelude.None
        } else if (scrut3 instanceof NofibPrelude.Some.class) {
          param01 = scrut3.x;
          ms = param01;
          tmp7 = NofibPrelude.Cons([
            mif,
            s
          ], ms);
          return NofibPrelude.Some(tmp7)
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
  tmp2 = moveDetailsFor(c, bd);
  mds = tmp2;
  scrut1 = n === 0;
  if (scrut1 === true) {
    scrut2 = NofibPrelude.null_(mds);
    if (scrut2 === true) {
      return NofibPrelude.Some(NofibPrelude.Nil)
    } else {
      return NofibPrelude.None
    }
  } else {
    scrut = n > 0;
    if (scrut === true) {
      tmp3 = NofibPrelude.Some(NofibPrelude.Nil);
      return foldr_lz(solnAnd, tmp3, mds)
    } else {
      throw globalThis.Error("n < 0");
    }
  }
};
solution = function solution(bd, c, n) {
  let solnOr, scrut, mds, tmp2;
  solnOr = function solnOr(mifb, other) {
    let first1, first0, mif, b, rsm, param0, rs, scrut1, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    if (globalThis.Array.isArray(mifb) && mifb.length === 2) {
      first0 = mifb[0];
      first1 = mifb[1];
      mif = first0;
      b = first1;
      tmp3 = opponent(c);
      tmp4 = n - 1;
      tmp5 = replies(b, tmp3, tmp4);
      rsm = tmp5;
      if (rsm instanceof NofibPrelude.None.class) {
        return NofibPrelude.force(other)
      } else if (rsm instanceof NofibPrelude.Some.class) {
        param0 = rsm.x;
        if (param0 instanceof NofibPrelude.Nil.class) {
          tmp6 = opponent(c);
          scrut1 = kingincheck(tmp6, b);
          if (scrut1 === true) {
            tmp7 = Solution1(mif, NofibPrelude.Nil);
            return NofibPrelude.Some(tmp7)
          } else {
            return NofibPrelude.force(other)
          }
        } else {
          rs = param0;
          tmp8 = Solution1(mif, rs);
          return NofibPrelude.Some(tmp8)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  scrut = n > 0;
  if (scrut === true) {
    tmp2 = moveDetailsFor(c, bd);
    mds = tmp2;
    return foldr_lz(solnOr, NofibPrelude.None, mds)
  } else {
    throw globalThis.Error("n <= 0");
  }
};
tab = function tab(n) {
  let scrut, tmp2, tmp3;
  scrut = n <= 0;
  if (scrut === true) {
    return NofibPrelude.Nil
  } else {
    tmp2 = n - 1;
    tmp3 = tab(tmp2);
    return NofibPrelude.Cons(" ", tmp3)
  }
};
showReplies = function showReplies(rs, n) {
  let param0, param1, first1, first0, mifs, s, rs1, scrut, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15;
  if (rs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (rs instanceof NofibPrelude.Cons.class) {
    param0 = rs.head;
    param1 = rs.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      mifs = first0;
      s = first1;
      rs1 = param1;
      tmp2 = tab(n);
      tmp3 = NofibPrelude.nofibStringToList("if ");
      tmp4 = NofibPrelude.null_(rs1);
      tmp5 = NofibPrelude.listLen(mifs);
      tmp6 = tmp5 > 1;
      scrut = tmp4 && tmp6;
      if (scrut === true) {
        tmp7 = NofibPrelude.nofibStringToList("others");
      } else {
        tmp8 = showMoves(mifs);
        tmp9 = NofibPrelude.nofibStringToList("; ");
        tmp10 = n + 1;
        tmp11 = showSoln(s, tmp10);
        tmp12 = showReplies(rs1, n);
        tmp13 = NofibPrelude.append(tmp11, tmp12);
        tmp14 = NofibPrelude.append(tmp9, tmp13);
        tmp7 = NofibPrelude.append(tmp8, tmp14);
      }
      tmp15 = NofibPrelude.append(tmp3, tmp7);
      return NofibPrelude.append(tmp2, tmp15)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
showSoln = function showSoln(s, n) {
  let param0, param1, mif, rs, param01, param11, first1, first0, mifs, s_, scrut, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25;
  if (s instanceof Soln1.class) {
    param0 = s.a;
    param1 = s.b;
    mif = param0;
    rs = param1;
    tmp2 = NofibPrelude.stringOfInt(n);
    tmp3 = NofibPrelude.nofibStringToList(tmp2);
    tmp4 = NofibPrelude.nofibStringToList(". ");
    tmp5 = showMoveInFull(mif);
    if (rs instanceof NofibPrelude.Nil.class) {
      tmp6 = NofibPrelude.nofibStringToList("++\n");
    } else if (rs instanceof NofibPrelude.Cons.class) {
      param01 = rs.head;
      param11 = rs.tail;
      if (globalThis.Array.isArray(param01) && param01.length === 2) {
        first0 = param01[0];
        first1 = param01[1];
        mifs = first0;
        s_ = first1;
        if (param11 instanceof NofibPrelude.Nil.class) {
          tmp7 = NofibPrelude.nofibStringToList(", ");
          tmp8 = NofibPrelude.listLen(mifs);
          scrut = tmp8 > 1;
          if (scrut === true) {
            tmp9 = NofibPrelude.nofibStringToList("...");
          } else {
            tmp9 = showMoves(mifs);
          }
          tmp10 = NofibPrelude.nofibStringToList("; ");
          tmp11 = n + 1;
          tmp12 = showSoln(s_, tmp11);
          tmp13 = NofibPrelude.append(tmp10, tmp12);
          tmp14 = NofibPrelude.append(tmp9, tmp13);
          tmp6 = NofibPrelude.append(tmp7, tmp14);
        } else {
          tmp15 = NofibPrelude.nofibStringToList(",\n");
          tmp16 = sort(rs);
          tmp17 = showReplies(tmp16, n);
          tmp6 = NofibPrelude.append(tmp15, tmp17);
        }
      } else {
        tmp18 = NofibPrelude.nofibStringToList(",\n");
        tmp19 = sort(rs);
        tmp20 = showReplies(tmp19, n);
        tmp6 = NofibPrelude.append(tmp18, tmp20);
      }
    } else {
      tmp21 = NofibPrelude.nofibStringToList(",\n");
      tmp22 = sort(rs);
      tmp23 = showReplies(tmp22, n);
      tmp6 = NofibPrelude.append(tmp21, tmp23);
    }
    tmp24 = NofibPrelude.append(tmp5, tmp6);
    tmp25 = NofibPrelude.append(tmp4, tmp24);
    return NofibPrelude.append(tmp3, tmp25)
  } else {
    throw new globalThis.Error("match error");
  }
};
compact = function compact(s) {
  let param0, param1, mif, rs, tmp2;
  if (s instanceof Solution1.class) {
    param0 = s.a;
    param1 = s.b;
    mif = param0;
    rs = param1;
    tmp2 = NofibPrelude.foldr(insertCompact, NofibPrelude.Nil, rs);
    return Soln1(mif, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
insertCompact = function insertCompact(mif_s, ls) {
  let insert, ic, first1, first0, mif, s, cs, tmp2;
  if (globalThis.Array.isArray(mif_s) && mif_s.length === 2) {
    first0 = mif_s[0];
    first1 = mif_s[1];
    mif = first0;
    s = first1;
    insert = function insert(x, ls1) {
      let param0, param1, y, ys, scrut, tmp3, tmp4;
      if (ls1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Cons(x, NofibPrelude.Nil)
      } else if (ls1 instanceof NofibPrelude.Cons.class) {
        param0 = ls1.head;
        param1 = ls1.tail;
        y = param0;
        ys = param1;
        scrut = x > y;
        if (scrut === true) {
          tmp3 = insert(x, ys);
          return NofibPrelude.Cons(y, tmp3)
        } else {
          tmp4 = NofibPrelude.Cons(y, ys);
          return NofibPrelude.Cons(x, tmp4)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    ic = function ic(ls1) {
      let param0, param1, first11, first01, mifs, cs_, etc, a, b, scrut, scrut1, scrut2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, lambda1, lambda2, lambda3, lambda4;
      if (ls1 instanceof NofibPrelude.Nil.class) {
        tmp3 = NofibPrelude.Cons(mif, NofibPrelude.Nil);
        return NofibPrelude.Cons([
          tmp3,
          cs
        ], NofibPrelude.Nil)
      } else if (ls1 instanceof NofibPrelude.Cons.class) {
        param0 = ls1.head;
        param1 = ls1.tail;
        if (globalThis.Array.isArray(param0) && param0.length === 2) {
          first01 = param0[0];
          first11 = param0[1];
          mifs = first01;
          cs_ = first11;
          etc = param1;
          tmp4 = showSoln(cs, 1);
          a = tmp4;
          tmp5 = showSoln(cs_, 1);
          b = tmp5;
          lambda1 = (undefined, function (x, y) {
            return x < y
          });
          lambda2 = (undefined, function (x, y) {
            return x > y
          });
          scrut2 = NofibPrelude.ltList(a, b, lambda1, lambda2);
          if (scrut2 === true) {
            tmp6 = NofibPrelude.Cons(mif, NofibPrelude.Nil);
            tmp7 = NofibPrelude.Cons([
              mifs,
              cs_
            ], etc);
            return NofibPrelude.Cons([
              tmp6,
              cs
            ], tmp7)
          } else {
            scrut1 = NofibPrelude.listEq(a, b);
            if (scrut1 === true) {
              tmp8 = insert(mif, mifs);
              return NofibPrelude.Cons([
                tmp8,
                cs
              ], etc)
            } else {
              lambda3 = (undefined, function (x, y) {
                return x < y
              });
              lambda4 = (undefined, function (x, y) {
                return x > y
              });
              tmp9 = NofibPrelude.ltList(a, b, lambda3, lambda4);
              scrut = BenchmarkPrelude.not(tmp9);
              if (scrut === true) {
                tmp10 = ic(etc);
                return NofibPrelude.Cons([
                  mifs,
                  cs_
                ], tmp10)
              } else {
                throw globalThis.Error("compare error");
              }
            }
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp2 = compact(s);
    cs = tmp2;
    return ic(ls)
  } else {
    throw new globalThis.Error("match error");
  }
};
showResult = function showResult(s) {
  let param0, s1, tmp2;
  if (s instanceof NofibPrelude.None.class) {
    return NofibPrelude.nofibStringToList("No solution!")
  } else if (s instanceof NofibPrelude.Some.class) {
    param0 = s.x;
    s1 = param0;
    tmp2 = compact(s1);
    return showSoln(tmp2, 1)
  } else {
    throw new globalThis.Error("match error");
  }
};
solve = function solve(bd, c, n) {
  let tmp2, tmp3, tmp4;
  tmp2 = 2 * n;
  tmp3 = tmp2 - 1;
  tmp4 = solution(bd, c, tmp3);
  return showResult(tmp4)
};
testMate_nofib = function testMate_nofib(dummy) {
  let input, bdcn, first1, first0, bd, first11, first01, c, n, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20;
  tmp2 = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/heathcote3.prob"));
  tmp3 = runtime.safeCall(tmp2.toString());
  tmp4 = NofibPrelude.nofibStringToList(tmp3);
  input = tmp4;
  tmp5 = readProblem(input);
  bdcn = tmp5;
  if (globalThis.Array.isArray(bdcn) && bdcn.length === 2) {
    first0 = bdcn[0];
    first1 = bdcn[1];
    bd = first0;
    if (globalThis.Array.isArray(first1) && first1.length === 2) {
      first01 = first1[0];
      first11 = first1[1];
      c = first01;
      n = first11;
      tmp6 = showBoard(bd);
      tmp7 = NofibPrelude.nofibStringToList("\n");
      tmp8 = showColour(c);
      tmp9 = NofibPrelude.nofibStringToList(" to move and mate in ");
      tmp10 = NofibPrelude.stringOfInt(n);
      tmp11 = NofibPrelude.nofibStringToList(tmp10);
      tmp12 = NofibPrelude.nofibStringToList("\n");
      tmp13 = NofibPrelude.nofibStringToList("\n");
      tmp14 = solve(bd, c, n);
      tmp15 = NofibPrelude.append(tmp13, tmp14);
      tmp16 = NofibPrelude.append(tmp12, tmp15);
      tmp17 = NofibPrelude.append(tmp11, tmp16);
      tmp18 = NofibPrelude.append(tmp9, tmp17);
      tmp19 = NofibPrelude.append(tmp8, tmp18);
      tmp20 = NofibPrelude.append(tmp7, tmp19);
      return NofibPrelude.append(tmp6, tmp20)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
Kind1 = class Kind {
  constructor() {}
  toString() { return "Kind"; }
};
const King$class = class King extends Kind1 {
  constructor() {
    super();
  }
  toString() { return "King"; }
}; King1 = new King$class;
King1.class = King$class;
const Queen$class = class Queen extends Kind1 {
  constructor() {
    super();
  }
  toString() { return "Queen"; }
}; Queen1 = new Queen$class;
Queen1.class = Queen$class;
const Rook$class = class Rook extends Kind1 {
  constructor() {
    super();
  }
  toString() { return "Rook"; }
}; Rook1 = new Rook$class;
Rook1.class = Rook$class;
const Bishop$class = class Bishop extends Kind1 {
  constructor() {
    super();
  }
  toString() { return "Bishop"; }
}; Bishop1 = new Bishop$class;
Bishop1.class = Bishop$class;
const Knight$class = class Knight extends Kind1 {
  constructor() {
    super();
  }
  toString() { return "Knight"; }
}; Knight1 = new Knight$class;
Knight1.class = Knight$class;
const Pawn$class = class Pawn extends Kind1 {
  constructor() {
    super();
  }
  toString() { return "Pawn"; }
}; Pawn1 = new Pawn$class;
Pawn1.class = Pawn$class;
Colour1 = class Colour {
  constructor() {}
  toString() { return "Colour"; }
};
const Black$class = class Black extends Colour1 {
  constructor() {
    super();
  }
  toString() { return "Black"; }
}; Black1 = new Black$class;
Black1.class = Black$class;
const White$class = class White extends Colour1 {
  constructor() {
    super();
  }
  toString() { return "White"; }
}; White1 = new White$class;
White1.class = White$class;
Board1 = function Board(a1, b1) {
  return new Board.class(a1, b1);
};
Board1.class = class Board {
  constructor(a, b) {
    this.a = a;
    this.b = b;
  }
  toString() { return "Board(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
};
Move1 = function Move(a1, b1, c1) {
  return new Move.class(a1, b1, c1);
};
Move1.class = class Move {
  constructor(a, b, c) {
    this.a = a;
    this.b = b;
    this.c = c;
  }
  toString() { return "Move(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.c) + ")"; }
};
MoveInFull1 = function MoveInFull(a1, b1, c1) {
  return new MoveInFull.class(a1, b1, c1);
};
MoveInFull1.class = class MoveInFull {
  constructor(a, b, c) {
    this.a = a;
    this.b = b;
    this.c = c;
  }
  toString() { return "MoveInFull(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.c) + ")"; }
};
Solution1 = function Solution(a1, b1) {
  return new Solution.class(a1, b1);
};
Solution1.class = class Solution {
  constructor(a, b) {
    this.a = a;
    this.b = b;
  }
  toString() { return "Solution(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
};
tmp = Board1(NofibPrelude.Nil, NofibPrelude.Nil);
emptyBoard = tmp;
Soln1 = function Soln(a1, b1) {
  return new Soln.class(a1, b1);
};
Soln1.class = class Soln {
  constructor(a, b) {
    this.a = a;
    this.b = b;
  }
  toString() { return "Soln(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
};
lambda = (undefined, function () {
  let tmp2, tmp3;
  tmp2 = testMate_nofib(0);
  tmp3 = NofibPrelude.nofibListToString(tmp2);
  return BenchmarkPrelude.print(tmp3)
});
tmp1 = lambda;
BenchmarkPrelude.benchmark(tmp1)