import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let pieceAtWith, consFile, showRank, emptyAtAllAnd, ml, lscomp2, promote, lscomp1, kthreat, givesCheck, addPiece, solnAnd, solnOr, insert, ic, mate1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda14, lambda15, lambda16, lambda17, lambda18, lambda19, lambda20, lambda21, lambda22, lambda23, lambda24, lambda25, lambda26, lambda27, lambda28, lambda29, lambda30, lambda31, lambda32, lambda33, lambda34, lambda35, lambda36, lambda37, pieceAtWith$, showRank$, consFile$, emptyAtAllAnd$, lambda$, ml$, lscomp1$, lscomp2$, promote$, lambda$1, givesCheck$, kthreat$, lambda$2, lambda$3, lambda$4, lambda$5, lambda$6, lambda$7, lambda$8, lambda$9, lambda$10, lambda$11, solnAnd$, solnOr$, ic$;
insert = function insert(x, ls) {
  let param0, param1, y, ys, scrut, tmp, tmp1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Cons(x, NofibPrelude.Nil)
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    y = param0;
    ys = param1;
    scrut = x > y;
    if (scrut === true) {
      tmp = insert(x, ys);
      return NofibPrelude.Cons(y, tmp)
    } else {
      tmp1 = NofibPrelude.Cons(y, ys);
      return NofibPrelude.Cons(x, tmp1)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda34 = (undefined, function (x, y) {
  return x < y
});
lambda35 = (undefined, function (x, y) {
  return x > y
});
lambda36 = (undefined, function (x, y) {
  return x < y
});
lambda37 = (undefined, function (x, y) {
  return x > y
});
ic$ = function ic$(mif, cs, ls) {
  let param0, param1, first1, first0, mifs, cs_, etc, a, b, scrut, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  if (ls instanceof NofibPrelude.Nil.class) {
    tmp = NofibPrelude.Cons(mif, NofibPrelude.Nil);
    return NofibPrelude.Cons([
      tmp,
      cs
    ], NofibPrelude.Nil)
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      mifs = first0;
      cs_ = first1;
      etc = param1;
      tmp1 = mate1.showSoln(cs, 1);
      a = tmp1;
      tmp2 = mate1.showSoln(cs_, 1);
      b = tmp2;
      scrut2 = NofibPrelude.ltList(a, b, lambda34, lambda35);
      if (scrut2 === true) {
        tmp3 = NofibPrelude.Cons(mif, NofibPrelude.Nil);
        tmp4 = NofibPrelude.Cons([
          mifs,
          cs_
        ], etc);
        return NofibPrelude.Cons([
          tmp3,
          cs
        ], tmp4)
      } else {
        scrut1 = NofibPrelude.listEq(a, b);
        if (scrut1 === true) {
          tmp5 = insert(mif, mifs);
          return NofibPrelude.Cons([
            tmp5,
            cs
          ], etc)
        } else {
          tmp6 = NofibPrelude.ltList(a, b, lambda36, lambda37);
          scrut = BenchmarkPrelude.not(tmp6);
          if (scrut === true) {
            tmp7 = ic$(mif, cs, etc);
            return NofibPrelude.Cons([
              mifs,
              cs_
            ], tmp7)
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
ic = function ic(mif, cs) {
  return (ls) => {
    return ic$(mif, cs, ls)
  }
};
solnOr$ = function solnOr$(c, n, mifb, other) {
  let first1, first0, mif, b, rsm, param0, rs, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
  if (globalThis.Array.isArray(mifb) && mifb.length === 2) {
    first0 = mifb[0];
    first1 = mifb[1];
    mif = first0;
    b = first1;
    tmp = mate1.opponent(c);
    tmp1 = n - 1;
    tmp2 = mate1.replies(b, tmp, tmp1);
    rsm = tmp2;
    if (rsm instanceof NofibPrelude.None.class) {
      return NofibPrelude.force(other)
    } else if (rsm instanceof NofibPrelude.Some.class) {
      param0 = rsm.x;
      if (param0 instanceof NofibPrelude.Nil.class) {
        tmp3 = mate1.opponent(c);
        scrut = mate1.kingincheck(tmp3, b);
        if (scrut === true) {
          tmp4 = mate1.Solution(mif, NofibPrelude.Nil);
          return NofibPrelude.Some(tmp4)
        } else {
          return NofibPrelude.force(other)
        }
      } else {
        rs = param0;
        tmp5 = mate1.Solution(mif, rs);
        return NofibPrelude.Some(tmp5)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
solnOr = function solnOr(c, n) {
  return (mifb, other) => {
    return solnOr$(c, n, mifb, other)
  }
};
solnAnd$ = function solnAnd$(c, n, mifb, rest) {
  let first1, first0, mif, b, sm, param0, s, scrut, param01, ms, tmp, tmp1, tmp2, tmp3;
  if (globalThis.Array.isArray(mifb) && mifb.length === 2) {
    first0 = mifb[0];
    first1 = mifb[1];
    mif = first0;
    b = first1;
    tmp = mate1.opponent(c);
    tmp1 = n - 1;
    tmp2 = mate1.solution(b, tmp, tmp1);
    sm = tmp2;
    if (sm instanceof NofibPrelude.None.class) {
      return NofibPrelude.None
    } else if (sm instanceof NofibPrelude.Some.class) {
      param0 = sm.x;
      s = param0;
      scrut = NofibPrelude.force(rest);
      if (scrut instanceof NofibPrelude.None.class) {
        return NofibPrelude.None
      } else if (scrut instanceof NofibPrelude.Some.class) {
        param01 = scrut.x;
        ms = param01;
        tmp3 = NofibPrelude.Cons([
          mif,
          s
        ], ms);
        return NofibPrelude.Some(tmp3)
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
solnAnd = function solnAnd(c, n) {
  return (mifb, rest) => {
    return solnAnd$(c, n, mifb, rest)
  }
};
lambda$11 = function lambda$(f, a, t) {
  return mate1.foldr_lz(f, a, t)
};
lambda33 = (undefined, function (f, a, t) {
  return () => {
    return lambda$11(f, a, t)
  }
});
lambda32 = (undefined, function (x) {
  let tmp;
  tmp = mate1.comment(x);
  return BenchmarkPrelude.not(tmp)
});
addPiece = function addPiece(p_sq, x) {
  let first1, first0, p, sq;
  if (globalThis.Array.isArray(p_sq) && p_sq.length === 2) {
    first0 = p_sq[0];
    first1 = p_sq[1];
    p = first0;
    sq = first1;
    return mate1.putPieceAt(sq, p, x)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda30 = (undefined, function (pp) {
  let tmp;
  tmp = pp === " ";
  return BenchmarkPrelude.not(tmp)
});
lambda$10 = function lambda$(r, a, b) {
  return mate1.parseSquare(r, a, b)
};
lambda31 = (undefined, function (r) {
  return (a, b) => {
    return lambda$10(r, a, b)
  }
});
lambda27 = (undefined, function (x) {
  return x
});
lambda$9 = function lambda$(h, t) {
  return NofibPrelude.Cons(h, t)
};
lambda29 = (undefined, function (h) {
  return (t) => {
    return lambda$9(h, t)
  }
});
lambda28 = (undefined, function (h) {
  return runtime.safeCall(lambda29(h))
});
lambda$8 = function lambda$(c, bd, ksq, rm, ms_) {
  let tmp, tmp1;
  tmp = mate1.tryMove(c, ksq, rm, bd);
  tmp1 = mate1.maybe(lambda27, lambda28, tmp);
  return runtime.safeCall(tmp1(ms_))
};
lambda26 = (undefined, function (c, bd, ksq) {
  return (rm, ms_) => {
    return lambda$8(c, bd, ksq, rm, ms_)
  }
});
lambda$7 = function lambda$(c, bd, ksq, ms) {
  let tmp, tmp1;
  tmp = runtime.safeCall(lambda26(c, bd, ksq));
  tmp1 = mate1.rawmoves(c, ksq, bd);
  return NofibPrelude.foldr(tmp, ms, tmp1)
};
lambda25 = (undefined, function (c, bd) {
  return (ksq, ms) => {
    return lambda$7(c, bd, ksq, ms)
  }
});
lambda23 = (undefined, function (x) {
  return x
});
lambda$6 = function lambda$(c, sq_, bd1, p_, dummy) {
  let tmp, tmp1;
  tmp = mate1.opponent(c);
  tmp1 = mate1.rmPieceAt(tmp, sq_, bd1);
  return mate1.putPieceAt(sq_, p_, tmp1)
};
lambda24 = (undefined, function (c, sq_, bd1, p_) {
  return (dummy) => {
    return lambda$6(c, sq_, bd1, p_, dummy)
  }
});
lambda$5 = function lambda$(y, xk, yk, caseScrut) {
  let first1, first0, xe, ye, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    xe = first0;
    ye = first1;
    tmp = xe === xk;
    tmp1 = NofibPrelude.min(y, yk);
    tmp2 = tmp1 < ye;
    tmp3 = NofibPrelude.max(y, yk);
    tmp4 = ye < tmp3;
    tmp5 = tmp2 && tmp4;
    return tmp && tmp5
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda19 = (undefined, function (y, xk, yk) {
  return (caseScrut) => {
    return lambda$5(y, xk, yk, caseScrut)
  }
});
lambda$4 = function lambda$(x, xk, yk, caseScrut) {
  let first1, first0, xe, ye, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    xe = first0;
    ye = first1;
    tmp = ye === yk;
    tmp1 = NofibPrelude.min(x, xk);
    tmp2 = tmp1 < xe;
    tmp3 = NofibPrelude.max(x, xk);
    tmp4 = xe < tmp3;
    tmp5 = tmp2 && tmp4;
    return tmp && tmp5
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda20 = (undefined, function (x, xk, yk) {
  return (caseScrut) => {
    return lambda$4(x, xk, yk, caseScrut)
  }
});
lambda$3 = function lambda$(x, xk, yk, caseScrut) {
  let first1, first0, xe, ye, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    xe = first0;
    ye = first1;
    tmp = xe + ye;
    tmp1 = xk + yk;
    tmp2 = tmp === tmp1;
    tmp3 = NofibPrelude.min(x, xk);
    tmp4 = tmp3 < xe;
    tmp5 = NofibPrelude.max(x, xk);
    tmp6 = xe < tmp5;
    tmp7 = tmp4 && tmp6;
    return tmp2 && tmp7
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda21 = (undefined, function (x, xk, yk) {
  return (caseScrut) => {
    return lambda$3(x, xk, yk, caseScrut)
  }
});
lambda$2 = function lambda$(x, xk, yk, caseScrut) {
  let first1, first0, xe, ye, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    xe = first0;
    ye = first1;
    tmp = xe - ye;
    tmp1 = xk - yk;
    tmp2 = tmp === tmp1;
    tmp3 = NofibPrelude.min(x, xk);
    tmp4 = tmp3 < xe;
    tmp5 = NofibPrelude.max(x, xk);
    tmp6 = xe < tmp5;
    tmp7 = tmp4 && tmp6;
    return tmp2 && tmp7
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda22 = (undefined, function (x, xk, yk) {
  return (caseScrut) => {
    return lambda$2(x, xk, yk, caseScrut)
  }
});
kthreat$ = function kthreat$(c, bd, x, y, param) {
  let scrut, first1, first0, xk, yk, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45;
  scrut = mate1.kingSquare(c, bd);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    xk = first0;
    yk = first1;
    if (param instanceof mate1.King.class) {
      tmp = x - xk;
      tmp1 = NofibPrelude.abs(tmp);
      scrut1 = tmp1 <= 1;
      if (scrut1 === true) {
        tmp2 = y - yk;
        tmp3 = NofibPrelude.abs(tmp2);
        scrut2 = tmp3 <= 1;
        if (scrut2 === true) {
          return true
        } else {
          return false
        }
      } else {
        return false
      }
    } else if (param instanceof mate1.Queen.class) {
      tmp4 = kthreat$(c, bd, x, y, mate1.Rook);
      tmp5 = kthreat$(c, bd, x, y, mate1.Bishop);
      return tmp4 || tmp5
    } else if (param instanceof mate1.Rook.class) {
      tmp6 = x === xk;
      tmp7 = runtime.safeCall(lambda19(y, xk, yk));
      tmp8 = mate1.emptyAtAll(bd, tmp7);
      tmp9 = tmp6 && tmp8;
      tmp10 = y === yk;
      tmp11 = runtime.safeCall(lambda20(x, xk, yk));
      tmp12 = mate1.emptyAtAll(bd, tmp11);
      tmp13 = tmp10 && tmp12;
      return tmp9 || tmp13
    } else if (param instanceof mate1.Bishop.class) {
      tmp14 = x + y;
      tmp15 = xk + yk;
      tmp16 = tmp14 === tmp15;
      tmp17 = runtime.safeCall(lambda21(x, xk, yk));
      tmp18 = mate1.emptyAtAll(bd, tmp17);
      tmp19 = tmp16 && tmp18;
      tmp20 = x - y;
      tmp21 = xk - yk;
      tmp22 = tmp20 === tmp21;
      tmp23 = runtime.safeCall(lambda22(x, xk, yk));
      tmp24 = mate1.emptyAtAll(bd, tmp23);
      tmp25 = tmp22 && tmp24;
      return tmp19 || tmp25
    } else if (param instanceof mate1.Knight.class) {
      tmp26 = x - xk;
      tmp27 = NofibPrelude.abs(tmp26);
      tmp28 = tmp27 === 2;
      tmp29 = y - yk;
      tmp30 = NofibPrelude.abs(tmp29);
      tmp31 = tmp30 === 1;
      tmp32 = tmp28 && tmp31;
      tmp33 = x - xk;
      tmp34 = NofibPrelude.abs(tmp33);
      tmp35 = tmp34 === 1;
      tmp36 = y - yk;
      tmp37 = NofibPrelude.abs(tmp36);
      tmp38 = tmp37 === 2;
      tmp39 = tmp35 && tmp38;
      return tmp32 || tmp39
    } else if (param instanceof mate1.Pawn.class) {
      tmp40 = x - xk;
      tmp41 = NofibPrelude.abs(tmp40);
      tmp42 = tmp41 === 1;
      if (c instanceof mate1.Black.class) {
        tmp43 = y + 1;
        tmp44 = yk === tmp43;
      } else {
        tmp45 = y - 1;
        tmp44 = yk === tmp45;
      }
      return tmp42 && tmp44
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
kthreat = function kthreat(c, bd, x, y) {
  return (param) => {
    return kthreat$(c, bd, x, y, param)
  }
};
givesCheck$ = function givesCheck$(c, bd, kxy) {
  let first1, first0, k, first11, first01, x, y;
  if (globalThis.Array.isArray(kxy) && kxy.length === 2) {
    first0 = kxy[0];
    first1 = kxy[1];
    k = first0;
    if (globalThis.Array.isArray(first1) && first1.length === 2) {
      first01 = first1[0];
      first11 = first1[1];
      x = first01;
      y = first11;
      return kthreat$(c, bd, x, y, k)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
givesCheck = function givesCheck(c, bd) {
  return (kxy) => {
    return givesCheck$(c, bd, kxy)
  }
};
lambda$1 = function lambda$(mcp, x, y, param) {
  let tmp;
  tmp = NofibPrelude.Some(param);
  return mate1.Move([
    x,
    y
  ], mcp, tmp)
};
lambda18 = (undefined, function (mcp, x, y) {
  return (param) => {
    return lambda$1(mcp, x, y, param)
  }
});
promote$ = function promote$(c, xy, mcp) {
  let first1, first0, x, y, scrut, scrut1, scrut2, scrut3, scrut4, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, lambda$this;
  if (globalThis.Array.isArray(xy) && xy.length === 2) {
    first0 = xy[0];
    first1 = xy[1];
    x = first0;
    y = first1;
    if (c instanceof mate1.Black.class) {
      tmp = true;
    } else {
      tmp = false;
    }
    scrut = tmp;
    if (scrut === true) {
      scrut1 = y === 1;
      if (scrut1 === true) {
        tmp1 = true;
      } else {
        tmp1 = false;
      }
    } else {
      tmp1 = false;
    }
    if (c instanceof mate1.White.class) {
      tmp2 = true;
    } else {
      tmp2 = false;
    }
    scrut2 = tmp2;
    if (scrut2 === true) {
      scrut3 = y === 8;
      if (scrut3 === true) {
        tmp3 = true;
      } else {
        tmp3 = false;
      }
    } else {
      tmp3 = false;
    }
    scrut4 = tmp1 || tmp3;
    if (scrut4 === true) {
      tmp4 = NofibPrelude.Cons([
        c,
        mate1.Knight
      ], NofibPrelude.Nil);
      tmp5 = NofibPrelude.Cons([
        c,
        mate1.Bishop
      ], tmp4);
      tmp6 = NofibPrelude.Cons([
        c,
        mate1.Rook
      ], tmp5);
      tmp7 = NofibPrelude.Cons([
        c,
        mate1.Queen
      ], tmp6);
      lambda$this = runtime.safeCall(lambda18(mcp, x, y));
      return NofibPrelude.map(lambda$this, tmp7)
    } else {
      tmp8 = mate1.Move([
        x,
        y
      ], mcp, NofibPrelude.None);
      return NofibPrelude.Cons(tmp8, NofibPrelude.Nil)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
promote = function promote(c) {
  return (xy, mcp) => {
    return promote$(c, xy, mcp)
  }
};
lscomp2$ = function lscomp2$(c, bd, sq, sqs, ls) {
  let param0, param1, h, ls1, param01, p_, scrut, tmp, tmp1, tmp2, tmp3, tmp4;
  if (ls instanceof NofibPrelude.Nil.class) {
    return lscomp1$(c, bd, sqs)
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    ls1 = param1;
    if (h instanceof NofibPrelude.Some.class) {
      param01 = h.x;
      p_ = param01;
      tmp = mate1.colourOf(p_);
      tmp1 = tmp === c;
      scrut = BenchmarkPrelude.not(tmp1);
      if (scrut === true) {
        tmp2 = NofibPrelude.Some(p_);
        tmp3 = promote$(c, sq, tmp2);
        tmp4 = lscomp2$(c, bd, sq, sqs, ls1);
        return NofibPrelude.Cons(tmp3, tmp4)
      } else {
        return lscomp2$(c, bd, sq, sqs, ls1)
      }
    } else {
      return lscomp2$(c, bd, sq, sqs, ls1)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp2 = function lscomp2(c, bd, sq, sqs) {
  return (ls) => {
    return lscomp2$(c, bd, sq, sqs, ls)
  }
};
lscomp1$ = function lscomp1$(c, bd, ls) {
  let param0, param1, sq, sqs, tmp, tmp1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    sq = param0;
    sqs = param1;
    tmp = mate1.pieceAt(bd, sq);
    tmp1 = NofibPrelude.Cons(tmp, NofibPrelude.Nil);
    return lscomp2$(c, bd, sq, sqs, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp1 = function lscomp1(c, bd) {
  return (ls) => {
    return lscomp1$(c, bd, ls)
  }
};
lambda13 = (undefined, function (caseScrut) {
  let first1, first0, x, y, tmp;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    x = first0;
    y = first1;
    tmp = x - 1;
    return [
      tmp,
      y
    ]
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda14 = (undefined, function (caseScrut) {
  let first1, first0, x, y, tmp;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    x = first0;
    y = first1;
    tmp = x + 1;
    return [
      tmp,
      y
    ]
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda15 = (undefined, function (caseScrut) {
  let first1, first0, x, y, tmp;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    x = first0;
    y = first1;
    tmp = y - 1;
    return [
      x,
      tmp
    ]
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda16 = (undefined, function (caseScrut) {
  let first1, first0, x, y, tmp;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    x = first0;
    y = first1;
    tmp = y + 1;
    return [
      x,
      tmp
    ]
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda17 = (undefined, function (x) {
  return x
});
lambda8 = (undefined, function (caseScrut) {
  let first1, first0, x, y, tmp, tmp1;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    x = first0;
    y = first1;
    tmp = x - 1;
    tmp1 = y + 1;
    return [
      tmp,
      tmp1
    ]
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda9 = (undefined, function (caseScrut) {
  let first1, first0, x, y, tmp, tmp1;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    x = first0;
    y = first1;
    tmp = x + 1;
    tmp1 = y + 1;
    return [
      tmp,
      tmp1
    ]
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda10 = (undefined, function (caseScrut) {
  let first1, first0, x, y, tmp, tmp1;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    x = first0;
    y = first1;
    tmp = x - 1;
    tmp1 = y - 1;
    return [
      tmp,
      tmp1
    ]
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda11 = (undefined, function (caseScrut) {
  let first1, first0, x, y, tmp, tmp1;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    x = first0;
    y = first1;
    tmp = x + 1;
    tmp1 = y - 1;
    return [
      tmp,
      tmp1
    ]
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda12 = (undefined, function (x) {
  return x
});
ml$ = function ml$(bd, c, inc, cont, sq, ms) {
  let sq_, scrut, scrut1, param0, p_, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  tmp = runtime.safeCall(inc(sq));
  sq_ = tmp;
  scrut = mate1.onboard(sq_);
  if (scrut === true) {
    scrut1 = mate1.pieceAt(bd, sq_);
    if (scrut1 instanceof NofibPrelude.None.class) {
      tmp1 = mate1.Move(sq_, NofibPrelude.None, NofibPrelude.None);
      tmp2 = NofibPrelude.Cons(tmp1, ms);
      return ml$(bd, c, inc, cont, sq_, tmp2)
    } else if (scrut1 instanceof NofibPrelude.Some.class) {
      param0 = scrut1.x;
      p_ = param0;
      tmp3 = mate1.colourOf(p_);
      tmp4 = tmp3 === c;
      scrut2 = BenchmarkPrelude.not(tmp4);
      if (scrut2 === true) {
        tmp5 = NofibPrelude.Some(p_);
        tmp6 = mate1.Move(sq_, tmp5, NofibPrelude.None);
        tmp7 = NofibPrelude.Cons(tmp6, ms);
        return runtime.safeCall(cont(tmp7))
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
ml = function ml(bd, c, inc, cont) {
  return (sq, ms) => {
    return ml$(bd, c, inc, cont, sq, ms)
  }
};
lambda$ = function lambda$(bd, c, sq, inc, cont, ms) {
  return ml$(bd, c, inc, cont, sq, ms)
};
lambda7 = (undefined, function (bd, c, sq, inc, cont) {
  return (ms) => {
    return lambda$(bd, c, sq, inc, cont, ms)
  }
});
lambda5 = (undefined, function (cp) {
  let tmp, tmp1, tmp2;
  tmp = mate1.showPiece(cp);
  tmp1 = NofibPrelude.Cons("/", NofibPrelude.Nil);
  tmp2 = NofibPrelude.append(tmp, tmp1);
  return NofibPrelude.Cons("x", tmp2)
});
lambda6 = (undefined, function (pp) {
  let tmp, tmp1, tmp2;
  tmp = mate1.showPiece(pp);
  tmp1 = NofibPrelude.Cons(")", NofibPrelude.Nil);
  tmp2 = NofibPrelude.append(tmp, tmp1);
  return NofibPrelude.Cons("(", tmp2)
});
emptyAtAllAnd$ = function emptyAtAllAnd$(e, b, ls) {
  let param0, param1, first1, first0, s, xs, scrut, scrut1, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return b
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      s = first1;
      xs = param1;
      tmp = runtime.safeCall(e(s));
      scrut = BenchmarkPrelude.not(tmp);
      if (scrut === true) {
        scrut1 = emptyAtAllAnd$(e, b, xs);
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
emptyAtAllAnd = function emptyAtAllAnd(e) {
  return (b, ls) => {
    return emptyAtAllAnd$(e, b, ls)
  }
};
consFile$ = function consFile$(bd, r, f, s) {
  let scrut, param0, p, tmp, tmp1, tmp2;
  scrut = mate1.pieceAt(bd, [
    f,
    r
  ]);
  if (scrut instanceof NofibPrelude.None.class) {
    tmp = NofibPrelude.nofibStringToList(" -");
    return NofibPrelude.append(tmp, s)
  } else if (scrut instanceof NofibPrelude.Some.class) {
    param0 = scrut.x;
    p = param0;
    tmp1 = mate1.pieceToChar(p);
    tmp2 = NofibPrelude.Cons(tmp1, s);
    return NofibPrelude.Cons(" ", tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
consFile = function consFile(bd, r) {
  return (f, s) => {
    return consFile$(bd, r, f, s)
  }
};
showRank$ = function showRank$(bd, r) {
  let tmp, consFile$this;
  tmp = NofibPrelude.enumFromTo(1, 8);
  consFile$this = runtime.safeCall(consFile(bd, r));
  return NofibPrelude.foldr(consFile$this, NofibPrelude.Nil, tmp)
};
showRank = function showRank(bd) {
  return (r) => {
    return showRank$(bd, r)
  }
};
pieceAtWith$ = function pieceAtWith$(sq, c, n, ls) {
  let param0, param1, first1, first0, k, s, xs, scrut;
  if (ls instanceof NofibPrelude.Nil.class) {
    return n
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      k = first0;
      s = first1;
      xs = param1;
      scrut = NofibPrelude.eqTup2(s, sq);
      if (scrut === true) {
        return NofibPrelude.Some([
          c,
          k
        ])
      } else {
        return pieceAtWith$(sq, c, n, xs)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
pieceAtWith = function pieceAtWith(sq) {
  return (c, n, ls) => {
    return pieceAtWith$(sq, c, n, ls)
  }
};
lambda4 = (undefined, function (x) {
  return x === "\n"
});
lambda3 = (undefined, function (l) {
  let tmp;
  tmp = NofibPrelude.Cons("\n", NofibPrelude.Nil);
  return NofibPrelude.append(l, tmp)
});
lambda1 = (undefined, function (x) {
  return x === " "
});
lambda2 = (undefined, function (x) {
  return x === " "
});
lambda = (undefined, function (a, b) {
  let first1, first0, aa, first11, first01, bb, tmp, tmp1;
  if (globalThis.Array.isArray(a) && a.length === 2) {
    first0 = a[0];
    first1 = a[1];
    aa = first0;
    if (globalThis.Array.isArray(b) && b.length === 2) {
      first01 = b[0];
      first11 = b[1];
      bb = first01;
      tmp = NofibPrelude.listLen(aa);
      tmp1 = NofibPrelude.listLen(bb);
      return tmp <= tmp1
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
});
mate1 = class mate {
  static {
    mate1 = mate;
    let tmp, tmp1, lambda38;
    this.Kind = class Kind {
      constructor() {}
      toString() { return "Kind"; }
    };
    const King$class = class King extends mate.Kind {
      constructor() {
        super();
      }
      toString() { return "King"; }
    };
    this.King = new King$class;
    this.King.class = King$class;
    const Queen$class = class Queen extends mate.Kind {
      constructor() {
        super();
      }
      toString() { return "Queen"; }
    };
    this.Queen = new Queen$class;
    this.Queen.class = Queen$class;
    const Rook$class = class Rook extends mate.Kind {
      constructor() {
        super();
      }
      toString() { return "Rook"; }
    };
    this.Rook = new Rook$class;
    this.Rook.class = Rook$class;
    const Bishop$class = class Bishop extends mate.Kind {
      constructor() {
        super();
      }
      toString() { return "Bishop"; }
    };
    this.Bishop = new Bishop$class;
    this.Bishop.class = Bishop$class;
    const Knight$class = class Knight extends mate.Kind {
      constructor() {
        super();
      }
      toString() { return "Knight"; }
    };
    this.Knight = new Knight$class;
    this.Knight.class = Knight$class;
    const Pawn$class = class Pawn extends mate.Kind {
      constructor() {
        super();
      }
      toString() { return "Pawn"; }
    };
    this.Pawn = new Pawn$class;
    this.Pawn.class = Pawn$class;
    this.Colour = class Colour {
      constructor() {}
      toString() { return "Colour"; }
    };
    const Black$class = class Black extends mate.Colour {
      constructor() {
        super();
      }
      toString() { return "Black"; }
    };
    this.Black = new Black$class;
    this.Black.class = Black$class;
    const White$class = class White extends mate.Colour {
      constructor() {
        super();
      }
      toString() { return "White"; }
    };
    this.White = new White$class;
    this.White.class = White$class;
    this.Board = function Board(a1, b1) {
      return new Board.class(a1, b1);
    };
    this.Board.class = class Board {
      constructor(a, b) {
        this.a = a;
        this.b = b;
      }
      toString() { return "Board(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    this.Move = function Move(a1, b1, c1) {
      return new Move.class(a1, b1, c1);
    };
    this.Move.class = class Move {
      constructor(a, b, c) {
        this.a = a;
        this.b = b;
        this.c = c;
      }
      toString() { return "Move(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.c) + ")"; }
    };
    this.MoveInFull = function MoveInFull(a1, b1, c1) {
      return new MoveInFull.class(a1, b1, c1);
    };
    this.MoveInFull.class = class MoveInFull {
      constructor(a, b, c) {
        this.a = a;
        this.b = b;
        this.c = c;
      }
      toString() { return "MoveInFull(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.c) + ")"; }
    };
    this.Solution = function Solution(a1, b1) {
      return new Solution.class(a1, b1);
    };
    this.Solution.class = class Solution {
      constructor(a, b) {
        this.a = a;
        this.b = b;
      }
      toString() { return "Solution(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    tmp = mate.Board(NofibPrelude.Nil, NofibPrelude.Nil);
    this.emptyBoard = tmp;
    this.Soln = function Soln(a1, b1) {
      return new Soln.class(a1, b1);
    };
    this.Soln.class = class Soln {
      constructor(a, b) {
        this.a = a;
        this.b = b;
      }
      toString() { return "Soln(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    lambda38 = (undefined, function () {
      let tmp2, tmp3;
      tmp2 = mate.testMate_nofib(0);
      tmp3 = NofibPrelude.nofibListToString(tmp2);
      return BenchmarkPrelude.print(tmp3)
    });
    tmp1 = lambda38;
    BenchmarkPrelude.benchmark(tmp1)
  }
  static rqpart(le, x, ys, rle, rgt, r) {
    let param0, param1, y, ys1, scrut, tmp, tmp1, tmp2, tmp3;
    if (ys instanceof NofibPrelude.Nil.class) {
      tmp = mate.qsort(le, rgt, r);
      tmp1 = NofibPrelude.Cons(x, tmp);
      return mate.qsort(le, rle, tmp1)
    } else if (ys instanceof NofibPrelude.Cons.class) {
      param0 = ys.head;
      param1 = ys.tail;
      y = param0;
      ys1 = param1;
      scrut = runtime.safeCall(le(y, x));
      if (scrut === true) {
        tmp2 = NofibPrelude.Cons(y, rle);
        return mate.rqpart(le, x, ys1, tmp2, rgt, r)
      } else {
        tmp3 = NofibPrelude.Cons(y, rgt);
        return mate.rqpart(le, x, ys1, rle, tmp3, r)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static rqsort(le1, xs, r1) {
    let param0, param1, x1, xs1, x2;
    if (xs instanceof NofibPrelude.Nil.class) {
      return r1
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param0 = xs.head;
      param1 = xs.tail;
      x2 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Cons(x2, r1)
      } else {
        x1 = param0;
        xs1 = param1;
        return mate.rqpart(le1, x1, xs1, NofibPrelude.Nil, NofibPrelude.Nil, r1)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static qpart(le2, x1, ys1, rlt, rge, r2) {
    let param0, param1, y, ys2, scrut, tmp, tmp1, tmp2, tmp3;
    if (ys1 instanceof NofibPrelude.Nil.class) {
      tmp = mate.rqsort(le2, rge, r2);
      tmp1 = NofibPrelude.Cons(x1, tmp);
      return mate.rqsort(le2, rlt, tmp1)
    } else if (ys1 instanceof NofibPrelude.Cons.class) {
      param0 = ys1.head;
      param1 = ys1.tail;
      y = param0;
      ys2 = param1;
      scrut = runtime.safeCall(le2(x1, y));
      if (scrut === true) {
        tmp2 = NofibPrelude.Cons(y, rge);
        return mate.qpart(le2, x1, ys2, rlt, tmp2, r2)
      } else {
        tmp3 = NofibPrelude.Cons(y, rlt);
        return mate.qpart(le2, x1, ys2, tmp3, rge, r2)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static qsort(le3, xs1, r3) {
    let param0, param1, x2, xs2, x3;
    if (xs1 instanceof NofibPrelude.Nil.class) {
      return r3
    } else if (xs1 instanceof NofibPrelude.Cons.class) {
      param0 = xs1.head;
      param1 = xs1.tail;
      x3 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Cons(x3, r3)
      } else {
        x2 = param0;
        xs2 = param1;
        return mate.qpart(le3, x2, xs2, NofibPrelude.Nil, NofibPrelude.Nil, r3)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static sort(l) {
    let tmp;
    tmp = lambda;
    return mate.qsort(tmp, l, NofibPrelude.Nil)
  } 
  static maybe(d, f, x2) {
    let param0, x3;
    if (x2 instanceof NofibPrelude.None.class) {
      return d
    } else if (x2 instanceof NofibPrelude.Some.class) {
      param0 = x2.x;
      x3 = param0;
      return runtime.safeCall(f(x3))
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static isUpper(c) {
    let x3, scrut, scrut1, tmp;
    tmp = runtime.safeCall(c.charCodeAt(0));
    x3 = tmp;
    scrut = x3 >= 65;
    if (scrut === true) {
      scrut1 = x3 <= 90;
      if (scrut1 === true) {
        return true
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static isLower(c1) {
    let x3, scrut, scrut1, tmp;
    tmp = runtime.safeCall(c1.charCodeAt(0));
    x3 = tmp;
    scrut = x3 >= 97;
    if (scrut === true) {
      scrut1 = x3 <= 122;
      if (scrut1 === true) {
        return true
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static toLower(c2) {
    let scrut, tmp, tmp1;
    scrut = mate.isUpper(c2);
    if (scrut === true) {
      tmp = runtime.safeCall(c2.charCodeAt(0));
      tmp1 = tmp + 32;
      return runtime.safeCall(globalThis.String.fromCharCode(tmp1))
    } else {
      return c2
    }
  } 
  static words(s) {
    let scrut, s_, scrut1, first1, first0, w, s__, tmp;
    scrut = NofibPrelude.dropWhile(lambda1, s);
    if (scrut instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      s_ = scrut;
      scrut1 = NofibPrelude.break_(lambda2, s_);
      if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
        first0 = scrut1[0];
        first1 = scrut1[1];
        w = first0;
        s__ = first1;
        tmp = mate.words(s__);
        return NofibPrelude.Cons(w, tmp)
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  static unlines(ls) {
    let tmp;
    tmp = NofibPrelude.map(lambda3, ls);
    return NofibPrelude.concat(tmp)
  } 
  static lines(s1) {
    let scrut, first1, first0, l1, s_, param0, param1, s__, tmp;
    scrut = NofibPrelude.break_(lambda4, s1);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      l1 = first0;
      s_ = first1;
      if (s_ instanceof NofibPrelude.Nil.class) {
        tmp = NofibPrelude.Nil;
      } else if (s_ instanceof NofibPrelude.Cons.class) {
        param0 = s_.head;
        param1 = s_.tail;
        s__ = param1;
        tmp = mate.lines(s__);
      } else {
        throw new globalThis.Error("match error");
      }
      return NofibPrelude.Cons(l1, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static any(p, ls1) {
    let param0, param1, x3, xs2, tmp, tmp1;
    if (ls1 instanceof NofibPrelude.Nil.class) {
      return false
    } else if (ls1 instanceof NofibPrelude.Cons.class) {
      param0 = ls1.head;
      param1 = ls1.tail;
      x3 = param0;
      xs2 = param1;
      tmp = runtime.safeCall(p(x3));
      tmp1 = mate.any(p, xs2);
      return tmp || tmp1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static showColour(c3) {
    let tmp;
    if (c3 instanceof mate.Black.class) {
      tmp = "Black";
    } else {
      tmp = "White";
    }
    return NofibPrelude.nofibStringToList(tmp)
  } 
  static pieceAt(bd, sq) {
    let param0, param1, wkss, bkss, tmp;
    if (bd instanceof mate.Board.class) {
      param0 = bd.a;
      param1 = bd.b;
      wkss = param0;
      bkss = param1;
      tmp = pieceAtWith$(sq, mate.Black, NofibPrelude.None, bkss);
      return pieceAtWith$(sq, mate.White, tmp, wkss)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static kindToChar(k) {
    if (k instanceof mate.King.class) {
      return "K"
    } else if (k instanceof mate.Queen.class) {
      return "Q"
    } else if (k instanceof mate.Rook.class) {
      return "R"
    } else if (k instanceof mate.Bishop.class) {
      return "B"
    } else if (k instanceof mate.Knight.class) {
      return "N"
    } else if (k instanceof mate.Pawn.class) {
      return "P"
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static pieceToChar(p1) {
    let first1, first0, k1, k2, tmp;
    if (globalThis.Array.isArray(p1) && p1.length === 2) {
      first0 = p1[0];
      first1 = p1[1];
      if (first0 instanceof mate.Black.class) {
        k2 = first1;
        return mate.kindToChar(k2)
      } else if (first0 instanceof mate.White.class) {
        k1 = first1;
        tmp = mate.kindToChar(k1);
        return mate.toLower(tmp)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static showBoard(bd1) {
    let tmp, tmp1, tmp2, showRank$this;
    tmp = NofibPrelude.enumFromTo(1, 8);
    tmp1 = NofibPrelude.reverse(tmp);
    showRank$this = runtime.safeCall(showRank(bd1));
    tmp2 = NofibPrelude.map(showRank$this, tmp1);
    return mate.unlines(tmp2)
  } 
  static showPiece(p2) {
    let first1, first0, c4, k1, tmp;
    if (globalThis.Array.isArray(p2) && p2.length === 2) {
      first0 = p2[0];
      first1 = p2[1];
      c4 = first0;
      k1 = first1;
      tmp = mate.kindToChar(k1);
      return NofibPrelude.Cons(tmp, NofibPrelude.Nil)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static showSquare(c4, x_y) {
    let first1, first0, x3, y, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20;
    if (globalThis.Array.isArray(x_y) && x_y.length === 2) {
      first0 = x_y[0];
      first1 = x_y[1];
      x3 = first0;
      y = first1;
      tmp = x3 - 1;
      tmp1 = NofibPrelude.nofibStringToList("QR");
      tmp2 = NofibPrelude.nofibStringToList("QN");
      tmp3 = NofibPrelude.nofibStringToList("QB");
      tmp4 = NofibPrelude.nofibStringToList("Q");
      tmp5 = NofibPrelude.nofibStringToList("K");
      tmp6 = NofibPrelude.nofibStringToList("KB");
      tmp7 = NofibPrelude.nofibStringToList("KN");
      tmp8 = NofibPrelude.nofibStringToList("KR");
      tmp9 = NofibPrelude.Cons(tmp8, NofibPrelude.Nil);
      tmp10 = NofibPrelude.Cons(tmp7, tmp9);
      tmp11 = NofibPrelude.Cons(tmp6, tmp10);
      tmp12 = NofibPrelude.Cons(tmp5, tmp11);
      tmp13 = NofibPrelude.Cons(tmp4, tmp12);
      tmp14 = NofibPrelude.Cons(tmp3, tmp13);
      tmp15 = NofibPrelude.Cons(tmp2, tmp14);
      tmp16 = NofibPrelude.Cons(tmp1, tmp15);
      tmp17 = NofibPrelude.atIndex(tmp, tmp16);
      if (c4 instanceof mate.Black.class) {
        tmp18 = 9 - y;
      } else {
        tmp18 = y;
      }
      tmp19 = NofibPrelude.stringOfInt(tmp18);
      tmp20 = NofibPrelude.nofibStringToList(tmp19);
      return NofibPrelude.append(tmp17, tmp20)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static emptyAtAll(bd2, e) {
    let param0, param1, wkss, bkss, tmp;
    if (bd2 instanceof mate.Board.class) {
      param0 = bd2.a;
      param1 = bd2.b;
      wkss = param0;
      bkss = param1;
      tmp = emptyAtAllAnd$(e, true, bkss);
      return emptyAtAllAnd$(e, tmp, wkss)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static rPa(sq1, kss) {
    let param0, param1, first1, first0, k1, s2, kss1, scrut, tmp;
    if (kss instanceof NofibPrelude.Nil.class) {
      throw globalThis.Error("rPa");
    } else if (kss instanceof NofibPrelude.Cons.class) {
      param0 = kss.head;
      param1 = kss.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        k1 = first0;
        s2 = first1;
        kss1 = param1;
        scrut = NofibPrelude.eqTup2(s2, sq1);
        if (scrut === true) {
          return kss1
        } else {
          tmp = mate.rPa(sq1, kss1);
          return NofibPrelude.Cons([
            k1,
            s2
          ], tmp)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static rmPieceAt(c5, sq2, bd3) {
    let param0, param1, wkss, bkss, tmp, tmp1;
    if (bd3 instanceof mate.Board.class) {
      param0 = bd3.a;
      param1 = bd3.b;
      wkss = param0;
      bkss = param1;
      if (c5 instanceof mate.White.class) {
        tmp = mate.rPa(sq2, wkss);
        return mate.Board(tmp, bkss)
      } else if (c5 instanceof mate.Black.class) {
        tmp1 = mate.rPa(sq2, bkss);
        return mate.Board(wkss, tmp1)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static putPieceAt(sq3, c_k, bd4) {
    let first1, first0, c6, k1, param0, param1, wkss, bkss, tmp, tmp1;
    if (globalThis.Array.isArray(c_k) && c_k.length === 2) {
      first0 = c_k[0];
      first1 = c_k[1];
      c6 = first0;
      k1 = first1;
      if (bd4 instanceof mate.Board.class) {
        param0 = bd4.a;
        param1 = bd4.b;
        wkss = param0;
        bkss = param1;
        if (c6 instanceof mate.White.class) {
          tmp = NofibPrelude.Cons([
            k1,
            sq3
          ], wkss);
          return mate.Board(tmp, bkss)
        } else if (c6 instanceof mate.Black.class) {
          tmp1 = NofibPrelude.Cons([
            k1,
            sq3
          ], bkss);
          return mate.Board(wkss, tmp1)
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
  static kSq(kss1) {
    let param0, param1, kss2, first1, first0, s2;
    if (kss1 instanceof NofibPrelude.Cons.class) {
      param0 = kss1.head;
      param1 = kss1.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        if (first0 instanceof mate.King.class) {
          s2 = first1;
          return s2
        } else {
          kss2 = param1;
          return mate.kSq(kss2)
        }
      } else {
        kss2 = param1;
        return mate.kSq(kss2)
      }
    } else if (kss1 instanceof NofibPrelude.Nil.class) {
      throw globalThis.Error("kSq");
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static kingSquare(c6, bd5) {
    let param0, param1, wkss, bkss;
    if (bd5 instanceof mate.Board.class) {
      param0 = bd5.a;
      param1 = bd5.b;
      wkss = param0;
      bkss = param1;
      if (c6 instanceof mate.White.class) {
        return mate.kSq(wkss)
      } else if (c6 instanceof mate.Black.class) {
        return mate.kSq(bkss)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static opponent(c7) {
    if (c7 instanceof mate.White.class) {
      return mate.Black
    } else {
      return mate.White
    }
  } 
  static colourOf(c_k1) {
    let first1, first0, c8;
    if (globalThis.Array.isArray(c_k1) && c_k1.length === 2) {
      first0 = c_k1[0];
      first1 = c_k1[1];
      c8 = first0;
      return c8
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static kindOf(c_k2) {
    let first1, first0, k1;
    if (globalThis.Array.isArray(c_k2) && c_k2.length === 2) {
      first0 = c_k2[0];
      first1 = c_k2[1];
      k1 = first1;
      return k1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static onboard(p_q) {
    let first1, first0, p3, q, scrut, scrut1, scrut2, scrut3, scrut4, scrut5, tmp, tmp1;
    if (globalThis.Array.isArray(p_q) && p_q.length === 2) {
      first0 = p_q[0];
      first1 = p_q[1];
      p3 = first0;
      q = first1;
      scrut = p3 >= 1;
      if (scrut === true) {
        scrut1 = p3 <= 8;
        if (scrut1 === true) {
          tmp = true;
        } else {
          tmp = false;
        }
      } else {
        tmp = false;
      }
      scrut2 = tmp;
      if (scrut2 === true) {
        scrut3 = q >= 1;
        if (scrut3 === true) {
          scrut4 = q <= 8;
          if (scrut4 === true) {
            tmp1 = true;
          } else {
            tmp1 = false;
          }
        } else {
          tmp1 = false;
        }
        scrut5 = tmp1;
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
  } 
  static forcesColoured(c8, bd6) {
    let param0, param1, wkss, bkss;
    if (bd6 instanceof mate.Board.class) {
      param0 = bd6.a;
      param1 = bd6.b;
      wkss = param0;
      bkss = param1;
      if (c8 instanceof mate.White.class) {
        return wkss
      } else if (c8 instanceof mate.Black.class) {
        return bkss
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static showMove(withPiece, m) {
    let param0, param1, param2, first1, first0, c9, k1, sq4, param01, param11, param21, sq_, mcp, mpp, capt, param02, prom, param03, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16;
    if (m instanceof mate.MoveInFull.class) {
      param0 = m.a;
      param1 = m.b;
      param2 = m.c;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        c9 = first0;
        k1 = first1;
        sq4 = param1;
        if (param2 instanceof mate.Move.class) {
          param01 = param2.a;
          param11 = param2.b;
          param21 = param2.c;
          sq_ = param01;
          mcp = param11;
          mpp = param21;
          if (mcp instanceof NofibPrelude.Some.class) {
            param02 = mcp.x;
            tmp = true;
          } else {
            tmp = false;
          }
          capt = tmp;
          if (mpp instanceof NofibPrelude.Some.class) {
            param03 = mpp.x;
            tmp1 = true;
          } else {
            tmp1 = false;
          }
          prom = tmp1;
          if (withPiece === true) {
            tmp2 = mate.showPiece([
              c9,
              k1
            ]);
            tmp3 = k1 === mate.King;
            if (k1 instanceof mate.Pawn.class) {
              tmp4 = capt || prom;
              scrut = BenchmarkPrelude.not(tmp4);
              if (scrut === true) {
                tmp5 = true;
              } else {
                tmp5 = false;
              }
            } else {
              tmp5 = false;
            }
            scrut1 = tmp3 || tmp5;
            if (scrut1 === true) {
              tmp6 = NofibPrelude.Nil;
            } else {
              tmp7 = mate.showSquare(c9, sq4);
              tmp6 = NofibPrelude.Cons("/", tmp7);
            }
            tmp8 = NofibPrelude.append(tmp2, tmp6);
          } else {
            tmp8 = NofibPrelude.Nil;
          }
          tmp9 = NofibPrelude.Cons("-", NofibPrelude.Nil);
          tmp10 = lambda5;
          tmp11 = mate.maybe(tmp9, tmp10, mcp);
          tmp12 = mate.showSquare(c9, sq_);
          tmp13 = lambda6;
          tmp14 = mate.maybe(NofibPrelude.Nil, tmp13, mpp);
          tmp15 = NofibPrelude.append(tmp12, tmp14);
          tmp16 = NofibPrelude.append(tmp11, tmp15);
          return NofibPrelude.append(tmp8, tmp16)
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
  static showMoveInFull(a) {
    return mate.showMove(true, a)
  } 
  static showMovesAfter(p_, mifs) {
    let param0, param1, param01, param11, param2, p3, sq4, d_, mifs1, param02, param12, param21, p_1, sq_, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10;
    if (mifs instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (mifs instanceof NofibPrelude.Cons.class) {
      param0 = mifs.head;
      param1 = mifs.tail;
      if (param0 instanceof mate.MoveInFull.class) {
        param01 = param0.a;
        param11 = param0.b;
        param2 = param0.c;
        p3 = param01;
        sq4 = param11;
        d_ = param2;
        mifs1 = param1;
        if (p_ instanceof mate.MoveInFull.class) {
          param02 = p_.a;
          param12 = p_.b;
          param21 = p_.c;
          p_1 = param02;
          sq_ = param12;
          tmp = NofibPrelude.nofibStringToList(", ");
          tmp1 = NofibPrelude.eqTup2(p3, p_1);
          tmp2 = BenchmarkPrelude.not(tmp1);
          tmp3 = NofibPrelude.eqTup2(sq4, sq_);
          tmp4 = BenchmarkPrelude.not(tmp3);
          tmp5 = tmp2 || tmp4;
          tmp6 = mate.MoveInFull(p3, sq4, d_);
          tmp7 = mate.showMove(tmp5, tmp6);
          tmp8 = mate.MoveInFull(p3, sq4, d_);
          tmp9 = mate.showMovesAfter(tmp8, mifs1);
          tmp10 = NofibPrelude.append(tmp7, tmp9);
          return NofibPrelude.append(tmp, tmp10)
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
  static showMoves(mifs1) {
    let param0, param1, mif, mifs2, tmp, tmp1;
    if (mifs1 instanceof NofibPrelude.Nil.class) {
      throw globalThis.Error("showMoves");
    } else if (mifs1 instanceof NofibPrelude.Cons.class) {
      param0 = mifs1.head;
      param1 = mifs1.tail;
      mif = param0;
      mifs2 = param1;
      tmp = mate.showMoveInFull(mif);
      tmp1 = mate.showMovesAfter(mif, mifs2);
      return NofibPrelude.append(tmp, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static sift(c9, bd7, ms, sqs) {
    let param0, param1, sq4, sqs1, scrut, scrut1, param01, p_1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    if (sqs instanceof NofibPrelude.Nil.class) {
      return ms
    } else if (sqs instanceof NofibPrelude.Cons.class) {
      param0 = sqs.head;
      param1 = sqs.tail;
      sq4 = param0;
      sqs1 = param1;
      scrut = mate.onboard(sq4);
      if (scrut === true) {
        scrut1 = mate.pieceAt(bd7, sq4);
        if (scrut1 instanceof NofibPrelude.None.class) {
          tmp = mate.Move(sq4, NofibPrelude.None, NofibPrelude.None);
          tmp1 = NofibPrelude.Cons(tmp, ms);
          return mate.sift(c9, bd7, tmp1, sqs1)
        } else if (scrut1 instanceof NofibPrelude.Some.class) {
          param01 = scrut1.x;
          p_1 = param01;
          tmp2 = mate.colourOf(p_1);
          scrut2 = tmp2 === c9;
          if (scrut2 === true) {
            return mate.sift(c9, bd7, ms, sqs1)
          } else {
            tmp3 = NofibPrelude.Some(p_1);
            tmp4 = mate.Move(sq4, tmp3, NofibPrelude.None);
            tmp5 = NofibPrelude.Cons(tmp4, ms);
            return mate.sift(c9, bd7, tmp5, sqs1)
          }
        } else {
          return mate.sift(c9, bd7, ms, sqs1)
        }
      } else {
        return mate.sift(c9, bd7, ms, sqs1)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static moveLine(bd8, c10, sq4, inc, cont) {
    return runtime.safeCall(lambda7(bd8, c10, sq4, inc, cont))
  } 
  static bishopmoves(c11, sq5, bd9) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    tmp = lambda8;
    tmp1 = lambda9;
    tmp2 = lambda10;
    tmp3 = lambda11;
    tmp4 = mate.moveLine(bd9, c11, sq5, tmp3, lambda12);
    tmp5 = mate.moveLine(bd9, c11, sq5, tmp2, tmp4);
    tmp6 = mate.moveLine(bd9, c11, sq5, tmp1, tmp5);
    tmp7 = mate.moveLine(bd9, c11, sq5, tmp, tmp6);
    return runtime.safeCall(tmp7(NofibPrelude.Nil))
  } 
  static rookmoves(c12, sq6, bd10) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    tmp = lambda13;
    tmp1 = lambda14;
    tmp2 = lambda15;
    tmp3 = lambda16;
    tmp4 = mate.moveLine(bd10, c12, sq6, tmp3, lambda17);
    tmp5 = mate.moveLine(bd10, c12, sq6, tmp2, tmp4);
    tmp6 = mate.moveLine(bd10, c12, sq6, tmp1, tmp5);
    tmp7 = mate.moveLine(bd10, c12, sq6, tmp, tmp6);
    return runtime.safeCall(tmp7(NofibPrelude.Nil))
  } 
  static kingmoves(c13, pq, bd11) {
    let first1, first0, p3, q, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19;
    if (globalThis.Array.isArray(pq) && pq.length === 2) {
      first0 = pq[0];
      first1 = pq[1];
      p3 = first0;
      q = first1;
      tmp = p3 - 1;
      tmp1 = q + 1;
      tmp2 = q + 1;
      tmp3 = p3 + 1;
      tmp4 = q + 1;
      tmp5 = p3 - 1;
      tmp6 = p3 + 1;
      tmp7 = p3 - 1;
      tmp8 = q - 1;
      tmp9 = q - 1;
      tmp10 = p3 + 1;
      tmp11 = q - 1;
      tmp12 = NofibPrelude.Cons([
        tmp10,
        tmp11
      ], NofibPrelude.Nil);
      tmp13 = NofibPrelude.Cons([
        p3,
        tmp9
      ], tmp12);
      tmp14 = NofibPrelude.Cons([
        tmp7,
        tmp8
      ], tmp13);
      tmp15 = NofibPrelude.Cons([
        tmp6,
        q
      ], tmp14);
      tmp16 = NofibPrelude.Cons([
        tmp5,
        q
      ], tmp15);
      tmp17 = NofibPrelude.Cons([
        tmp3,
        tmp4
      ], tmp16);
      tmp18 = NofibPrelude.Cons([
        p3,
        tmp2
      ], tmp17);
      tmp19 = NofibPrelude.Cons([
        tmp,
        tmp1
      ], tmp18);
      return mate.sift(c13, bd11, NofibPrelude.Nil, tmp19)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static knightmoves(c14, pq1, bd12) {
    let first1, first0, p3, q, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23;
    if (globalThis.Array.isArray(pq1) && pq1.length === 2) {
      first0 = pq1[0];
      first1 = pq1[1];
      p3 = first0;
      q = first1;
      tmp = p3 - 1;
      tmp1 = q + 2;
      tmp2 = p3 + 1;
      tmp3 = q + 2;
      tmp4 = p3 - 2;
      tmp5 = q + 1;
      tmp6 = p3 + 2;
      tmp7 = q + 1;
      tmp8 = p3 - 2;
      tmp9 = q - 1;
      tmp10 = p3 + 2;
      tmp11 = q - 1;
      tmp12 = p3 - 1;
      tmp13 = q - 2;
      tmp14 = p3 + 1;
      tmp15 = q - 2;
      tmp16 = NofibPrelude.Cons([
        tmp14,
        tmp15
      ], NofibPrelude.Nil);
      tmp17 = NofibPrelude.Cons([
        tmp12,
        tmp13
      ], tmp16);
      tmp18 = NofibPrelude.Cons([
        tmp10,
        tmp11
      ], tmp17);
      tmp19 = NofibPrelude.Cons([
        tmp8,
        tmp9
      ], tmp18);
      tmp20 = NofibPrelude.Cons([
        tmp6,
        tmp7
      ], tmp19);
      tmp21 = NofibPrelude.Cons([
        tmp4,
        tmp5
      ], tmp20);
      tmp22 = NofibPrelude.Cons([
        tmp2,
        tmp3
      ], tmp21);
      tmp23 = NofibPrelude.Cons([
        tmp,
        tmp1
      ], tmp22);
      return mate.sift(c14, bd12, NofibPrelude.Nil, tmp23)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static pawnmoves(c15, pq2, bd13) {
    let first1, first0, p3, q, fwd, movs, on1, on2, scrut, scrut1, scrut2, scrut3, scrut4, caps, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17;
    if (globalThis.Array.isArray(pq2) && pq2.length === 2) {
      first0 = pq2[0];
      first1 = pq2[1];
      p3 = first0;
      q = first1;
      if (c15 instanceof mate.White.class) {
        tmp = 1;
      } else {
        tmp = - 1;
      }
      fwd = tmp;
      tmp1 = q + fwd;
      on1 = [
        p3,
        tmp1
      ];
      tmp2 = 2 * fwd;
      tmp3 = q + tmp2;
      on2 = [
        p3,
        tmp3
      ];
      scrut = mate.pieceAt(bd13, on1);
      if (scrut instanceof NofibPrelude.None.class) {
        tmp4 = promote$(c15, on1, NofibPrelude.None);
        scrut1 = q === 2;
        if (scrut1 === true) {
          if (c15 instanceof mate.White.class) {
            tmp5 = true;
          } else {
            tmp5 = false;
          }
        } else {
          tmp5 = false;
        }
        scrut2 = q === 7;
        if (scrut2 === true) {
          if (c15 instanceof mate.Black.class) {
            tmp6 = true;
          } else {
            tmp6 = false;
          }
        } else {
          tmp6 = false;
        }
        scrut3 = tmp5 || tmp6;
        if (scrut3 === true) {
          scrut4 = mate.pieceAt(bd13, on2);
          if (scrut4 instanceof NofibPrelude.None.class) {
            tmp7 = mate.Move(on2, NofibPrelude.None, NofibPrelude.None);
            tmp8 = NofibPrelude.Cons(tmp7, NofibPrelude.Nil);
          } else {
            tmp8 = NofibPrelude.Nil;
          }
        } else {
          tmp8 = NofibPrelude.Nil;
        }
        tmp9 = NofibPrelude.append(tmp4, tmp8);
      } else {
        tmp9 = NofibPrelude.Nil;
      }
      movs = tmp9;
      tmp10 = p3 + 1;
      tmp11 = q + fwd;
      tmp12 = p3 - 1;
      tmp13 = q + fwd;
      tmp14 = NofibPrelude.Cons([
        tmp12,
        tmp13
      ], NofibPrelude.Nil);
      tmp15 = NofibPrelude.Cons([
        tmp10,
        tmp11
      ], tmp14);
      tmp16 = lscomp1$(c15, bd13, tmp15);
      tmp17 = NofibPrelude.concat(tmp16);
      caps = tmp17;
      return NofibPrelude.append(movs, caps)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static queenmoves(c16, sq7, bd14) {
    let tmp, tmp1;
    tmp = mate.bishopmoves(c16, sq7, bd14);
    tmp1 = mate.rookmoves(c16, sq7, bd14);
    return NofibPrelude.append(tmp, tmp1)
  } 
  static kingincheck(c17, bd15) {
    let tmp, tmp1, givesCheck$this;
    tmp = mate.opponent(c17);
    tmp1 = mate.forcesColoured(tmp, bd15);
    givesCheck$this = runtime.safeCall(givesCheck(c17, bd15));
    return mate.any(givesCheck$this, tmp1)
  } 
  static tryMove(c18, ksq, m1, bd16) {
    let first1, first0, k1, sq8, param0, param1, param2, sq_, mcp, mpp, p3, bd17, p_1, bd21, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    if (globalThis.Array.isArray(ksq) && ksq.length === 2) {
      first0 = ksq[0];
      first1 = ksq[1];
      k1 = first0;
      sq8 = first1;
      if (m1 instanceof mate.Move.class) {
        param0 = m1.a;
        param1 = m1.b;
        param2 = m1.c;
        sq_ = param0;
        mcp = param1;
        mpp = param2;
        p3 = [
          c18,
          k1
        ];
        tmp = mate.rmPieceAt(c18, sq8, bd16);
        bd17 = tmp;
        tmp1 = mate.maybe(p3, lambda23, mpp);
        p_1 = tmp1;
        tmp2 = mate.putPieceAt(sq_, p_1, bd17);
        tmp3 = runtime.safeCall(lambda24(c18, sq_, bd17, p_1));
        tmp4 = mate.maybe(tmp2, tmp3, mcp);
        bd21 = tmp4;
        tmp5 = mate.kingincheck(c18, bd21);
        scrut = BenchmarkPrelude.not(tmp5);
        if (scrut === true) {
          tmp6 = mate.Move(sq_, mcp, mpp);
          tmp7 = mate.MoveInFull(p3, sq8, tmp6);
          return NofibPrelude.Some([
            tmp7,
            bd21
          ])
        } else {
          return NofibPrelude.None
        }
      } else {
        throw globalThis.Error(m1);
      }
    } else {
      throw globalThis.Error(m1);
    }
  } 
  static rawmoves(c19, ksq1, bd17) {
    let first1, first0, k1, sq8, m2, res, tmp, tmp1;
    if (globalThis.Array.isArray(ksq1) && ksq1.length === 2) {
      first0 = ksq1[0];
      first1 = ksq1[1];
      k1 = first0;
      sq8 = first1;
      if (k1 instanceof mate.King.class) {
        tmp = mate.kingmoves;
      } else if (k1 instanceof mate.Queen.class) {
        tmp = mate.queenmoves;
      } else if (k1 instanceof mate.Rook.class) {
        tmp = mate.rookmoves;
      } else if (k1 instanceof mate.Bishop.class) {
        tmp = mate.bishopmoves;
      } else if (k1 instanceof mate.Knight.class) {
        tmp = mate.knightmoves;
      } else if (k1 instanceof mate.Pawn.class) {
        tmp = mate.pawnmoves;
      } else {
        throw new globalThis.Error("match error");
      }
      m2 = tmp;
      tmp1 = runtime.safeCall(m2(c19, sq8, bd17));
      res = tmp1;
      return res
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static moveDetailsFor(c20, bd18) {
    let tmp, lambda$this;
    tmp = mate.forcesColoured(c20, bd18);
    lambda$this = runtime.safeCall(lambda25(c20, bd18));
    return NofibPrelude.foldr(lambda$this, NofibPrelude.Nil, tmp)
  } 
  static comment(s2) {
    let tmp, tmp1, tmp2, tmp3;
    if (s2 instanceof NofibPrelude.Nil.class) {
      tmp = true;
    } else {
      tmp = false;
    }
    tmp1 = NofibPrelude.take(2, s2);
    tmp2 = NofibPrelude.nofibStringToList("--");
    tmp3 = NofibPrelude.listEq(tmp1, tmp2);
    return tmp || tmp3
  } 
  static last(ls2) {
    let param0, param1, h, t, x3;
    if (ls2 instanceof NofibPrelude.Cons.class) {
      param0 = ls2.head;
      param1 = ls2.tail;
      x3 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return x3
      } else {
        h = param0;
        t = param1;
        return mate.last(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static intOfString(s3) {
    let tmp;
    tmp = NofibPrelude.nofibListToString(s3);
    return runtime.safeCall(globalThis.parseInt(tmp))
  } 
  static parseGoal(ls3) {
    let param0, param1, gltxt, ws, c21, scrut, n, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    if (ls3 instanceof NofibPrelude.Cons.class) {
      param0 = ls3.head;
      param1 = ls3.tail;
      gltxt = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        tmp = mate.words(gltxt);
        ws = tmp;
        tmp1 = NofibPrelude.head(ws);
        tmp2 = NofibPrelude.nofibStringToList("Black");
        scrut = NofibPrelude.listEq(tmp1, tmp2);
        if (scrut === true) {
          tmp3 = mate.Black;
        } else {
          tmp3 = mate.White;
        }
        c21 = tmp3;
        tmp4 = mate.last(ws);
        tmp5 = mate.intOfString(tmp4);
        n = tmp5;
        return [
          c21,
          n
        ]
      } else {
        throw globalThis.Error("parseGoal");
      }
    } else {
      throw globalThis.Error("parseGoal");
    }
  } 
  static parseSquare(r4, f1, c21) {
    let clr, scrut, kin, scrut1, scrut2, scrut3, scrut4, scrut5, scrut6, scrut7, scrut8, tmp, tmp1;
    scrut8 = c21 === "-";
    if (scrut8 === true) {
      return NofibPrelude.Nil
    } else {
      scrut = mate.isUpper(c21);
      if (scrut === true) {
        tmp = mate.Black;
      } else {
        tmp = mate.White;
      }
      clr = tmp;
      scrut1 = mate.toLower(c21);
      scrut7 = scrut1 === "k";
      if (scrut7 === true) {
        tmp1 = mate.King;
      } else {
        scrut6 = scrut1 === "q";
        if (scrut6 === true) {
          tmp1 = mate.Queen;
        } else {
          scrut5 = scrut1 === "r";
          if (scrut5 === true) {
            tmp1 = mate.Rook;
          } else {
            scrut4 = scrut1 === "b";
            if (scrut4 === true) {
              tmp1 = mate.Bishop;
            } else {
              scrut3 = scrut1 === "n";
              if (scrut3 === true) {
                tmp1 = mate.Knight;
              } else {
                scrut2 = scrut1 === "p";
                if (scrut2 === true) {
                  tmp1 = mate.Pawn;
                } else {
                  throw new globalThis.Error("match error");
                }
              }
            }
          }
        }
      }
      kin = tmp1;
      return NofibPrelude.Cons([
        [
          clr,
          kin
        ],
        [
          f1,
          r4
        ]
      ], NofibPrelude.Nil)
    }
  } 
  static parseRank(r5, x3) {
    let tmp, tmp1, tmp2, lambda$this;
    tmp = NofibPrelude.enumFromTo(1, 8);
    tmp1 = NofibPrelude.filter(lambda30, x3);
    lambda$this = runtime.safeCall(lambda31(r5));
    tmp2 = NofibPrelude.zipWith(lambda$this, tmp, tmp1);
    return NofibPrelude.concat(tmp2)
  } 
  static parseBoard(ls4) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = NofibPrelude.enumFromTo(1, 8);
    tmp1 = NofibPrelude.reverse(tmp);
    tmp2 = NofibPrelude.zipWith(mate.parseRank, tmp1, ls4);
    tmp3 = NofibPrelude.concat(tmp2);
    return NofibPrelude.foldr(addPiece, mate.emptyBoard, tmp3)
  } 
  static parseProblem(s4) {
    let bdtxt_gltxt, first1, first0, bdtxt, gltxt, bd19, gl, tmp, tmp1, tmp2, tmp3;
    tmp = NofibPrelude.filter(lambda32, s4);
    tmp1 = NofibPrelude.splitAt(8, tmp);
    bdtxt_gltxt = tmp1;
    if (globalThis.Array.isArray(bdtxt_gltxt) && bdtxt_gltxt.length === 2) {
      first0 = bdtxt_gltxt[0];
      first1 = bdtxt_gltxt[1];
      bdtxt = first0;
      gltxt = first1;
      tmp2 = mate.parseBoard(bdtxt);
      bd19 = tmp2;
      tmp3 = mate.parseGoal(gltxt);
      gl = tmp3;
      return [
        bd19,
        gl
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static readProblem(s5) {
    let tmp;
    tmp = mate.lines(s5);
    return mate.parseProblem(tmp)
  } 
  static foldr_lz(f2, a1, x4) {
    let param0, param1, h, t, tmp, lambda$this;
    if (x4 instanceof NofibPrelude.Cons.class) {
      param0 = x4.head;
      param1 = x4.tail;
      h = param0;
      t = param1;
      lambda$this = runtime.safeCall(lambda33(f2, a1, t));
      tmp = NofibPrelude.lazy(lambda$this);
      return runtime.safeCall(f2(h, tmp))
    } else if (x4 instanceof NofibPrelude.Nil.class) {
      return a1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static replies(bd19, c22, n) {
    let mds, scrut, scrut1, scrut2, tmp, tmp1, solnAnd$this;
    tmp = mate.moveDetailsFor(c22, bd19);
    mds = tmp;
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
        tmp1 = NofibPrelude.Some(NofibPrelude.Nil);
        solnAnd$this = runtime.safeCall(solnAnd(c22, n));
        return mate.foldr_lz(solnAnd$this, tmp1, mds)
      } else {
        throw globalThis.Error("n < 0");
      }
    }
  } 
  static solution(bd20, c23, n1) {
    let scrut, mds, tmp, solnOr$this;
    scrut = n1 > 0;
    if (scrut === true) {
      tmp = mate.moveDetailsFor(c23, bd20);
      mds = tmp;
      solnOr$this = runtime.safeCall(solnOr(c23, n1));
      return mate.foldr_lz(solnOr$this, NofibPrelude.None, mds)
    } else {
      throw globalThis.Error("n <= 0");
    }
  } 
  static tab(n2) {
    let scrut, tmp, tmp1;
    scrut = n2 <= 0;
    if (scrut === true) {
      return NofibPrelude.Nil
    } else {
      tmp = n2 - 1;
      tmp1 = mate.tab(tmp);
      return NofibPrelude.Cons(" ", tmp1)
    }
  } 
  static showReplies(rs, n3) {
    let param0, param1, first1, first0, mifs2, s6, rs1, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13;
    if (rs instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (rs instanceof NofibPrelude.Cons.class) {
      param0 = rs.head;
      param1 = rs.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        mifs2 = first0;
        s6 = first1;
        rs1 = param1;
        tmp = mate.tab(n3);
        tmp1 = NofibPrelude.nofibStringToList("if ");
        tmp2 = NofibPrelude.null_(rs1);
        tmp3 = NofibPrelude.listLen(mifs2);
        tmp4 = tmp3 > 1;
        scrut = tmp2 && tmp4;
        if (scrut === true) {
          tmp5 = NofibPrelude.nofibStringToList("others");
        } else {
          tmp6 = mate.showMoves(mifs2);
          tmp7 = NofibPrelude.nofibStringToList("; ");
          tmp8 = n3 + 1;
          tmp9 = mate.showSoln(s6, tmp8);
          tmp10 = mate.showReplies(rs1, n3);
          tmp11 = NofibPrelude.append(tmp9, tmp10);
          tmp12 = NofibPrelude.append(tmp7, tmp11);
          tmp5 = NofibPrelude.append(tmp6, tmp12);
        }
        tmp13 = NofibPrelude.append(tmp1, tmp5);
        return NofibPrelude.append(tmp, tmp13)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static showSoln(s6, n4) {
    let param0, param1, mif, rs1, param01, param11, first1, first0, mifs2, s_, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23;
    if (s6 instanceof mate.Soln.class) {
      param0 = s6.a;
      param1 = s6.b;
      mif = param0;
      rs1 = param1;
      tmp = NofibPrelude.stringOfInt(n4);
      tmp1 = NofibPrelude.nofibStringToList(tmp);
      tmp2 = NofibPrelude.nofibStringToList(". ");
      tmp3 = mate.showMoveInFull(mif);
      if (rs1 instanceof NofibPrelude.Nil.class) {
        tmp4 = NofibPrelude.nofibStringToList("++\n");
      } else if (rs1 instanceof NofibPrelude.Cons.class) {
        param01 = rs1.head;
        param11 = rs1.tail;
        if (globalThis.Array.isArray(param01) && param01.length === 2) {
          first0 = param01[0];
          first1 = param01[1];
          mifs2 = first0;
          s_ = first1;
          if (param11 instanceof NofibPrelude.Nil.class) {
            tmp5 = NofibPrelude.nofibStringToList(", ");
            tmp6 = NofibPrelude.listLen(mifs2);
            scrut = tmp6 > 1;
            if (scrut === true) {
              tmp7 = NofibPrelude.nofibStringToList("...");
            } else {
              tmp7 = mate.showMoves(mifs2);
            }
            tmp8 = NofibPrelude.nofibStringToList("; ");
            tmp9 = n4 + 1;
            tmp10 = mate.showSoln(s_, tmp9);
            tmp11 = NofibPrelude.append(tmp8, tmp10);
            tmp12 = NofibPrelude.append(tmp7, tmp11);
            tmp4 = NofibPrelude.append(tmp5, tmp12);
          } else {
            tmp13 = NofibPrelude.nofibStringToList(",\n");
            tmp14 = mate.sort(rs1);
            tmp15 = mate.showReplies(tmp14, n4);
            tmp4 = NofibPrelude.append(tmp13, tmp15);
          }
        } else {
          tmp16 = NofibPrelude.nofibStringToList(",\n");
          tmp17 = mate.sort(rs1);
          tmp18 = mate.showReplies(tmp17, n4);
          tmp4 = NofibPrelude.append(tmp16, tmp18);
        }
      } else {
        tmp19 = NofibPrelude.nofibStringToList(",\n");
        tmp20 = mate.sort(rs1);
        tmp21 = mate.showReplies(tmp20, n4);
        tmp4 = NofibPrelude.append(tmp19, tmp21);
      }
      tmp22 = NofibPrelude.append(tmp3, tmp4);
      tmp23 = NofibPrelude.append(tmp2, tmp22);
      return NofibPrelude.append(tmp1, tmp23)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static compact(s7) {
    let param0, param1, mif, rs1, tmp;
    if (s7 instanceof mate.Solution.class) {
      param0 = s7.a;
      param1 = s7.b;
      mif = param0;
      rs1 = param1;
      tmp = NofibPrelude.foldr(mate.insertCompact, NofibPrelude.Nil, rs1);
      return mate.Soln(mif, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static insertCompact(mif_s, ls5) {
    let first1, first0, mif, s8, cs, tmp;
    if (globalThis.Array.isArray(mif_s) && mif_s.length === 2) {
      first0 = mif_s[0];
      first1 = mif_s[1];
      mif = first0;
      s8 = first1;
      tmp = mate.compact(s8);
      cs = tmp;
      return ic$(mif, cs, ls5)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static showResult(s8) {
    let param0, s9, tmp;
    if (s8 instanceof NofibPrelude.None.class) {
      return NofibPrelude.nofibStringToList("No solution!")
    } else if (s8 instanceof NofibPrelude.Some.class) {
      param0 = s8.x;
      s9 = param0;
      tmp = mate.compact(s9);
      return mate.showSoln(tmp, 1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static solve(bd21, c24, n5) {
    let tmp, tmp1, tmp2;
    tmp = 2 * n5;
    tmp1 = tmp - 1;
    tmp2 = mate.solution(bd21, c24, tmp1);
    return mate.showResult(tmp2)
  } 
  static testMate_nofib(dummy) {
    let input, bdcn, first1, first0, bd22, first11, first01, c25, n6, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18;
    tmp = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/heathcote3.prob"));
    tmp1 = runtime.safeCall(tmp.toString());
    tmp2 = NofibPrelude.nofibStringToList(tmp1);
    input = tmp2;
    tmp3 = mate.readProblem(input);
    bdcn = tmp3;
    if (globalThis.Array.isArray(bdcn) && bdcn.length === 2) {
      first0 = bdcn[0];
      first1 = bdcn[1];
      bd22 = first0;
      if (globalThis.Array.isArray(first1) && first1.length === 2) {
        first01 = first1[0];
        first11 = first1[1];
        c25 = first01;
        n6 = first11;
        tmp4 = mate.showBoard(bd22);
        tmp5 = NofibPrelude.nofibStringToList("\n");
        tmp6 = mate.showColour(c25);
        tmp7 = NofibPrelude.nofibStringToList(" to move and mate in ");
        tmp8 = NofibPrelude.stringOfInt(n6);
        tmp9 = NofibPrelude.nofibStringToList(tmp8);
        tmp10 = NofibPrelude.nofibStringToList("\n");
        tmp11 = NofibPrelude.nofibStringToList("\n");
        tmp12 = mate.solve(bd22, c25, n6);
        tmp13 = NofibPrelude.append(tmp11, tmp12);
        tmp14 = NofibPrelude.append(tmp10, tmp13);
        tmp15 = NofibPrelude.append(tmp9, tmp14);
        tmp16 = NofibPrelude.append(tmp7, tmp15);
        tmp17 = NofibPrelude.append(tmp6, tmp16);
        tmp18 = NofibPrelude.append(tmp5, tmp17);
        return NofibPrelude.append(tmp4, tmp18)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  }
  static toString() { return "mate"; }
};
let mate = mate1; export default mate;
