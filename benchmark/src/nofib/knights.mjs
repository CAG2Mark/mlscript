import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let quickSortIntInt, removeBack, showChessSet, addPiece, singleDescend, quickSortIntChessSet, testKnights_nofib, spaces, inquireFront_lz, printBoard, move, RU1, tourFinished, DL1, addFront, myIsDigit, Board1, root, intChessSetComp, isFinished, DR1, LD1, removeFront_lz, possibleMoves, startTour, printTour, LU1, sizeBoard, positionPiece, canMove, intintComp, moveKnight, firstPiece, inquireBack, isSquareFree, tup2InList, myInit, addAllBack, UR1, descAndNo, allDescend, canJumpFirst, sizeQueue, deadEnd, RD1, grow, lastPiece, emptyQueue, canMoveTo, emptyQueue_lz, addAllFront, removeFront, inquireFront, pieceAtTile, UL1, createBoard, deleteFirst, myLast, addAllFront_lz, noPieces, addBack, depthSearch, descendents, assignMoveNo, Direction1, createQueue, tmp, lambda;
myIsDigit = function myIsDigit(c) {
  let tmp1, tmp2, tmp3, tmp4;
  tmp1 = runtime.safeCall(c.codePointAt(0));
  tmp2 = tmp1 >= 48;
  tmp3 = runtime.safeCall(c.codePointAt(0));
  tmp4 = tmp3 <= 57;
  return tmp2 && tmp4
};
intintComp = function intintComp(a_b, c_d) {
  let first1, first0, a, b, first11, first01, c, d, tmp1, tmp2, tmp3, tmp4;
  if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
    first0 = a_b[0];
    first1 = a_b[1];
    a = first0;
    b = first1;
    if (globalThis.Array.isArray(c_d) && c_d.length === 2) {
      first01 = c_d[0];
      first11 = c_d[1];
      c = first01;
      d = first11;
      tmp1 = a < c;
      tmp2 = a === c;
      tmp3 = b < d;
      tmp4 = tmp2 && tmp3;
      return tmp1 || tmp4
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
intChessSetComp = function intChessSetComp(a_b, c_d) {
  let first1, first0, a, b, first11, first01, c, d;
  if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
    first0 = a_b[0];
    first1 = a_b[1];
    a = first0;
    b = first1;
    if (globalThis.Array.isArray(c_d) && c_d.length === 2) {
      first01 = c_d[0];
      first11 = c_d[1];
      c = first01;
      d = first11;
      return a < c
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
myInit = function myInit(a_t) {
  let param0, param1, a, t, a1, tmp1;
  if (a_t instanceof NofibPrelude.Cons.class) {
    param0 = a_t.head;
    param1 = a_t.tail;
    a1 = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      a = param0;
      t = param1;
      tmp1 = myInit(t);
      return NofibPrelude.Cons(a, tmp1)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
myLast = function myLast(a_t) {
  let go, param0, param1, a, t;
  go = function go(h, t1) {
    let param01, param11, head, t2;
    if (t1 instanceof NofibPrelude.Nil.class) {
      return h
    } else if (t1 instanceof NofibPrelude.Cons.class) {
      param01 = t1.head;
      param11 = t1.tail;
      head = param01;
      t2 = param11;
      return go(head, t2)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  if (a_t instanceof NofibPrelude.Cons.class) {
    param0 = a_t.head;
    param1 = a_t.tail;
    a = param0;
    t = param1;
    return go(a, t)
  } else {
    throw new globalThis.Error("match error");
  }
};
quickSortIntInt = function quickSortIntInt(xs) {
  let lscomp2, lscomp1, param0, param1, x, xs1, tmp1, tmp2, tmp3, tmp4, tmp5;
  if (xs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs1 = param1;
    lscomp1 = function lscomp1(ls) {
      let param01, param11, h, t, scrut, tmp6;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param01 = ls.head;
        param11 = ls.tail;
        h = param01;
        t = param11;
        scrut = intintComp(h, x);
        if (scrut === true) {
          tmp6 = lscomp1(t);
          return NofibPrelude.Cons(h, tmp6)
        } else {
          return lscomp1(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    lscomp2 = function lscomp2(ls) {
      let param01, param11, h, t, scrut, tmp6, tmp7;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param01 = ls.head;
        param11 = ls.tail;
        h = param01;
        t = param11;
        tmp6 = intintComp(h, x);
        scrut = BenchmarkPrelude.not(tmp6);
        if (scrut === true) {
          tmp7 = lscomp2(t);
          return NofibPrelude.Cons(h, tmp7)
        } else {
          return lscomp2(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp1 = lscomp1(xs1);
    tmp2 = quickSortIntInt(tmp1);
    tmp3 = lscomp2(xs1);
    tmp4 = quickSortIntInt(tmp3);
    tmp5 = NofibPrelude.Cons(x, tmp4);
    return NofibPrelude.append(tmp2, tmp5)
  } else {
    throw new globalThis.Error("match error");
  }
};
quickSortIntChessSet = function quickSortIntChessSet(xs) {
  let lscomp2, lscomp1, scrut, param0, param1, x, xs1, tmp1, tmp2, tmp3, tmp4, lambda1, lambda2;
  scrut = NofibPrelude.force(xs);
  if (scrut instanceof NofibPrelude.LzNil.class) {
    lambda1 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    return NofibPrelude.lazy(lambda1)
  } else if (scrut instanceof NofibPrelude.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    x = param0;
    xs1 = param1;
    lscomp1 = function lscomp1(ls) {
      let scrut1, param01, param11, h, t, scrut2, lambda3, lambda4;
      scrut1 = NofibPrelude.force(ls);
      if (scrut1 instanceof NofibPrelude.LzNil.class) {
        lambda3 = (undefined, function () {
          return NofibPrelude.LzNil
        });
        return NofibPrelude.lazy(lambda3)
      } else if (scrut1 instanceof NofibPrelude.LzCons.class) {
        param01 = scrut1.head;
        param11 = scrut1.tail;
        h = param01;
        t = param11;
        scrut2 = intChessSetComp(h, x);
        if (scrut2 === true) {
          lambda4 = (undefined, function () {
            let tmp5;
            tmp5 = lscomp1(t);
            return NofibPrelude.LzCons(h, tmp5)
          });
          return NofibPrelude.lazy(lambda4)
        } else {
          return lscomp1(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    lscomp2 = function lscomp2(ls) {
      let scrut1, param01, param11, h, t, scrut2, tmp5, lambda3, lambda4;
      scrut1 = NofibPrelude.force(ls);
      if (scrut1 instanceof NofibPrelude.LzNil.class) {
        lambda3 = (undefined, function () {
          return NofibPrelude.LzNil
        });
        return NofibPrelude.lazy(lambda3)
      } else if (scrut1 instanceof NofibPrelude.LzCons.class) {
        param01 = scrut1.head;
        param11 = scrut1.tail;
        h = param01;
        t = param11;
        tmp5 = intChessSetComp(h, x);
        scrut2 = BenchmarkPrelude.not(tmp5);
        if (scrut2 === true) {
          lambda4 = (undefined, function () {
            let tmp6;
            tmp6 = lscomp2(t);
            return NofibPrelude.LzCons(h, tmp6)
          });
          return NofibPrelude.lazy(lambda4)
        } else {
          return lscomp2(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp1 = lscomp1(xs1);
    tmp2 = quickSortIntChessSet(tmp1);
    lambda2 = (undefined, function () {
      let tmp5, tmp6;
      tmp5 = lscomp2(xs1);
      tmp6 = quickSortIntChessSet(tmp5);
      return NofibPrelude.LzCons(x, tmp6)
    });
    tmp3 = lambda2;
    tmp4 = NofibPrelude.lazy(tmp3);
    return NofibPrelude.append_lz_lz(tmp2, tmp4)
  } else {
    throw new globalThis.Error("match error");
  }
};
sizeQueue = function sizeQueue(xs) {
  return NofibPrelude.listLen(xs)
};
emptyQueue = function emptyQueue(x) {
  return NofibPrelude.listEq(x, NofibPrelude.Nil)
};
removeBack = function removeBack(xs) {
  let param0, param1, x, xs1, x1, tmp1;
  if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x1 = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      x = param0;
      xs1 = param1;
      tmp1 = removeBack(xs1);
      return NofibPrelude.Cons(x, tmp1)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
removeFront = function removeFront(xs) {
  let param0, param1, h, t;
  if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    h = param0;
    t = param1;
    return t
  } else {
    throw new globalThis.Error("match error");
  }
};
inquireBack = function inquireBack(xs) {
  let param0, param1, x, xs1, x1;
  if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x1 = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return x1
    } else {
      x = param0;
      xs1 = param1;
      return inquireBack(xs1)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
inquireFront = function inquireFront(h_t) {
  return NofibPrelude.head(h_t)
};
addAllBack = function addAllBack(list, q) {
  return NofibPrelude.append(q, list)
};
addAllFront = function addAllFront(list, q) {
  return NofibPrelude.append(list, q)
};
addBack = function addBack(x, q) {
  let tmp1;
  tmp1 = NofibPrelude.Cons(x, NofibPrelude.Nil);
  return NofibPrelude.append(q, tmp1)
};
addFront = function addFront(x, q) {
  return NofibPrelude.Cons(x, q)
};
createBoard = function createBoard(x, t) {
  let tmp1, tmp2, lambda1;
  lambda1 = (undefined, function () {
    return t
  });
  tmp1 = NofibPrelude.lazy(lambda1);
  tmp2 = NofibPrelude.Cons(t, NofibPrelude.Nil);
  return Board1(x, 1, tmp1, tmp2)
};
sizeBoard = function sizeBoard(b) {
  let param0, param1, param2, param3, a;
  if (b instanceof Board1.class) {
    param0 = b.a;
    param1 = b.b;
    param2 = b.c;
    param3 = b.d;
    a = param0;
    return a
  } else {
    throw new globalThis.Error("match error");
  }
};
noPieces = function noPieces(b) {
  let param0, param1, param2, param3, n;
  if (b instanceof Board1.class) {
    param0 = b.a;
    param1 = b.b;
    param2 = b.c;
    param3 = b.d;
    n = param1;
    return n
  } else {
    throw new globalThis.Error("match error");
  }
};
addPiece = function addPiece(t, b) {
  let param0, param1, param2, param3, s, n, f, ts, tmp1, tmp2;
  if (b instanceof Board1.class) {
    param0 = b.a;
    param1 = b.b;
    param2 = b.c;
    param3 = b.d;
    s = param0;
    n = param1;
    f = param2;
    ts = param3;
    tmp1 = n + 1;
    tmp2 = NofibPrelude.Cons(t, ts);
    return Board1(s, tmp1, f, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
deleteFirst = function deleteFirst(b) {
  let param0, param1, param2, param3, s, n, f, ts, ts_, tmp1, tmp2, tmp3, lambda1;
  if (b instanceof Board1.class) {
    param0 = b.a;
    param1 = b.b;
    param2 = b.c;
    param3 = b.d;
    s = param0;
    n = param1;
    f = param2;
    ts = param3;
    tmp1 = myInit(ts);
    ts_ = tmp1;
    tmp2 = n - 1;
    lambda1 = (undefined, function () {
      return myLast(ts_)
    });
    tmp3 = NofibPrelude.lazy(lambda1);
    return Board1(s, tmp2, tmp3, ts_)
  } else {
    throw new globalThis.Error("match error");
  }
};
positionPiece = function positionPiece(x, b) {
  let param0, param1, param2, param3, n, ts, tmp1;
  if (b instanceof Board1.class) {
    param0 = b.a;
    param1 = b.b;
    param2 = b.c;
    param3 = b.d;
    n = param1;
    ts = param3;
    tmp1 = n - x;
    return NofibPrelude.atIndex(tmp1, ts)
  } else {
    throw new globalThis.Error("match error");
  }
};
lastPiece = function lastPiece(b) {
  let param0, param1, param2, param3, param01, param11, t, ts;
  if (b instanceof Board1.class) {
    param0 = b.a;
    param1 = b.b;
    param2 = b.c;
    param3 = b.d;
    if (param3 instanceof NofibPrelude.Cons.class) {
      param01 = param3.head;
      param11 = param3.tail;
      t = param01;
      ts = param11;
      return t
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
firstPiece = function firstPiece(b) {
  let param0, param1, param2, param3, f;
  if (b instanceof Board1.class) {
    param0 = b.a;
    param1 = b.b;
    param2 = b.c;
    param3 = b.d;
    f = param2;
    return NofibPrelude.force(f)
  } else {
    throw new globalThis.Error("match error");
  }
};
pieceAtTile = function pieceAtTile(x, b) {
  let find, param0, param1, param2, param3, ts;
  if (b instanceof Board1.class) {
    param0 = b.a;
    param1 = b.b;
    param2 = b.c;
    param3 = b.d;
    ts = param3;
    find = function find(x1, xs) {
      let param01, param11, y, xs1, scrut, tmp1;
      if (xs instanceof NofibPrelude.Nil.class) {
        throw globalThis.Error("Tile not used");
      } else if (xs instanceof NofibPrelude.Cons.class) {
        param01 = xs.head;
        param11 = xs.tail;
        y = param01;
        xs1 = param11;
        scrut = NofibPrelude.eqTup2(x1, y);
        if (scrut === true) {
          tmp1 = NofibPrelude.listLen(xs1);
          return 1 + tmp1
        } else {
          return find(x1, xs1)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    return find(x, ts)
  } else {
    throw new globalThis.Error("match error");
  }
};
tup2InList = function tup2InList(y, xs) {
  let param0, param1, x, xs1, scrut;
  if (xs instanceof NofibPrelude.Nil.class) {
    return false
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs1 = param1;
    scrut = NofibPrelude.eqTup2(y, x);
    if (scrut === true) {
      return true
    } else {
      return tup2InList(y, xs1)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
isSquareFree = function isSquareFree(x, b) {
  let param0, param1, param2, param3, ts, tmp1;
  if (b instanceof Board1.class) {
    param0 = b.a;
    param1 = b.b;
    param2 = b.c;
    param3 = b.d;
    ts = param3;
    tmp1 = tup2InList(x, ts);
    return BenchmarkPrelude.not(tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
assignMoveNo = function assignMoveNo(t, size, z) {
  let param0, param1, first1, first0, x, y, t1, tmp1, tmp2, tmp3, tmp4, tmp5;
  if (t instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (t instanceof NofibPrelude.Cons.class) {
    param0 = t.head;
    param1 = t.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      x = first0;
      y = first1;
      t1 = param1;
      tmp1 = y - 1;
      tmp2 = tmp1 * size;
      tmp3 = tmp2 + x;
      tmp4 = z - 1;
      tmp5 = assignMoveNo(t1, size, tmp4);
      return NofibPrelude.Cons([
        tmp3,
        z
      ], tmp5)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
spaces = function spaces(s, y) {
  let logTen, tmp1, tmp2, tmp3, tmp4;
  logTen = function logTen(x) {
    let scrut, tmp5, tmp6;
    scrut = x === 0;
    if (scrut === true) {
      return 0
    } else {
      tmp5 = NofibPrelude.intDiv(x, 10);
      tmp6 = logTen(tmp5);
      return 1 + tmp6
    }
  };
  tmp1 = logTen(s);
  tmp2 = logTen(y);
  tmp3 = tmp1 - tmp2;
  tmp4 = tmp3 + 1;
  return NofibPrelude.replicate(tmp4, " ")
};
printBoard = function printBoard(s, n, xs) {
  let param0, param1, first1, first0, i, j, xs1, scrut, scrut1, scrut2, scrut3, scrut4, scrut5, scrut6, scrut7, scrut8, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75, tmp76, tmp77, tmp78, tmp79, tmp80, tmp81, tmp82;
  if (xs instanceof NofibPrelude.Nil.class) {
    tmp1 = s * s;
    scrut8 = n > tmp1;
    if (scrut8 === true) {
      return NofibPrelude.Nil
    } else {
      tmp2 = NofibPrelude.intMod(n, s);
      scrut7 = tmp2 != 0;
      if (scrut7 === true) {
        tmp3 = s * s;
        tmp4 = spaces(tmp3, 1);
        tmp5 = n + 1;
        tmp6 = printBoard(s, tmp5, NofibPrelude.Nil);
        tmp7 = NofibPrelude.append(tmp4, tmp6);
        return NofibPrelude.Cons("*", tmp7)
      } else {
        tmp8 = NofibPrelude.intMod(n, s);
        scrut6 = tmp8 === 0;
        if (scrut6 === true) {
          tmp9 = NofibPrelude.nofibStringToList("*\n");
          tmp10 = n + 1;
          tmp11 = printBoard(s, tmp10, NofibPrelude.Nil);
          return NofibPrelude.append(tmp9, tmp11)
        } else {
          throw globalThis.Error("printBoard empty list error");
        }
      }
    }
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      i = first0;
      j = first1;
      xs1 = param1;
      scrut4 = i === n;
      if (scrut4 === true) {
        tmp12 = NofibPrelude.intMod(n, s);
        scrut5 = tmp12 === 0;
        if (scrut5 === true) {
          tmp13 = NofibPrelude.stringOfInt(j);
          tmp14 = NofibPrelude.nofibStringToList(tmp13);
          tmp15 = NofibPrelude.nofibStringToList("\n");
          tmp16 = n + 1;
          tmp17 = printBoard(s, tmp16, xs1);
          tmp18 = NofibPrelude.append(tmp15, tmp17);
          return NofibPrelude.append(tmp14, tmp18)
        } else {
          scrut2 = i === n;
          if (scrut2 === true) {
            tmp19 = NofibPrelude.intMod(n, s);
            scrut3 = tmp19 != 0;
            if (scrut3 === true) {
              tmp20 = NofibPrelude.stringOfInt(j);
              tmp21 = NofibPrelude.nofibStringToList(tmp20);
              tmp22 = s * s;
              tmp23 = spaces(tmp22, j);
              tmp24 = n + 1;
              tmp25 = printBoard(s, tmp24, xs1);
              tmp26 = NofibPrelude.append(tmp23, tmp25);
              return NofibPrelude.append(tmp21, tmp26)
            } else {
              tmp27 = NofibPrelude.intMod(n, s);
              scrut1 = tmp27 != 0;
              if (scrut1 === true) {
                tmp28 = s * s;
                tmp29 = spaces(tmp28, 1);
                tmp30 = n + 1;
                tmp31 = NofibPrelude.Cons([
                  i,
                  j
                ], xs1);
                tmp32 = printBoard(s, tmp30, tmp31);
                tmp33 = NofibPrelude.append(tmp29, tmp32);
                return NofibPrelude.Cons("*", tmp33)
              } else {
                tmp34 = NofibPrelude.intMod(n, s);
                scrut = tmp34 === 0;
                if (scrut === true) {
                  tmp35 = NofibPrelude.nofibStringToList("*\n");
                  tmp36 = n + 1;
                  tmp37 = NofibPrelude.Cons([
                    i,
                    j
                  ], xs1);
                  tmp38 = printBoard(s, tmp36, tmp37);
                  return NofibPrelude.append(tmp35, tmp38)
                } else {
                  throw globalThis.Error("printBoard non-empty list error");
                }
              }
            }
          } else {
            tmp39 = NofibPrelude.intMod(n, s);
            scrut1 = tmp39 != 0;
            if (scrut1 === true) {
              tmp40 = s * s;
              tmp41 = spaces(tmp40, 1);
              tmp42 = n + 1;
              tmp43 = NofibPrelude.Cons([
                i,
                j
              ], xs1);
              tmp44 = printBoard(s, tmp42, tmp43);
              tmp45 = NofibPrelude.append(tmp41, tmp44);
              return NofibPrelude.Cons("*", tmp45)
            } else {
              tmp46 = NofibPrelude.intMod(n, s);
              scrut = tmp46 === 0;
              if (scrut === true) {
                tmp47 = NofibPrelude.nofibStringToList("*\n");
                tmp48 = n + 1;
                tmp49 = NofibPrelude.Cons([
                  i,
                  j
                ], xs1);
                tmp50 = printBoard(s, tmp48, tmp49);
                return NofibPrelude.append(tmp47, tmp50)
              } else {
                throw globalThis.Error("printBoard non-empty list error");
              }
            }
          }
        }
      } else {
        scrut2 = i === n;
        if (scrut2 === true) {
          tmp51 = NofibPrelude.intMod(n, s);
          scrut3 = tmp51 != 0;
          if (scrut3 === true) {
            tmp52 = NofibPrelude.stringOfInt(j);
            tmp53 = NofibPrelude.nofibStringToList(tmp52);
            tmp54 = s * s;
            tmp55 = spaces(tmp54, j);
            tmp56 = n + 1;
            tmp57 = printBoard(s, tmp56, xs1);
            tmp58 = NofibPrelude.append(tmp55, tmp57);
            return NofibPrelude.append(tmp53, tmp58)
          } else {
            tmp59 = NofibPrelude.intMod(n, s);
            scrut1 = tmp59 != 0;
            if (scrut1 === true) {
              tmp60 = s * s;
              tmp61 = spaces(tmp60, 1);
              tmp62 = n + 1;
              tmp63 = NofibPrelude.Cons([
                i,
                j
              ], xs1);
              tmp64 = printBoard(s, tmp62, tmp63);
              tmp65 = NofibPrelude.append(tmp61, tmp64);
              return NofibPrelude.Cons("*", tmp65)
            } else {
              tmp66 = NofibPrelude.intMod(n, s);
              scrut = tmp66 === 0;
              if (scrut === true) {
                tmp67 = NofibPrelude.nofibStringToList("*\n");
                tmp68 = n + 1;
                tmp69 = NofibPrelude.Cons([
                  i,
                  j
                ], xs1);
                tmp70 = printBoard(s, tmp68, tmp69);
                return NofibPrelude.append(tmp67, tmp70)
              } else {
                throw globalThis.Error("printBoard non-empty list error");
              }
            }
          }
        } else {
          tmp71 = NofibPrelude.intMod(n, s);
          scrut1 = tmp71 != 0;
          if (scrut1 === true) {
            tmp72 = s * s;
            tmp73 = spaces(tmp72, 1);
            tmp74 = n + 1;
            tmp75 = NofibPrelude.Cons([
              i,
              j
            ], xs1);
            tmp76 = printBoard(s, tmp74, tmp75);
            tmp77 = NofibPrelude.append(tmp73, tmp76);
            return NofibPrelude.Cons("*", tmp77)
          } else {
            tmp78 = NofibPrelude.intMod(n, s);
            scrut = tmp78 === 0;
            if (scrut === true) {
              tmp79 = NofibPrelude.nofibStringToList("*\n");
              tmp80 = n + 1;
              tmp81 = NofibPrelude.Cons([
                i,
                j
              ], xs1);
              tmp82 = printBoard(s, tmp80, tmp81);
              return NofibPrelude.append(tmp79, tmp82)
            } else {
              throw globalThis.Error("printBoard non-empty list error");
            }
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
move = function move(d, x_y) {
  let first1, first0, x, y, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16;
  if (globalThis.Array.isArray(x_y) && x_y.length === 2) {
    first0 = x_y[0];
    first1 = x_y[1];
    x = first0;
    y = first1;
    if (d instanceof UL1.class) {
      tmp1 = x - 1;
      tmp2 = y - 2;
      return [
        tmp1,
        tmp2
      ]
    } else if (d instanceof UR1.class) {
      tmp3 = x + 1;
      tmp4 = y - 2;
      return [
        tmp3,
        tmp4
      ]
    } else if (d instanceof DL1.class) {
      tmp5 = x - 1;
      tmp6 = y + 2;
      return [
        tmp5,
        tmp6
      ]
    } else if (d instanceof DR1.class) {
      tmp7 = x + 1;
      tmp8 = y + 2;
      return [
        tmp7,
        tmp8
      ]
    } else if (d instanceof LU1.class) {
      tmp9 = x - 2;
      tmp10 = y - 1;
      return [
        tmp9,
        tmp10
      ]
    } else if (d instanceof LD1.class) {
      tmp11 = x - 2;
      tmp12 = y + 1;
      return [
        tmp11,
        tmp12
      ]
    } else if (d instanceof RU1.class) {
      tmp13 = x + 2;
      tmp14 = y - 1;
      return [
        tmp13,
        tmp14
      ]
    } else if (d instanceof RD1.class) {
      tmp15 = x + 2;
      tmp16 = y + 1;
      return [
        tmp15,
        tmp16
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
startTour = function startTour(st, size) {
  let scrut, tmp1;
  tmp1 = NofibPrelude.intMod(size, 2);
  scrut = tmp1 === 0;
  if (scrut === true) {
    return createBoard(size, st)
  } else {
    throw globalThis.Error("Tour doesnt exist for odd size board");
  }
};
moveKnight = function moveKnight(board, dir) {
  let tmp1, tmp2;
  tmp1 = lastPiece(board);
  tmp2 = move(dir, tmp1);
  return addPiece(tmp2, board)
};
canMoveTo = function canMoveTo(x_y, board) {
  let first1, first0, x, y, sze, res, scrut, scrut1, scrut2, scrut3, scrut4, tmp1, tmp2;
  if (globalThis.Array.isArray(x_y) && x_y.length === 2) {
    first0 = x_y[0];
    first1 = x_y[1];
    x = first0;
    y = first1;
    tmp1 = sizeBoard(board);
    sze = tmp1;
    scrut = x >= 1;
    if (scrut === true) {
      scrut1 = x <= sze;
      if (scrut1 === true) {
        scrut2 = y >= 1;
        if (scrut2 === true) {
          scrut3 = y <= sze;
          if (scrut3 === true) {
            scrut4 = isSquareFree(x_y, board);
            if (scrut4 === true) {
              tmp2 = true;
            } else {
              tmp2 = false;
            }
          } else {
            tmp2 = false;
          }
        } else {
          tmp2 = false;
        }
      } else {
        tmp2 = false;
      }
    } else {
      tmp2 = false;
    }
    res = tmp2;
    return res
  } else {
    throw new globalThis.Error("match error");
  }
};
canMove = function canMove(board, dir) {
  let tmp1, tmp2;
  tmp1 = lastPiece(board);
  tmp2 = move(dir, tmp1);
  return canMoveTo(tmp2, board)
};
canJumpFirst = function canJumpFirst(board) {
  let tmp1, tmp2;
  tmp1 = firstPiece(board);
  tmp2 = deleteFirst(board);
  return canMoveTo(tmp1, tmp2)
};
tourFinished = function tourFinished(board) {
  let sze, tmp1, tmp2, tmp3, tmp4, tmp5;
  tmp1 = sizeBoard(board);
  sze = tmp1;
  tmp2 = noPieces(board);
  tmp3 = sze * sze;
  tmp4 = tmp2 === tmp3;
  tmp5 = canJumpFirst(board);
  return tmp4 && tmp5
};
possibleMoves = function possibleMoves(board) {
  let lscomp, res, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
  lscomp = function lscomp(ls) {
    let param0, param1, x, t, scrut, tmp10;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x = param0;
      t = param1;
      scrut = canMove(board, x);
      if (scrut === true) {
        tmp10 = lscomp(t);
        return NofibPrelude.Cons(x, tmp10)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp1 = NofibPrelude.Cons(RD1, NofibPrelude.Nil);
  tmp2 = NofibPrelude.Cons(RU1, tmp1);
  tmp3 = NofibPrelude.Cons(LD1, tmp2);
  tmp4 = NofibPrelude.Cons(LU1, tmp3);
  tmp5 = NofibPrelude.Cons(DR1, tmp4);
  tmp6 = NofibPrelude.Cons(DL1, tmp5);
  tmp7 = NofibPrelude.Cons(UR1, tmp6);
  tmp8 = NofibPrelude.Cons(UL1, tmp7);
  tmp9 = lscomp(tmp8);
  res = tmp9;
  return res
};
deadEnd = function deadEnd(board) {
  let tmp1, tmp2;
  tmp1 = possibleMoves(board);
  tmp2 = NofibPrelude.listLen(tmp1);
  return tmp2 === 0
};
allDescend = function allDescend(board) {
  let tmp1, lambda1;
  tmp1 = possibleMoves(board);
  lambda1 = (undefined, function (b) {
    return moveKnight(board, b)
  });
  return NofibPrelude.map(lambda1, tmp1)
};
descAndNo = function descAndNo(board) {
  let lscomp, tmp1;
  lscomp = function lscomp(ls) {
    let param0, param1, x, t, tmp2, lambda1, lambda2;
    if (ls instanceof NofibPrelude.Nil.class) {
      lambda1 = (undefined, function () {
        return NofibPrelude.LzNil
      });
      return NofibPrelude.lazy(lambda1)
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x = param0;
      t = param1;
      lambda2 = (undefined, function () {
        let tmp3, tmp4, tmp5, tmp6;
        tmp3 = deleteFirst(x);
        tmp4 = possibleMoves(tmp3);
        tmp5 = NofibPrelude.listLen(tmp4);
        tmp6 = lscomp(t);
        return NofibPrelude.LzCons([
          tmp5,
          x
        ], tmp6)
      });
      tmp2 = lambda2;
      return NofibPrelude.lazy(tmp2)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp1 = allDescend(board);
  return lscomp(tmp1)
};
singleDescend = function singleDescend(board) {
  let lscomp, tmp1;
  lscomp = function lscomp(ls) {
    let scrut, param0, param1, first1, first0, y, x, t, scrut1, tmp2;
    scrut = NofibPrelude.force(ls);
    if (scrut instanceof NofibPrelude.LzNil.class) {
      return NofibPrelude.Nil
    } else if (scrut instanceof NofibPrelude.LzCons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        y = first0;
        x = first1;
        t = param1;
        scrut1 = y === 1;
        if (scrut1 === true) {
          tmp2 = lscomp(t);
          return NofibPrelude.Cons(x, tmp2)
        } else {
          return lscomp(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp1 = descAndNo(board);
  return lscomp(tmp1)
};
descendents = function descendents(board) {
  let singles, scrut, res, scrut1, param0, param1, h, scrut2, scrut3, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, lambda1, lambda2, lambda3;
  tmp1 = canJumpFirst(board);
  tmp2 = firstPiece(board);
  tmp3 = addPiece(tmp2, board);
  tmp4 = deadEnd(tmp3);
  scrut3 = tmp1 && tmp4;
  if (scrut3 === true) {
    lambda1 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    return NofibPrelude.lazy(lambda1)
  } else {
    tmp5 = singleDescend(board);
    singles = tmp5;
    tmp6 = NofibPrelude.listLen(singles);
    scrut = tmp6;
    scrut2 = scrut === 0;
    if (scrut2 === true) {
      tmp7 = descAndNo(board);
      tmp8 = quickSortIntChessSet(tmp7);
      tmp9 = NofibPrelude.map_lz(NofibPrelude.snd, tmp8);
    } else {
      scrut1 = scrut === 1;
      if (scrut1 === true) {
        if (singles instanceof NofibPrelude.Cons.class) {
          param0 = singles.head;
          param1 = singles.tail;
          h = param0;
          if (param1 instanceof NofibPrelude.Nil.class) {
            lambda2 = (undefined, function () {
              let tmp11, lambda4;
              lambda4 = (undefined, function () {
                return NofibPrelude.LzNil
              });
              tmp11 = NofibPrelude.lazy(lambda4);
              return NofibPrelude.LzCons(h, tmp11)
            });
            tmp10 = NofibPrelude.lazy(lambda2);
          } else {
            throw globalThis.Error("unreachable");
          }
        } else {
          throw globalThis.Error("unreachable");
        }
        tmp9 = tmp10;
      } else {
        lambda3 = (undefined, function () {
          return NofibPrelude.LzNil
        });
        tmp9 = NofibPrelude.lazy(lambda3);
      }
    }
    res = tmp9;
    return res
  }
};
showChessSet = function showChessSet(b) {
  let param0, param1, param2, param3, sze, n, f, ts, sortedTrail, tmp1, tmp2;
  if (b instanceof Board1.class) {
    param0 = b.a;
    param1 = b.b;
    param2 = b.c;
    param3 = b.d;
    sze = param0;
    n = param1;
    f = param2;
    ts = param3;
    tmp1 = assignMoveNo(ts, sze, n);
    tmp2 = quickSortIntInt(tmp1);
    sortedTrail = tmp2;
    return printBoard(sze, 1, sortedTrail)
  } else {
    throw new globalThis.Error("match error");
  }
};
root = function root(sze) {
  let lscomp1, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, lambda1;
  lscomp1 = function lscomp1(ls) {
    let lscomp2, param0, param1, h1, t1, tmp11, lambda2;
    if (ls instanceof NofibPrelude.Nil.class) {
      lambda2 = (undefined, function () {
        return NofibPrelude.LzNil
      });
      return NofibPrelude.lazy(lambda2)
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      h1 = param0;
      t1 = param1;
      lscomp2 = function lscomp2(ls1) {
        let param01, param11, h2, t2, lambda3;
        if (ls1 instanceof NofibPrelude.Nil.class) {
          return lscomp1(t1)
        } else if (ls1 instanceof NofibPrelude.Cons.class) {
          param01 = ls1.head;
          param11 = ls1.tail;
          h2 = param01;
          t2 = param11;
          lambda3 = (undefined, function () {
            let tmp12;
            tmp12 = lscomp2(t2);
            return NofibPrelude.LzCons([
              h1,
              h2
            ], tmp12)
          });
          return NofibPrelude.lazy(lambda3)
        } else {
          throw new globalThis.Error("match error");
        }
      };
      tmp11 = NofibPrelude.enumFromTo(1, sze);
      return lscomp2(tmp11)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp1 = sze * sze;
  tmp2 = 1 - tmp1;
  tmp3 = NofibPrelude.repeat(tmp2);
  tmp4 = NofibPrelude.enumFromTo(1, sze);
  tmp5 = lscomp1(tmp4);
  tmp6 = sze * sze;
  tmp7 = NofibPrelude.replicate_lz(tmp6, sze);
  tmp8 = NofibPrelude.zipWith_lz_lz(startTour, tmp5, tmp7);
  tmp9 = NofibPrelude.zip_lz_lz(tmp3, tmp8);
  lambda1 = (undefined, function () {
    return NofibPrelude.LzNil
  });
  tmp10 = NofibPrelude.lazy(lambda1);
  return NofibPrelude.append_lz_lz(tmp9, tmp10)
};
grow = function grow(x_y) {
  let first1, first0, x, y, tmp1, tmp2, tmp3;
  if (globalThis.Array.isArray(x_y) && x_y.length === 2) {
    first0 = x_y[0];
    first1 = x_y[1];
    x = first0;
    y = first1;
    tmp1 = x + 1;
    tmp2 = NofibPrelude.repeat(tmp1);
    tmp3 = descendents(y);
    return NofibPrelude.zip_lz_lz(tmp2, tmp3)
  } else {
    throw new globalThis.Error("match error");
  }
};
isFinished = function isFinished(x_y) {
  let first1, first0, x, y;
  if (globalThis.Array.isArray(x_y) && x_y.length === 2) {
    first0 = x_y[0];
    first1 = x_y[1];
    x = first0;
    y = first1;
    return tourFinished(y)
  } else {
    throw new globalThis.Error("match error");
  }
};
emptyQueue_lz = function emptyQueue_lz(x) {
  let scrut;
  scrut = NofibPrelude.force(x);
  if (scrut instanceof NofibPrelude.LzNil.class) {
    return true
  } else {
    return false
  }
};
removeFront_lz = function removeFront_lz(xs) {
  let scrut, param0, param1, h, t;
  scrut = NofibPrelude.force(xs);
  if (scrut instanceof NofibPrelude.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    h = param0;
    t = param1;
    return t
  } else {
    throw new globalThis.Error("match error");
  }
};
inquireFront_lz = function inquireFront_lz(h_t) {
  let scrut, param0, param1, h, t;
  scrut = NofibPrelude.force(h_t);
  if (scrut instanceof NofibPrelude.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    h = param0;
    t = param1;
    return h
  } else {
    throw new globalThis.Error("match error");
  }
};
addAllFront_lz = function addAllFront_lz(list, q) {
  return NofibPrelude.append_lz_lz(list, q)
};
depthSearch = function depthSearch(q, growFn, finFn) {
  let scrut, scrut1, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, lambda1, lambda2;
  scrut1 = emptyQueue_lz(q);
  if (scrut1 === true) {
    lambda1 = (undefined, function () {
      return NofibPrelude.LzNil
    });
    return NofibPrelude.lazy(lambda1)
  } else {
    tmp1 = inquireFront_lz(q);
    scrut = runtime.safeCall(finFn(tmp1));
    if (scrut === true) {
      lambda2 = (undefined, function () {
        let tmp7, tmp8, tmp9;
        tmp7 = inquireFront_lz(q);
        tmp8 = removeFront_lz(q);
        tmp9 = depthSearch(tmp8, growFn, finFn);
        return NofibPrelude.LzCons(tmp7, tmp9)
      });
      tmp2 = lambda2;
      return NofibPrelude.lazy(tmp2)
    } else {
      tmp3 = inquireFront_lz(q);
      tmp4 = runtime.safeCall(growFn(tmp3));
      tmp5 = removeFront_lz(q);
      tmp6 = addAllFront_lz(tmp4, tmp5);
      return depthSearch(tmp6, growFn, finFn)
    }
  }
};
printTour = function printTour(ss) {
  let pp, strToInt, scrut, param0, param1, size, param01, param11, number, tmp1, tmp2, tmp3, lambda1;
  strToInt = function strToInt(y, xs) {
    let param02, param12, x, xs1, tmp4, tmp5, tmp6, tmp7;
    if (xs instanceof NofibPrelude.Nil.class) {
      return y
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param02 = xs.head;
      param12 = xs.tail;
      x = param02;
      xs1 = param12;
      tmp4 = 10 * y;
      tmp5 = runtime.safeCall(x.codePointAt(0));
      tmp6 = tmp5 - 48;
      tmp7 = tmp4 + tmp6;
      return strToInt(tmp7, xs1)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  pp = function pp(xs) {
    let param02, param12, first1, first0, x, y, xs1, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12;
    if (xs instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param02 = xs.head;
      param12 = xs.tail;
      if (globalThis.Array.isArray(param02) && param02.length === 2) {
        first0 = param02[0];
        first1 = param02[1];
        x = first0;
        y = first1;
        xs1 = param12;
        tmp4 = NofibPrelude.nofibStringToList("\nKnights tour with ");
        tmp5 = NofibPrelude.stringOfInt(x);
        tmp6 = NofibPrelude.nofibStringToList(tmp5);
        tmp7 = NofibPrelude.nofibStringToList(" backtracking moves\n");
        tmp8 = showChessSet(y);
        tmp9 = pp(xs1);
        tmp10 = NofibPrelude.append(tmp8, tmp9);
        tmp11 = NofibPrelude.append(tmp7, tmp10);
        tmp12 = NofibPrelude.append(tmp6, tmp11);
        return NofibPrelude.append(tmp4, tmp12)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  lambda1 = (undefined, function (x) {
    return strToInt(0, x)
  });
  scrut = NofibPrelude.map(lambda1, ss);
  if (scrut instanceof NofibPrelude.Cons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    size = param0;
    if (param1 instanceof NofibPrelude.Cons.class) {
      param01 = param1.head;
      param11 = param1.tail;
      number = param01;
      if (param11 instanceof NofibPrelude.Nil.class) {
        tmp1 = root(size);
        tmp2 = depthSearch(tmp1, grow, isFinished);
        tmp3 = NofibPrelude.take_lz(number, tmp2);
        return pp(tmp3)
      } else {
        throw globalThis.Error("printTour error");
      }
    } else {
      throw globalThis.Error("printTour error");
    }
  } else {
    throw globalThis.Error("printTour error");
  }
};
testKnights_nofib = function testKnights_nofib(ss) {
  let argsOk, all_digits, usageString, scrut;
  all_digits = function all_digits(s) {
    let lambda1;
    lambda1 = (undefined, function (a, b) {
      let tmp1;
      tmp1 = myIsDigit(a);
      return tmp1 && b
    });
    return NofibPrelude.foldr(lambda1, true, s)
  };
  argsOk = function argsOk(ss1) {
    let tmp1, tmp2, tmp3, lambda1;
    tmp1 = NofibPrelude.listLen(ss1);
    tmp2 = tmp1 === 2;
    lambda1 = (undefined, function (a, b) {
      let tmp4;
      tmp4 = all_digits(a);
      return tmp4 && b
    });
    tmp3 = NofibPrelude.foldr(lambda1, true, ss1);
    return tmp2 && tmp3
  };
  usageString = "\nUsage: knights <board size> <no solutions> \n";
  scrut = argsOk(ss);
  if (scrut === true) {
    return printTour(ss)
  } else {
    throw globalThis.Error(usageString);
  }
};
createQueue = NofibPrelude.Nil;
Board1 = function Board(a1, b1, c1, d1) {
  return new Board.class(a1, b1, c1, d1);
};
Board1.class = class Board {
  constructor(a, b, c, d) {
    this.a = a;
    this.b = b;
    this.c = c;
    this.d = d;
  }
  toString() { return "Board(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.c) + ", " + globalThis.Predef.render(this.d) + ")"; }
};
Direction1 = class Direction {
  constructor() {}
  toString() { return "Direction"; }
};
const UL$class = class UL extends Direction1 {
  constructor() {
    super();
  }
  toString() { return "UL"; }
}; UL1 = new UL$class;
UL1.class = UL$class;
const UR$class = class UR extends Direction1 {
  constructor() {
    super();
  }
  toString() { return "UR"; }
}; UR1 = new UR$class;
UR1.class = UR$class;
const DL$class = class DL extends Direction1 {
  constructor() {
    super();
  }
  toString() { return "DL"; }
}; DL1 = new DL$class;
DL1.class = DL$class;
const DR$class = class DR extends Direction1 {
  constructor() {
    super();
  }
  toString() { return "DR"; }
}; DR1 = new DR$class;
DR1.class = DR$class;
const LU$class = class LU extends Direction1 {
  constructor() {
    super();
  }
  toString() { return "LU"; }
}; LU1 = new LU$class;
LU1.class = LU$class;
const LD$class = class LD extends Direction1 {
  constructor() {
    super();
  }
  toString() { return "LD"; }
}; LD1 = new LD$class;
LD1.class = LD$class;
const RU$class = class RU extends Direction1 {
  constructor() {
    super();
  }
  toString() { return "RU"; }
}; RU1 = new RU$class;
RU1.class = RU$class;
const RD$class = class RD extends Direction1 {
  constructor() {
    super();
  }
  toString() { return "RD"; }
}; RD1 = new RD$class;
RD1.class = RD$class;
lambda = (undefined, function () {
  let tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
  tmp1 = NofibPrelude.nofibStringToList("8");
  tmp2 = NofibPrelude.nofibStringToList("1");
  tmp3 = NofibPrelude.Cons(tmp2, NofibPrelude.Nil);
  tmp4 = NofibPrelude.Cons(tmp1, tmp3);
  tmp5 = testKnights_nofib(tmp4);
  tmp6 = NofibPrelude.nofibListToString(tmp5);
  return BenchmarkPrelude.print(tmp6)
});
tmp = lambda;
BenchmarkPrelude.benchmark(tmp)