import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let lscomp2, lscomp1, best_, board, minimax1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda$, lscomp2$, lambda$1, lambda$2, lambda$3, lambda$4, best_$, lambda$5, lambda$6, lambda$7, lambda$8, board$;
board$ = function board$(testBoard, x) {
  let scrut;
  scrut = x === "doesn't happen";
  if (scrut === true) {
    return NofibPrelude.append(testBoard, testBoard)
  } else {
    return testBoard
  }
};
board = function board(testBoard) {
  return (x) => {
    return board$(testBoard, x)
  }
};
lambda$8 = function lambda$(f, g, opposition, x) {
  return minimax1.bestMove(opposition, g, f, x)
};
lambda10 = (undefined, function (f, g, opposition) {
  return (x) => {
    return lambda$8(f, g, opposition, x)
  }
});
lambda$7 = function lambda$(p, x) {
  return minimax1.newPositions(p, x)
};
lambda8 = (undefined, function (p) {
  return (x) => {
    return lambda$7(p, x)
  }
});
lambda$6 = function lambda$(p, x) {
  let tmp;
  tmp = minimax1.opposite(p);
  return minimax1.newPositions(tmp, x)
};
lambda9 = (undefined, function (p) {
  return (x) => {
    return lambda$6(p, x)
  }
});
lambda$5 = function lambda$(f, g, x) {
  return minimax1.mise(g, f, x)
};
lambda7 = (undefined, function (f, g) {
  return (x) => {
    return lambda$5(f, g, x)
  }
});
best_$ = function best_$(f, b, s, ls1, ls2) {
  let param0, param1, b_, bs, param01, param11, s_, ss, scrut, tmp;
  if (ls1 instanceof NofibPrelude.Nil.class) {
    if (ls2 instanceof NofibPrelude.Nil.class) {
      return [
        b,
        s
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else if (ls1 instanceof NofibPrelude.Cons.class) {
    param0 = ls1.head;
    param1 = ls1.tail;
    b_ = param0;
    bs = param1;
    if (ls2 instanceof NofibPrelude.Cons.class) {
      param01 = ls2.head;
      param11 = ls2.tail;
      s_ = param01;
      ss = param11;
      tmp = runtime.safeCall(f(s, s_));
      scrut = minimax1.evaluationEq(s, tmp);
      if (scrut === true) {
        return best_$(f, b, s, bs, ss)
      } else {
        return best_$(f, b_, s_, bs, ss)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
best_ = function best_(f) {
  return (b, s, ls1, ls2) => {
    return best_$(f, b, s, ls1, ls2)
  }
};
lambda$4 = function lambda$(n, x) {
  let tmp;
  tmp = n - 1;
  return minimax1.prune(tmp, x)
};
lambda6 = (undefined, function (n) {
  return (x) => {
    return lambda$4(n, x)
  }
});
lambda$3 = function lambda$(f, x) {
  return minimax1.mapTree(f, x)
};
lambda5 = (undefined, function (f) {
  return (x) => {
    return lambda$3(f, x)
  }
});
lambda$2 = function lambda$(f, g, x) {
  return minimax1.repTree(g, f, x)
};
lambda4 = (undefined, function (f, g) {
  return (x) => {
    return lambda$2(f, g, x)
  }
});
lambda$1 = function lambda$(board1, x) {
  return minimax1.score(board1, x)
};
lambda3 = (undefined, function (board1) {
  return (x) => {
    return lambda$1(board1, x)
  }
});
lambda2 = (undefined, function (x, y) {
  return minimax1.map2(minimax1.scorePiece, x, y)
});
lscomp2$ = function lscomp2$(x, xs, ls) {
  let param0, param1, y, ys, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return lscomp1(xs)
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    y = param0;
    ys = param1;
    tmp = lscomp2$(x, xs, ys);
    return NofibPrelude.Cons([
      x,
      y
    ], tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp2 = function lscomp2(x, xs) {
  return (ls) => {
    return lscomp2$(x, xs, ls)
  }
};
lscomp1 = function lscomp1(ls) {
  let param0, param1, x, xs, tmp, tmp1, tmp2;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    x = param0;
    xs = param1;
    tmp = NofibPrelude.Cons(3, NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons(2, tmp);
    tmp2 = NofibPrelude.Cons(1, tmp1);
    return lscomp2$(x, xs, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$ = function lambda$(piece, board1, pos) {
  return minimax1.placePiece(piece, board1, pos)
};
lambda1 = (undefined, function (piece, board1) {
  return (pos) => {
    return lambda$(piece, board1, pos)
  }
});
lambda = (undefined, function (x) {
  let tmp;
  tmp = minimax1.eqPiece(x, minimax1.Empty);
  return BenchmarkPrelude.not(tmp)
});
minimax1 = class minimax {
  static {
    minimax1 = minimax;
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75, tmp76, tmp77, tmp78, tmp79, tmp80, tmp81, tmp82, tmp83, tmp84, tmp85, tmp86, tmp87, tmp88, tmp89, tmp90, tmp91, tmp92, tmp93, tmp94, tmp95, tmp96, tmp97, tmp98, tmp99, tmp100, tmp101, tmp102, tmp103, tmp104, tmp105, tmp106, lambda11;
    this.Piece = class Piece {
      constructor() {}
      toString() { return "Piece"; }
    };
    const X$class = class X extends minimax.Piece {
      constructor() {
        super();
      }
      toString() { return "X"; }
    };
    this.X = new X$class;
    this.X.class = X$class;
    const O$class = class O extends minimax.Piece {
      constructor() {
        super();
      }
      toString() { return "O"; }
    };
    this.O = new O$class;
    this.O.class = O$class;
    const Empty$class = class Empty extends minimax.Piece {
      constructor() {
        super();
      }
      toString() { return "Empty"; }
    };
    this.Empty = new Empty$class;
    this.Empty.class = Empty$class;
    this.Evaluation = class Evaluation {
      constructor() {}
      toString() { return "Evaluation"; }
    };
    const XWin$class = class XWin extends minimax.Evaluation {
      constructor() {
        super();
      }
      toString() { return "XWin"; }
    };
    this.XWin = new XWin$class;
    this.XWin.class = XWin$class;
    const OWin$class = class OWin extends minimax.Evaluation {
      constructor() {
        super();
      }
      toString() { return "OWin"; }
    };
    this.OWin = new OWin$class;
    this.OWin.class = OWin$class;
    this.Score = function Score(i1) {
      return new Score.class(i1);
    };
    this.Score.class = class Score extends minimax.Evaluation {
      constructor(i) {
        super();
        this.i = i;
      }
      toString() { return "Score(" + globalThis.Predef.render(this.i) + ")"; }
    };
    this.Branch = function Branch(a1, cs1) {
      return new Branch.class(a1, cs1);
    };
    this.Branch.class = class Branch {
      constructor(a, cs) {
        this.a = a;
        this.cs = cs;
      }
      toString() { return "Branch(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.cs) + ")"; }
    };
    tmp = NofibPrelude.Cons(1, NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons(1, tmp);
    tmp2 = NofibPrelude.Cons(1, tmp1);
    tmp3 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp4 = NofibPrelude.Cons(0, tmp3);
    tmp5 = NofibPrelude.Cons(0, tmp4);
    tmp6 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp7 = NofibPrelude.Cons(0, tmp6);
    tmp8 = NofibPrelude.Cons(0, tmp7);
    tmp9 = NofibPrelude.Cons(tmp8, NofibPrelude.Nil);
    tmp10 = NofibPrelude.Cons(tmp5, tmp9);
    tmp11 = NofibPrelude.Cons(tmp2, tmp10);
    this.win1 = tmp11;
    tmp12 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp13 = NofibPrelude.Cons(0, tmp12);
    tmp14 = NofibPrelude.Cons(0, tmp13);
    tmp15 = NofibPrelude.Cons(1, NofibPrelude.Nil);
    tmp16 = NofibPrelude.Cons(1, tmp15);
    tmp17 = NofibPrelude.Cons(1, tmp16);
    tmp18 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp19 = NofibPrelude.Cons(0, tmp18);
    tmp20 = NofibPrelude.Cons(0, tmp19);
    tmp21 = NofibPrelude.Cons(tmp20, NofibPrelude.Nil);
    tmp22 = NofibPrelude.Cons(tmp17, tmp21);
    tmp23 = NofibPrelude.Cons(tmp14, tmp22);
    this.win2 = tmp23;
    tmp24 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp25 = NofibPrelude.Cons(0, tmp24);
    tmp26 = NofibPrelude.Cons(0, tmp25);
    tmp27 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp28 = NofibPrelude.Cons(0, tmp27);
    tmp29 = NofibPrelude.Cons(0, tmp28);
    tmp30 = NofibPrelude.Cons(1, NofibPrelude.Nil);
    tmp31 = NofibPrelude.Cons(1, tmp30);
    tmp32 = NofibPrelude.Cons(1, tmp31);
    tmp33 = NofibPrelude.Cons(tmp32, NofibPrelude.Nil);
    tmp34 = NofibPrelude.Cons(tmp29, tmp33);
    tmp35 = NofibPrelude.Cons(tmp26, tmp34);
    this.win3 = tmp35;
    tmp36 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp37 = NofibPrelude.Cons(0, tmp36);
    tmp38 = NofibPrelude.Cons(1, tmp37);
    tmp39 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp40 = NofibPrelude.Cons(0, tmp39);
    tmp41 = NofibPrelude.Cons(1, tmp40);
    tmp42 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp43 = NofibPrelude.Cons(0, tmp42);
    tmp44 = NofibPrelude.Cons(1, tmp43);
    tmp45 = NofibPrelude.Cons(tmp44, NofibPrelude.Nil);
    tmp46 = NofibPrelude.Cons(tmp41, tmp45);
    tmp47 = NofibPrelude.Cons(tmp38, tmp46);
    this.win4 = tmp47;
    tmp48 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp49 = NofibPrelude.Cons(1, tmp48);
    tmp50 = NofibPrelude.Cons(0, tmp49);
    tmp51 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp52 = NofibPrelude.Cons(1, tmp51);
    tmp53 = NofibPrelude.Cons(0, tmp52);
    tmp54 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp55 = NofibPrelude.Cons(1, tmp54);
    tmp56 = NofibPrelude.Cons(0, tmp55);
    tmp57 = NofibPrelude.Cons(tmp56, NofibPrelude.Nil);
    tmp58 = NofibPrelude.Cons(tmp53, tmp57);
    tmp59 = NofibPrelude.Cons(tmp50, tmp58);
    this.win5 = tmp59;
    tmp60 = NofibPrelude.Cons(1, NofibPrelude.Nil);
    tmp61 = NofibPrelude.Cons(0, tmp60);
    tmp62 = NofibPrelude.Cons(0, tmp61);
    tmp63 = NofibPrelude.Cons(1, NofibPrelude.Nil);
    tmp64 = NofibPrelude.Cons(0, tmp63);
    tmp65 = NofibPrelude.Cons(0, tmp64);
    tmp66 = NofibPrelude.Cons(1, NofibPrelude.Nil);
    tmp67 = NofibPrelude.Cons(0, tmp66);
    tmp68 = NofibPrelude.Cons(0, tmp67);
    tmp69 = NofibPrelude.Cons(tmp68, NofibPrelude.Nil);
    tmp70 = NofibPrelude.Cons(tmp65, tmp69);
    tmp71 = NofibPrelude.Cons(tmp62, tmp70);
    this.win6 = tmp71;
    tmp72 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp73 = NofibPrelude.Cons(0, tmp72);
    tmp74 = NofibPrelude.Cons(1, tmp73);
    tmp75 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp76 = NofibPrelude.Cons(1, tmp75);
    tmp77 = NofibPrelude.Cons(0, tmp76);
    tmp78 = NofibPrelude.Cons(1, NofibPrelude.Nil);
    tmp79 = NofibPrelude.Cons(0, tmp78);
    tmp80 = NofibPrelude.Cons(0, tmp79);
    tmp81 = NofibPrelude.Cons(tmp80, NofibPrelude.Nil);
    tmp82 = NofibPrelude.Cons(tmp77, tmp81);
    tmp83 = NofibPrelude.Cons(tmp74, tmp82);
    this.win7 = tmp83;
    tmp84 = NofibPrelude.Cons(1, NofibPrelude.Nil);
    tmp85 = NofibPrelude.Cons(0, tmp84);
    tmp86 = NofibPrelude.Cons(0, tmp85);
    tmp87 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp88 = NofibPrelude.Cons(1, tmp87);
    tmp89 = NofibPrelude.Cons(0, tmp88);
    tmp90 = NofibPrelude.Cons(0, NofibPrelude.Nil);
    tmp91 = NofibPrelude.Cons(0, tmp90);
    tmp92 = NofibPrelude.Cons(1, tmp91);
    tmp93 = NofibPrelude.Cons(tmp92, NofibPrelude.Nil);
    tmp94 = NofibPrelude.Cons(tmp89, tmp93);
    tmp95 = NofibPrelude.Cons(tmp86, tmp94);
    this.win8 = tmp95;
    tmp96 = NofibPrelude.Cons(minimax.win8, NofibPrelude.Nil);
    tmp97 = NofibPrelude.Cons(minimax.win7, tmp96);
    tmp98 = NofibPrelude.Cons(minimax.win6, tmp97);
    tmp99 = NofibPrelude.Cons(minimax.win5, tmp98);
    tmp100 = NofibPrelude.Cons(minimax.win4, tmp99);
    tmp101 = NofibPrelude.Cons(minimax.win3, tmp100);
    tmp102 = NofibPrelude.Cons(minimax.win2, tmp101);
    tmp103 = NofibPrelude.Cons(minimax.win1, tmp102);
    this.wins = tmp103;
    tmp104 = NofibPrelude.replicate(3, minimax.Empty);
    tmp105 = NofibPrelude.replicate(3, tmp104);
    this.initialBoard = tmp105;
    lambda11 = (undefined, function () {
      let tmp107, tmp108;
      tmp107 = minimax.prog("180000");
      tmp108 = NofibPrelude.nofibListToString(tmp107);
      return BenchmarkPrelude.print(tmp108)
    });
    tmp106 = lambda11;
    BenchmarkPrelude.benchmark(tmp106)
  }
  static andd(ls) {
    let param0, param1, b, bs, tmp;
    if (ls instanceof NofibPrelude.Nil.class) {
      return true
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      b = param0;
      bs = param1;
      tmp = minimax.andd(bs);
      return b && tmp
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static eqPiece(p1, p2) {
    if (p1 instanceof minimax.X.class) {
      if (p2 instanceof minimax.X.class) {
        return true
      } else {
        return false
      }
    } else if (p1 instanceof minimax.O.class) {
      if (p2 instanceof minimax.O.class) {
        return true
      } else {
        return false
      }
    } else if (p1 instanceof minimax.Empty.class) {
      if (p2 instanceof minimax.Empty.class) {
        return true
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static evaluationEq(x, y) {
    let param0, i, param01, j, scrut;
    if (x instanceof minimax.XWin.class) {
      if (y instanceof minimax.XWin.class) {
        return true
      } else {
        return false
      }
    } else if (x instanceof minimax.OWin.class) {
      if (y instanceof minimax.OWin.class) {
        return true
      } else {
        return false
      }
    } else if (x instanceof minimax.Score.class) {
      param0 = x.i;
      i = param0;
      if (y instanceof minimax.Score.class) {
        param01 = y.i;
        j = param01;
        scrut = i === j;
        if (scrut === true) {
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
  } 
  static showEvaluation(e) {
    let param0, i, tmp, tmp1, tmp2;
    if (e instanceof minimax.XWin.class) {
      return NofibPrelude.nofibStringToList("XWin")
    } else if (e instanceof minimax.OWin.class) {
      return NofibPrelude.nofibStringToList("OWin")
    } else if (e instanceof minimax.Score.class) {
      param0 = e.i;
      i = param0;
      tmp = NofibPrelude.nofibStringToList("Score ");
      tmp1 = NofibPrelude.stringOfInt(i);
      tmp2 = NofibPrelude.nofibStringToList(tmp1);
      return NofibPrelude.append(tmp, tmp2)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static showPiece(p) {
    if (p instanceof minimax.X.class) {
      return NofibPrelude.nofibStringToList("X")
    } else if (p instanceof minimax.O.class) {
      return NofibPrelude.nofibStringToList("O")
    } else if (p instanceof minimax.Empty.class) {
      return NofibPrelude.nofibStringToList(" ")
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static showRow(ps) {
    let param0, param1, p11, param01, param11, p21, param02, param12, p3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    if (ps instanceof NofibPrelude.Cons.class) {
      param0 = ps.head;
      param1 = ps.tail;
      p11 = param0;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        p21 = param01;
        if (param11 instanceof NofibPrelude.Cons.class) {
          param02 = param11.head;
          param12 = param11.tail;
          p3 = param02;
          if (param12 instanceof NofibPrelude.Nil.class) {
            tmp = minimax.showPiece(p11);
            tmp1 = NofibPrelude.nofibStringToList("|");
            tmp2 = minimax.showPiece(p21);
            tmp3 = NofibPrelude.nofibStringToList("|");
            tmp4 = minimax.showPiece(p3);
            tmp5 = NofibPrelude.append(tmp3, tmp4);
            tmp6 = NofibPrelude.append(tmp2, tmp5);
            tmp7 = NofibPrelude.append(tmp1, tmp6);
            return NofibPrelude.append(tmp, tmp7)
          } else {
            throw new globalThis.Error("match error");
          }
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
  static showBoard(rs) {
    let param0, param1, r1, param01, param11, r2, param02, param12, r3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    if (rs instanceof NofibPrelude.Cons.class) {
      param0 = rs.head;
      param1 = rs.tail;
      r1 = param0;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        r2 = param01;
        if (param11 instanceof NofibPrelude.Cons.class) {
          param02 = param11.head;
          param12 = param11.tail;
          r3 = param02;
          if (param12 instanceof NofibPrelude.Nil.class) {
            tmp = minimax.showRow(r1);
            tmp1 = NofibPrelude.nofibStringToList("\n------\n");
            tmp2 = minimax.showRow(r2);
            tmp3 = NofibPrelude.nofibStringToList("\n------\n");
            tmp4 = minimax.showRow(r3);
            tmp5 = NofibPrelude.nofibStringToList("\n\n");
            tmp6 = NofibPrelude.append(tmp4, tmp5);
            tmp7 = NofibPrelude.append(tmp3, tmp6);
            tmp8 = NofibPrelude.append(tmp2, tmp7);
            tmp9 = NofibPrelude.append(tmp1, tmp8);
            return NofibPrelude.append(tmp, tmp9)
          } else {
            throw new globalThis.Error("match error");
          }
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
  static insert(p3, ps1, i) {
    let param0, param1, p11, param01, param11, p21, param02, param12, p31, scrut, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    if (ps1 instanceof NofibPrelude.Cons.class) {
      param0 = ps1.head;
      param1 = ps1.tail;
      p11 = param0;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        p21 = param01;
        if (param11 instanceof NofibPrelude.Cons.class) {
          param02 = param11.head;
          param12 = param11.tail;
          p31 = param02;
          if (param12 instanceof NofibPrelude.Nil.class) {
            scrut2 = i === 1;
            if (scrut2 === true) {
              tmp = NofibPrelude.Cons(p31, NofibPrelude.Nil);
              tmp1 = NofibPrelude.Cons(p21, tmp);
              return NofibPrelude.Cons(p3, tmp1)
            } else {
              scrut1 = i === 2;
              if (scrut1 === true) {
                tmp2 = NofibPrelude.Cons(p31, NofibPrelude.Nil);
                tmp3 = NofibPrelude.Cons(p3, tmp2);
                return NofibPrelude.Cons(p11, tmp3)
              } else {
                scrut = i === 3;
                if (scrut === true) {
                  tmp4 = NofibPrelude.Cons(p3, NofibPrelude.Nil);
                  tmp5 = NofibPrelude.Cons(p21, tmp4);
                  return NofibPrelude.Cons(p11, tmp5)
                } else {
                  throw new globalThis.Error("match error");
                }
              }
            }
          } else {
            throw new globalThis.Error("match error");
          }
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
  static empty_(x1, r) {
    let scrut, param0, param1, param01, param11, param02, param12, scrut1, scrut2;
    scrut2 = x1 === 1;
    if (scrut2 === true) {
      if (r instanceof NofibPrelude.Cons.class) {
        param0 = r.head;
        param1 = r.tail;
        if (param0 instanceof minimax.Empty.class) {
          if (param1 instanceof NofibPrelude.Cons.class) {
            param01 = param1.head;
            param11 = param1.tail;
            if (param11 instanceof NofibPrelude.Cons.class) {
              param02 = param11.head;
              param12 = param11.tail;
              if (param12 instanceof NofibPrelude.Nil.class) {
                return true
              } else {
                scrut1 = x1 === 2;
                if (scrut1 === true) {
                  if (param01 instanceof minimax.Empty.class) {
                    scrut = x1 === 3;
                    if (scrut === true) {
                      if (param02 instanceof minimax.Empty.class) {
                        return false
                      } else {
                        return false
                      }
                    } else {
                      return false
                    }
                  } else {
                    scrut = x1 === 3;
                    if (scrut === true) {
                      if (param02 instanceof minimax.Empty.class) {
                        return false
                      } else {
                        return false
                      }
                    } else {
                      return false
                    }
                  }
                } else {
                  scrut = x1 === 3;
                  if (scrut === true) {
                    if (param02 instanceof minimax.Empty.class) {
                      return false
                    } else {
                      return false
                    }
                  } else {
                    return false
                  }
                }
              }
            } else {
              scrut1 = x1 === 2;
              if (scrut1 === true) {
                if (param01 instanceof minimax.Empty.class) {
                  scrut = x1 === 3;
                  if (scrut === true) {
                    return false
                  } else {
                    return false
                  }
                } else {
                  scrut = x1 === 3;
                  if (scrut === true) {
                    return false
                  } else {
                    return false
                  }
                }
              } else {
                scrut = x1 === 3;
                if (scrut === true) {
                  return false
                } else {
                  return false
                }
              }
            }
          } else {
            scrut1 = x1 === 2;
            if (scrut1 === true) {
              scrut = x1 === 3;
              if (scrut === true) {
                return false
              } else {
                return false
              }
            } else {
              scrut = x1 === 3;
              if (scrut === true) {
                return false
              } else {
                return false
              }
            }
          }
        } else {
          scrut1 = x1 === 2;
          if (scrut1 === true) {
            if (param1 instanceof NofibPrelude.Cons.class) {
              param01 = param1.head;
              param11 = param1.tail;
              if (param01 instanceof minimax.Empty.class) {
                if (param11 instanceof NofibPrelude.Cons.class) {
                  param02 = param11.head;
                  param12 = param11.tail;
                  if (param12 instanceof NofibPrelude.Nil.class) {
                    return true
                  } else {
                    scrut = x1 === 3;
                    if (scrut === true) {
                      if (param02 instanceof minimax.Empty.class) {
                        return false
                      } else {
                        return false
                      }
                    } else {
                      return false
                    }
                  }
                } else {
                  scrut = x1 === 3;
                  if (scrut === true) {
                    return false
                  } else {
                    return false
                  }
                }
              } else {
                scrut = x1 === 3;
                if (scrut === true) {
                  if (param11 instanceof NofibPrelude.Cons.class) {
                    param02 = param11.head;
                    param12 = param11.tail;
                    if (param02 instanceof minimax.Empty.class) {
                      if (param12 instanceof NofibPrelude.Nil.class) {
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
                } else {
                  return false
                }
              }
            } else {
              scrut = x1 === 3;
              if (scrut === true) {
                return false
              } else {
                return false
              }
            }
          } else {
            scrut = x1 === 3;
            if (scrut === true) {
              if (param1 instanceof NofibPrelude.Cons.class) {
                param01 = param1.head;
                param11 = param1.tail;
                if (param11 instanceof NofibPrelude.Cons.class) {
                  param02 = param11.head;
                  param12 = param11.tail;
                  if (param02 instanceof minimax.Empty.class) {
                    if (param12 instanceof NofibPrelude.Nil.class) {
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
              } else {
                return false
              }
            } else {
              return false
            }
          }
        }
      } else {
        scrut1 = x1 === 2;
        if (scrut1 === true) {
          scrut = x1 === 3;
          if (scrut === true) {
            return false
          } else {
            return false
          }
        } else {
          scrut = x1 === 3;
          if (scrut === true) {
            return false
          } else {
            return false
          }
        }
      }
    } else {
      scrut1 = x1 === 2;
      if (scrut1 === true) {
        if (r instanceof NofibPrelude.Cons.class) {
          param0 = r.head;
          param1 = r.tail;
          if (param1 instanceof NofibPrelude.Cons.class) {
            param01 = param1.head;
            param11 = param1.tail;
            if (param01 instanceof minimax.Empty.class) {
              if (param11 instanceof NofibPrelude.Cons.class) {
                param02 = param11.head;
                param12 = param11.tail;
                if (param12 instanceof NofibPrelude.Nil.class) {
                  return true
                } else {
                  scrut = x1 === 3;
                  if (scrut === true) {
                    if (param02 instanceof minimax.Empty.class) {
                      return false
                    } else {
                      return false
                    }
                  } else {
                    return false
                  }
                }
              } else {
                scrut = x1 === 3;
                if (scrut === true) {
                  return false
                } else {
                  return false
                }
              }
            } else {
              scrut = x1 === 3;
              if (scrut === true) {
                if (param11 instanceof NofibPrelude.Cons.class) {
                  param02 = param11.head;
                  param12 = param11.tail;
                  if (param02 instanceof minimax.Empty.class) {
                    if (param12 instanceof NofibPrelude.Nil.class) {
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
              } else {
                return false
              }
            }
          } else {
            scrut = x1 === 3;
            if (scrut === true) {
              return false
            } else {
              return false
            }
          }
        } else {
          scrut = x1 === 3;
          if (scrut === true) {
            return false
          } else {
            return false
          }
        }
      } else {
        scrut = x1 === 3;
        if (scrut === true) {
          if (r instanceof NofibPrelude.Cons.class) {
            param0 = r.head;
            param1 = r.tail;
            if (param1 instanceof NofibPrelude.Cons.class) {
              param01 = param1.head;
              param11 = param1.tail;
              if (param11 instanceof NofibPrelude.Cons.class) {
                param02 = param11.head;
                param12 = param11.tail;
                if (param02 instanceof minimax.Empty.class) {
                  if (param12 instanceof NofibPrelude.Nil.class) {
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
            } else {
              return false
            }
          } else {
            return false
          }
        } else {
          return false
        }
      }
    }
  } 
  static empty(pos, board1) {
    let param0, param1, r1, param01, param11, r2, param02, param12, r3, first1, first0, x2, x3, x4;
    if (board1 instanceof NofibPrelude.Cons.class) {
      param0 = board1.head;
      param1 = board1.tail;
      r1 = param0;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        r2 = param01;
        if (param11 instanceof NofibPrelude.Cons.class) {
          param02 = param11.head;
          param12 = param11.tail;
          r3 = param02;
          if (param12 instanceof NofibPrelude.Nil.class) {
            if (globalThis.Array.isArray(pos) && pos.length === 2) {
              first0 = pos[0];
              first1 = pos[1];
              if (first0 === 1) {
                x4 = first1;
                return minimax.empty_(x4, r1)
              } else if (first0 === 2) {
                x3 = first1;
                return minimax.empty_(x3, r2)
              } else if (first0 === 3) {
                x2 = first1;
                return minimax.empty_(x2, r3)
              } else {
                throw new globalThis.Error("match error");
              }
            } else {
              throw new globalThis.Error("match error");
            }
          } else {
            throw new globalThis.Error("match error");
          }
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
  static placePiece(p4, board2, pos1) {
    let param0, param1, r1, param01, param11, r2, param02, param12, r3, first1, first0, x2, x3, x4, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12;
    tmp = minimax.empty(pos1, board2);
    scrut = BenchmarkPrelude.not(tmp);
    if (scrut === true) {
      return NofibPrelude.Nil
    } else {
      if (board2 instanceof NofibPrelude.Cons.class) {
        param0 = board2.head;
        param1 = board2.tail;
        r1 = param0;
        if (param1 instanceof NofibPrelude.Cons.class) {
          param01 = param1.head;
          param11 = param1.tail;
          r2 = param01;
          if (param11 instanceof NofibPrelude.Cons.class) {
            param02 = param11.head;
            param12 = param11.tail;
            r3 = param02;
            if (param12 instanceof NofibPrelude.Nil.class) {
              if (globalThis.Array.isArray(pos1) && pos1.length === 2) {
                first0 = pos1[0];
                first1 = pos1[1];
                if (first0 === 1) {
                  x4 = first1;
                  tmp1 = minimax.insert(p4, r1, x4);
                  tmp2 = NofibPrelude.Cons(r3, NofibPrelude.Nil);
                  tmp3 = NofibPrelude.Cons(r2, tmp2);
                  tmp4 = NofibPrelude.Cons(tmp1, tmp3);
                  return NofibPrelude.Cons(tmp4, NofibPrelude.Nil)
                } else if (first0 === 2) {
                  x3 = first1;
                  tmp5 = minimax.insert(p4, r2, x3);
                  tmp6 = NofibPrelude.Cons(r3, NofibPrelude.Nil);
                  tmp7 = NofibPrelude.Cons(tmp5, tmp6);
                  tmp8 = NofibPrelude.Cons(r1, tmp7);
                  return NofibPrelude.Cons(tmp8, NofibPrelude.Nil)
                } else if (first0 === 3) {
                  x2 = first1;
                  tmp9 = minimax.insert(p4, r3, x2);
                  tmp10 = NofibPrelude.Cons(tmp9, NofibPrelude.Nil);
                  tmp11 = NofibPrelude.Cons(r2, tmp10);
                  tmp12 = NofibPrelude.Cons(r1, tmp11);
                  return NofibPrelude.Cons(tmp12, NofibPrelude.Nil)
                } else {
                  throw new globalThis.Error("match error");
                }
              } else {
                throw new globalThis.Error("match error");
              }
            } else {
              throw new globalThis.Error("match error");
            }
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
  } 
  static fullBoard(b) {
    let tmp, tmp1;
    tmp = NofibPrelude.concat(b);
    tmp1 = NofibPrelude.map(lambda, tmp);
    return minimax.andd(tmp1)
  } 
  static newPositions(piece, board3) {
    let tmp, tmp1, tmp2, tmp3, tmp4, lambda$this;
    tmp = NofibPrelude.Cons(3, NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons(2, tmp);
    tmp2 = NofibPrelude.Cons(1, tmp1);
    tmp3 = lscomp1(tmp2);
    lambda$this = runtime.safeCall(lambda1(piece, board3));
    tmp4 = NofibPrelude.map(lambda$this, tmp3);
    return NofibPrelude.concat(tmp4)
  } 
  static eval(x2) {
    let scrut, scrut1, tmp;
    scrut1 = x2 === 3;
    if (scrut1 === true) {
      return minimax.XWin
    } else {
      tmp = - 3;
      scrut = x2 === tmp;
      if (scrut === true) {
        return minimax.OWin
      } else {
        return minimax.Score(x2)
      }
    }
  } 
  static interpret(x3, l) {
    let param0, param1, param01, y1, ls1, tmp;
    if (l instanceof NofibPrelude.Nil.class) {
      return minimax.Score(x3)
    } else if (l instanceof NofibPrelude.Cons.class) {
      param0 = l.head;
      param1 = l.tail;
      if (param0 instanceof minimax.Score.class) {
        param01 = param0.i;
        y1 = param01;
        ls1 = param1;
        tmp = x3 + y1;
        return minimax.interpret(tmp, ls1)
      } else if (param0 instanceof minimax.XWin.class) {
        return minimax.XWin
      } else if (param0 instanceof minimax.OWin.class) {
        return minimax.OWin
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static scorePiece(p5, score) {
    if (p5 instanceof minimax.X.class) {
      return score
    } else if (p5 instanceof minimax.Empty.class) {
      return 0
    } else if (p5 instanceof minimax.O.class) {
      return - score
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static map2(f, xs, ys) {
    let param0, param1, x4, xs1, scrut, param01, param11, y1, ys1, tmp, tmp1;
    if (xs instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param0 = xs.head;
      param1 = xs.tail;
      x4 = param0;
      xs1 = param1;
      if (ys instanceof NofibPrelude.Cons.class) {
        param01 = ys.head;
        param11 = ys.tail;
        y1 = param01;
        ys1 = param11;
        tmp = runtime.safeCall(f(x4, y1));
        tmp1 = minimax.map2(f, xs1, ys1);
        return NofibPrelude.Cons(tmp, tmp1)
      } else {
        scrut = NofibPrelude.Nil;
        if (scrut === true) {
          return NofibPrelude.Nil
        } else {
          throw new globalThis.Error("match error");
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static score(board4, win) {
    let tmp, tmp1, tmp2;
    tmp = minimax.map2(lambda2, board4, win);
    tmp1 = NofibPrelude.map(NofibPrelude.sum, tmp);
    tmp2 = NofibPrelude.sum(tmp1);
    return minimax.eval(tmp2)
  } 
  static static(board5) {
    let tmp, lambda$this;
    lambda$this = runtime.safeCall(lambda3(board5));
    tmp = NofibPrelude.map(lambda$this, minimax.wins);
    return minimax.interpret(0, tmp)
  } 
  static repTree(f1, g, a) {
    let tmp, tmp1, lambda$this;
    tmp = runtime.safeCall(f1(a));
    lambda$this = runtime.safeCall(lambda4(f1, g));
    tmp1 = NofibPrelude.map(lambda$this, tmp);
    return minimax.Branch(a, tmp1)
  } 
  static mapTree(f2, t) {
    let param0, param1, a1, l1, tmp, tmp1, lambda$this;
    if (t instanceof minimax.Branch.class) {
      param0 = t.a;
      param1 = t.cs;
      a1 = param0;
      l1 = param1;
      tmp = runtime.safeCall(f2(a1));
      lambda$this = runtime.safeCall(lambda5(f2));
      tmp1 = NofibPrelude.map(lambda$this, l1);
      return minimax.Branch(tmp, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static prune(n, t1) {
    let param0, param1, a1, l1, scrut, scrut1, tmp, lambda$this;
    if (t1 instanceof minimax.Branch.class) {
      param0 = t1.a;
      param1 = t1.cs;
      a1 = param0;
      l1 = param1;
      scrut1 = n === 0;
      if (scrut1 === true) {
        return minimax.Branch(a1, NofibPrelude.Nil)
      } else {
        scrut = n < 0;
        if (scrut === true) {
          throw globalThis.Error("Tree.prune: < 0");
        } else {
          lambda$this = runtime.safeCall(lambda6(n));
          tmp = NofibPrelude.map(lambda$this, l1);
          return minimax.Branch(a1, tmp)
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static opposite(p6) {
    if (p6 instanceof minimax.X.class) {
      return minimax.O
    } else if (p6 instanceof minimax.O.class) {
      return minimax.X
    } else {
      throw globalThis.Error("opposite");
    }
  } 
  static best(f3, bs, ss) {
    let param0, param1, b1, bs1, param01, param11, s, ss1;
    if (bs instanceof NofibPrelude.Cons.class) {
      param0 = bs.head;
      param1 = bs.tail;
      b1 = param0;
      bs1 = param1;
      if (ss instanceof NofibPrelude.Cons.class) {
        param01 = ss.head;
        param11 = ss.tail;
        s = param01;
        ss1 = param11;
        return best_$(f3, b1, s, bs1, ss1)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static showMove(m) {
    let first1, first0, b1, e1, tmp, tmp1, tmp2, tmp3;
    if (globalThis.Array.isArray(m) && m.length === 2) {
      first0 = m[0];
      first1 = m[1];
      b1 = first0;
      e1 = first1;
      tmp = minimax.showEvaluation(e1);
      tmp1 = NofibPrelude.nofibStringToList("\n");
      tmp2 = minimax.showBoard(b1);
      tmp3 = NofibPrelude.append(tmp1, tmp2);
      return NofibPrelude.append(tmp, tmp3)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static max_(e1, e2) {
    let param0, x4, param01, y1, scrut;
    if (e1 instanceof minimax.XWin.class) {
      return minimax.XWin
    } else {
      if (e2 instanceof minimax.XWin.class) {
        return minimax.XWin
      } else if (e2 instanceof minimax.OWin.class) {
        return e1
      } else {
        if (e1 instanceof minimax.OWin.class) {
          return e2
        } else if (e1 instanceof minimax.Score.class) {
          param0 = e1.i;
          x4 = param0;
          if (e2 instanceof minimax.Score.class) {
            param01 = e2.i;
            y1 = param01;
            scrut = x4 > y1;
            if (scrut === true) {
              return minimax.Score(x4)
            } else {
              return minimax.Score(y1)
            }
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      }
    }
  } 
  static min_(e11, e21) {
    let param0, x4, param01, y1, scrut;
    if (e11 instanceof minimax.OWin.class) {
      return minimax.OWin
    } else {
      if (e21 instanceof minimax.OWin.class) {
        return minimax.OWin
      } else if (e21 instanceof minimax.XWin.class) {
        return e11
      } else {
        if (e11 instanceof minimax.XWin.class) {
          return e21
        } else if (e11 instanceof minimax.Score.class) {
          param0 = e11.i;
          x4 = param0;
          if (e21 instanceof minimax.Score.class) {
            param01 = e21.i;
            y1 = param01;
            scrut = x4 < y1;
            if (scrut === true) {
              return minimax.Score(x4)
            } else {
              return minimax.Score(y1)
            }
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      }
    }
  } 
  static mise(f4, g1, t2) {
    let param0, param1, l1, a1, tmp, tmp1, lambda$this;
    if (t2 instanceof minimax.Branch.class) {
      param0 = t2.a;
      param1 = t2.cs;
      a1 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return a1
      } else {
        l1 = param1;
        tmp = runtime.safeCall(g1(minimax.OWin, minimax.XWin));
        lambda$this = runtime.safeCall(lambda7(f4, g1));
        tmp1 = NofibPrelude.map(lambda$this, l1);
        return NofibPrelude.foldr(f4, tmp, tmp1)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static searchTree(p7, board6) {
    let tmp, lambda$this, lambda$this1;
    lambda$this = runtime.safeCall(lambda8(p7));
    lambda$this1 = runtime.safeCall(lambda9(p7));
    tmp = minimax.repTree(lambda$this, lambda$this1, board6);
    return minimax.prune(5, tmp)
  } 
  static cropTree(t3) {
    let param0, param1, x4, l1, param01, x5, l2, a1, tmp, tmp1;
    if (t3 instanceof minimax.Branch.class) {
      param0 = t3.a;
      param1 = t3.cs;
      a1 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return minimax.Branch(a1, NofibPrelude.Nil)
      } else {
        if (param0 instanceof minimax.Score.class) {
          param01 = param0.i;
          x5 = param01;
          l2 = param1;
          tmp = minimax.Score(x5);
          tmp1 = NofibPrelude.map(minimax.cropTree, l2);
          return minimax.Branch(tmp, tmp1)
        } else {
          x4 = param0;
          l1 = param1;
          return minimax.Branch(x4, NofibPrelude.Nil)
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static bestMove(p8, f5, g2, b1) {
    let tmp, tmp1, tmp2;
    tmp = minimax.searchTree(p8, b1);
    tmp1 = minimax.mapTree(minimax.static, tmp);
    tmp2 = minimax.cropTree(tmp1);
    return minimax.mise(f5, g2, tmp2)
  } 
  static alternate(player, f6, g3, board7) {
    let opposition, possibles, scores, boardd_eval, first1, first0, boardd, eval1, scrut, scrut1, scrut2, tmp, tmp1, tmp2, lambda$this;
    scrut2 = minimax.fullBoard(board7);
    if (scrut2 === true) {
      return NofibPrelude.Nil
    } else {
      tmp = minimax.static(board7);
      scrut1 = minimax.evaluationEq(tmp, minimax.XWin);
      if (scrut1 === true) {
        return NofibPrelude.Nil
      } else {
        tmp1 = minimax.static(board7);
        scrut = minimax.evaluationEq(tmp1, minimax.OWin);
        if (scrut === true) {
          return NofibPrelude.Nil
        } else {
          opposition = minimax.opposite(player);
          possibles = minimax.newPositions(player, board7);
          lambda$this = runtime.safeCall(lambda10(f6, g3, opposition));
          scores = NofibPrelude.map(lambda$this, possibles);
          boardd_eval = minimax.best(f6, possibles, scores);
          if (globalThis.Array.isArray(boardd_eval) && boardd_eval.length === 2) {
            first0 = boardd_eval[0];
            first1 = boardd_eval[1];
            boardd = first0;
            eval1 = first1;
            tmp2 = minimax.alternate(opposition, g3, f6, boardd);
            return NofibPrelude.Cons([
              boardd,
              eval1
            ], tmp2)
          } else {
            throw new globalThis.Error("match error");
          }
        }
      }
    }
  } 
  static prog(input) {
    let testBoard, game, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16;
    tmp = NofibPrelude.Cons(minimax.Empty, NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons(minimax.O, tmp);
    tmp2 = NofibPrelude.Cons(minimax.Empty, tmp1);
    tmp3 = NofibPrelude.Cons(minimax.Empty, NofibPrelude.Nil);
    tmp4 = NofibPrelude.Cons(minimax.X, tmp3);
    tmp5 = NofibPrelude.Cons(minimax.Empty, tmp4);
    tmp6 = NofibPrelude.Cons(minimax.Empty, NofibPrelude.Nil);
    tmp7 = NofibPrelude.Cons(minimax.Empty, tmp6);
    tmp8 = NofibPrelude.Cons(minimax.Empty, tmp7);
    tmp9 = NofibPrelude.Cons(tmp8, NofibPrelude.Nil);
    tmp10 = NofibPrelude.Cons(tmp5, tmp9);
    tmp11 = NofibPrelude.Cons(tmp2, tmp10);
    testBoard = tmp11;
    tmp12 = board$(testBoard, input);
    tmp13 = minimax.alternate(minimax.X, minimax.max_, minimax.min_, tmp12);
    game = tmp13;
    tmp14 = NofibPrelude.nofibStringToList("OXO\n");
    tmp15 = NofibPrelude.map(minimax.showMove, game);
    tmp16 = NofibPrelude.concat(tmp15);
    return NofibPrelude.append(tmp14, tmp16)
  }
  static toString() { return "minimax"; }
};
let minimax = minimax1; export default minimax;
