import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let mate1;
mate1 = class mate {
  static #emptyBoard;
  static {
    let tmp, tmp1, lambda;
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
    mate.#emptyBoard = tmp;
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
    lambda = (undefined, function () {
      let tmp2, tmp3;
      tmp2 = mate.testMate_nofib(0);
      tmp3 = NofibPrelude.nofibListToString(tmp2);
      return BenchmarkPrelude.print(tmp3)
    });
    tmp1 = lambda;
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
    let tmp, lambda;
    lambda = (undefined, function (a, b) {
      let first1, first0, aa, first11, first01, bb, tmp1, tmp2;
      if (globalThis.Array.isArray(a) && a.length === 2) {
        first0 = a[0];
        first1 = a[1];
        aa = first0;
        if (globalThis.Array.isArray(b) && b.length === 2) {
          first01 = b[0];
          first11 = b[1];
          bb = first01;
          tmp1 = NofibPrelude.listLen(aa);
          tmp2 = NofibPrelude.listLen(bb);
          return tmp1 <= tmp2
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    });
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
    let scrut, s_, scrut1, first1, first0, w, s__, tmp, lambda, lambda1;
    lambda = (undefined, function (x3) {
      return x3 === " "
    });
    scrut = NofibPrelude.dropWhile(lambda, s);
    if (scrut instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      s_ = scrut;
      lambda1 = (undefined, function (x3) {
        return x3 === " "
      });
      scrut1 = NofibPrelude.break_(lambda1, s_);
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
    let tmp, lambda;
    lambda = (undefined, function (l1) {
      let tmp1;
      tmp1 = NofibPrelude.Cons("\n", NofibPrelude.Nil);
      return NofibPrelude.append(l1, tmp1)
    });
    tmp = NofibPrelude.map(lambda, ls);
    return NofibPrelude.concat(tmp)
  } 
  static lines(s1) {
    let scrut, first1, first0, l1, s_, param0, param1, s__, tmp, lambda;
    lambda = (undefined, function (x3) {
      return x3 === "\n"
    });
    scrut = NofibPrelude.break_(lambda, s1);
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
    let pieceAtWith, param0, param1, wkss, bkss, tmp;
    if (bd instanceof mate.Board.class) {
      param0 = bd.a;
      param1 = bd.b;
      wkss = param0;
      bkss = param1;
      pieceAtWith = function pieceAtWith(c4, n, ls2) {
        let param01, param11, first1, first0, k, s2, xs2, scrut;
        if (ls2 instanceof NofibPrelude.Nil.class) {
          return n
        } else if (ls2 instanceof NofibPrelude.Cons.class) {
          param01 = ls2.head;
          param11 = ls2.tail;
          if (globalThis.Array.isArray(param01) && param01.length === 2) {
            first0 = param01[0];
            first1 = param01[1];
            k = first0;
            s2 = first1;
            xs2 = param11;
            scrut = NofibPrelude.eqTup2(s2, sq);
            if (scrut === true) {
              return NofibPrelude.Some([
                c4,
                k
              ])
            } else {
              return pieceAtWith(c4, n, xs2)
            }
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      };
      tmp = pieceAtWith(mate.Black, NofibPrelude.None, bkss);
      return pieceAtWith(mate.White, tmp, wkss)
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
    let showRank, tmp, tmp1, tmp2;
    showRank = function showRank(r4) {
      let consFile, tmp3;
      consFile = function consFile(f1, s2) {
        let scrut, param0, p2, tmp4, tmp5, tmp6;
        scrut = mate.pieceAt(bd1, [
          f1,
          r4
        ]);
        if (scrut instanceof NofibPrelude.None.class) {
          tmp4 = NofibPrelude.nofibStringToList(" -");
          return NofibPrelude.append(tmp4, s2)
        } else if (scrut instanceof NofibPrelude.Some.class) {
          param0 = scrut.x;
          p2 = param0;
          tmp5 = mate.pieceToChar(p2);
          tmp6 = NofibPrelude.Cons(tmp5, s2);
          return NofibPrelude.Cons(" ", tmp6)
        } else {
          throw new globalThis.Error("match error");
        }
      };
      tmp3 = NofibPrelude.enumFromTo(1, 8);
      return NofibPrelude.foldr(consFile, NofibPrelude.Nil, tmp3)
    };
    tmp = NofibPrelude.enumFromTo(1, 8);
    tmp1 = NofibPrelude.reverse(tmp);
    tmp2 = NofibPrelude.map(showRank, tmp1);
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
    let emptyAtAllAnd, param0, param1, wkss, bkss, tmp;
    if (bd2 instanceof mate.Board.class) {
      param0 = bd2.a;
      param1 = bd2.b;
      wkss = param0;
      bkss = param1;
      emptyAtAllAnd = function emptyAtAllAnd(b, ls2) {
        let param01, param11, first1, first0, s2, xs2, scrut, scrut1, tmp1;
        if (ls2 instanceof NofibPrelude.Nil.class) {
          return b
        } else if (ls2 instanceof NofibPrelude.Cons.class) {
          param01 = ls2.head;
          param11 = ls2.tail;
          if (globalThis.Array.isArray(param01) && param01.length === 2) {
            first0 = param01[0];
            first1 = param01[1];
            s2 = first1;
            xs2 = param11;
            tmp1 = runtime.safeCall(e(s2));
            scrut = BenchmarkPrelude.not(tmp1);
            if (scrut === true) {
              scrut1 = emptyAtAllAnd(b, xs2);
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
      tmp = emptyAtAllAnd(true, bkss);
      return emptyAtAllAnd(tmp, wkss)
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
    let param0, param1, param2, first1, first0, c9, k1, sq4, param01, param11, param21, sq_, mcp, mpp, capt, param02, prom, param03, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, lambda, lambda1;
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
          lambda = (undefined, function (cp) {
            let tmp17, tmp18, tmp19;
            tmp17 = mate.showPiece(cp);
            tmp18 = NofibPrelude.Cons("/", NofibPrelude.Nil);
            tmp19 = NofibPrelude.append(tmp17, tmp18);
            return NofibPrelude.Cons("x", tmp19)
          });
          tmp10 = lambda;
          tmp11 = mate.maybe(tmp9, tmp10, mcp);
          tmp12 = mate.showSquare(c9, sq_);
          lambda1 = (undefined, function (pp) {
            let tmp17, tmp18, tmp19;
            tmp17 = mate.showPiece(pp);
            tmp18 = NofibPrelude.Cons(")", NofibPrelude.Nil);
            tmp19 = NofibPrelude.append(tmp17, tmp18);
            return NofibPrelude.Cons("(", tmp19)
          });
          tmp13 = lambda1;
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
    let ml, lambda;
    ml = function ml(sq5, ms1) {
      let sq_, scrut, scrut1, param0, p_1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
      tmp = runtime.safeCall(inc(sq5));
      sq_ = tmp;
      scrut = mate.onboard(sq_);
      if (scrut === true) {
        scrut1 = mate.pieceAt(bd8, sq_);
        if (scrut1 instanceof NofibPrelude.None.class) {
          tmp1 = mate.Move(sq_, NofibPrelude.None, NofibPrelude.None);
          tmp2 = NofibPrelude.Cons(tmp1, ms1);
          return ml(sq_, tmp2)
        } else if (scrut1 instanceof NofibPrelude.Some.class) {
          param0 = scrut1.x;
          p_1 = param0;
          tmp3 = mate.colourOf(p_1);
          tmp4 = tmp3 === c10;
          scrut2 = BenchmarkPrelude.not(tmp4);
          if (scrut2 === true) {
            tmp5 = NofibPrelude.Some(p_1);
            tmp6 = mate.Move(sq_, tmp5, NofibPrelude.None);
            tmp7 = NofibPrelude.Cons(tmp6, ms1);
            return runtime.safeCall(cont(tmp7))
          } else {
            return runtime.safeCall(cont(ms1))
          }
        } else {
          return runtime.safeCall(cont(ms1))
        }
      } else {
        return runtime.safeCall(cont(ms1))
      }
    };
    lambda = (undefined, function (ms1) {
      return ml(sq4, ms1)
    });
    return lambda
  } 
  static bishopmoves(c11, sq5, bd9) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, lambda, lambda1, lambda2, lambda3, lambda4;
    lambda = (undefined, function (caseScrut) {
      let first1, first0, x3, y, tmp8, tmp9;
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        x3 = first0;
        y = first1;
        tmp8 = x3 - 1;
        tmp9 = y + 1;
        return [
          tmp8,
          tmp9
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    lambda1 = (undefined, function (caseScrut) {
      let first1, first0, x3, y, tmp8, tmp9;
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        x3 = first0;
        y = first1;
        tmp8 = x3 + 1;
        tmp9 = y + 1;
        return [
          tmp8,
          tmp9
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp1 = lambda1;
    lambda2 = (undefined, function (caseScrut) {
      let first1, first0, x3, y, tmp8, tmp9;
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        x3 = first0;
        y = first1;
        tmp8 = x3 - 1;
        tmp9 = y - 1;
        return [
          tmp8,
          tmp9
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp2 = lambda2;
    lambda3 = (undefined, function (caseScrut) {
      let first1, first0, x3, y, tmp8, tmp9;
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        x3 = first0;
        y = first1;
        tmp8 = x3 + 1;
        tmp9 = y - 1;
        return [
          tmp8,
          tmp9
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp3 = lambda3;
    lambda4 = (undefined, function (x3) {
      return x3
    });
    tmp4 = mate.moveLine(bd9, c11, sq5, tmp3, lambda4);
    tmp5 = mate.moveLine(bd9, c11, sq5, tmp2, tmp4);
    tmp6 = mate.moveLine(bd9, c11, sq5, tmp1, tmp5);
    tmp7 = mate.moveLine(bd9, c11, sq5, tmp, tmp6);
    return runtime.safeCall(tmp7(NofibPrelude.Nil))
  } 
  static rookmoves(c12, sq6, bd10) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, lambda, lambda1, lambda2, lambda3, lambda4;
    lambda = (undefined, function (caseScrut) {
      let first1, first0, x3, y, tmp8;
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        x3 = first0;
        y = first1;
        tmp8 = x3 - 1;
        return [
          tmp8,
          y
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    lambda1 = (undefined, function (caseScrut) {
      let first1, first0, x3, y, tmp8;
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        x3 = first0;
        y = first1;
        tmp8 = x3 + 1;
        return [
          tmp8,
          y
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp1 = lambda1;
    lambda2 = (undefined, function (caseScrut) {
      let first1, first0, x3, y, tmp8;
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        x3 = first0;
        y = first1;
        tmp8 = y - 1;
        return [
          x3,
          tmp8
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp2 = lambda2;
    lambda3 = (undefined, function (caseScrut) {
      let first1, first0, x3, y, tmp8;
      if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
        first0 = caseScrut[0];
        first1 = caseScrut[1];
        x3 = first0;
        y = first1;
        tmp8 = y + 1;
        return [
          x3,
          tmp8
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp3 = lambda3;
    lambda4 = (undefined, function (x3) {
      return x3
    });
    tmp4 = mate.moveLine(bd10, c12, sq6, tmp3, lambda4);
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
    let promote, lscomp1, first1, first0, p3, q, fwd, movs, on1, on2, scrut, scrut1, scrut2, scrut3, scrut4, caps, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17;
    if (globalThis.Array.isArray(pq2) && pq2.length === 2) {
      first0 = pq2[0];
      first1 = pq2[1];
      p3 = first0;
      q = first1;
      promote = function promote(xy, mcp) {
        let first11, first01, x3, y, scrut5, scrut6, scrut7, scrut8, scrut9, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, lambda;
        if (globalThis.Array.isArray(xy) && xy.length === 2) {
          first01 = xy[0];
          first11 = xy[1];
          x3 = first01;
          y = first11;
          if (c15 instanceof mate.Black.class) {
            tmp18 = true;
          } else {
            tmp18 = false;
          }
          scrut5 = tmp18;
          if (scrut5 === true) {
            scrut6 = y === 1;
            if (scrut6 === true) {
              tmp19 = true;
            } else {
              tmp19 = false;
            }
          } else {
            tmp19 = false;
          }
          if (c15 instanceof mate.White.class) {
            tmp20 = true;
          } else {
            tmp20 = false;
          }
          scrut7 = tmp20;
          if (scrut7 === true) {
            scrut8 = y === 8;
            if (scrut8 === true) {
              tmp21 = true;
            } else {
              tmp21 = false;
            }
          } else {
            tmp21 = false;
          }
          scrut9 = tmp19 || tmp21;
          if (scrut9 === true) {
            tmp22 = NofibPrelude.Cons([
              c15,
              mate.Knight
            ], NofibPrelude.Nil);
            tmp23 = NofibPrelude.Cons([
              c15,
              mate.Bishop
            ], tmp22);
            tmp24 = NofibPrelude.Cons([
              c15,
              mate.Rook
            ], tmp23);
            tmp25 = NofibPrelude.Cons([
              c15,
              mate.Queen
            ], tmp24);
            lambda = (undefined, function (param) {
              let tmp27;
              tmp27 = NofibPrelude.Some(param);
              return mate.Move([
                x3,
                y
              ], mcp, tmp27)
            });
            return NofibPrelude.map(lambda, tmp25)
          } else {
            tmp26 = mate.Move([
              x3,
              y
            ], mcp, NofibPrelude.None);
            return NofibPrelude.Cons(tmp26, NofibPrelude.Nil)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      };
      lscomp1 = function lscomp1(ls2) {
        let lscomp2, param0, param1, sq7, sqs1, tmp18, tmp19;
        if (ls2 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (ls2 instanceof NofibPrelude.Cons.class) {
          param0 = ls2.head;
          param1 = ls2.tail;
          sq7 = param0;
          sqs1 = param1;
          lscomp2 = function lscomp2(ls3) {
            let param01, param11, h, ls4, param02, p_1, scrut5, tmp20, tmp21, tmp22, tmp23, tmp24;
            if (ls3 instanceof NofibPrelude.Nil.class) {
              return lscomp1(sqs1)
            } else if (ls3 instanceof NofibPrelude.Cons.class) {
              param01 = ls3.head;
              param11 = ls3.tail;
              h = param01;
              ls4 = param11;
              if (h instanceof NofibPrelude.Some.class) {
                param02 = h.x;
                p_1 = param02;
                tmp20 = mate.colourOf(p_1);
                tmp21 = tmp20 === c15;
                scrut5 = BenchmarkPrelude.not(tmp21);
                if (scrut5 === true) {
                  tmp22 = NofibPrelude.Some(p_1);
                  tmp23 = promote(sq7, tmp22);
                  tmp24 = lscomp2(ls4);
                  return NofibPrelude.Cons(tmp23, tmp24)
                } else {
                  return lscomp2(ls4)
                }
              } else {
                return lscomp2(ls4)
              }
            } else {
              throw new globalThis.Error("match error");
            }
          };
          tmp18 = mate.pieceAt(bd13, sq7);
          tmp19 = NofibPrelude.Cons(tmp18, NofibPrelude.Nil);
          return lscomp2(tmp19)
        } else {
          throw new globalThis.Error("match error");
        }
      };
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
        tmp4 = promote(on1, NofibPrelude.None);
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
      tmp16 = lscomp1(tmp15);
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
    let givesCheck, tmp, tmp1;
    givesCheck = function givesCheck(kxy) {
      let kthreat, first1, first0, k1, first11, first01, x3, y;
      if (globalThis.Array.isArray(kxy) && kxy.length === 2) {
        first0 = kxy[0];
        first1 = kxy[1];
        k1 = first0;
        if (globalThis.Array.isArray(first1) && first1.length === 2) {
          first01 = first1[0];
          first11 = first1[1];
          x3 = first01;
          y = first11;
          kthreat = function kthreat(param) {
            let scrut, first12, first02, xk, yk, scrut1, scrut2, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, lambda, lambda1, lambda2, lambda3;
            scrut = mate.kingSquare(c17, bd15);
            if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
              first02 = scrut[0];
              first12 = scrut[1];
              xk = first02;
              yk = first12;
              if (param instanceof mate.King.class) {
                tmp2 = x3 - xk;
                tmp3 = NofibPrelude.abs(tmp2);
                scrut1 = tmp3 <= 1;
                if (scrut1 === true) {
                  tmp4 = y - yk;
                  tmp5 = NofibPrelude.abs(tmp4);
                  scrut2 = tmp5 <= 1;
                  if (scrut2 === true) {
                    return true
                  } else {
                    return false
                  }
                } else {
                  return false
                }
              } else if (param instanceof mate.Queen.class) {
                tmp6 = kthreat(mate.Rook);
                tmp7 = kthreat(mate.Bishop);
                return tmp6 || tmp7
              } else if (param instanceof mate.Rook.class) {
                tmp8 = x3 === xk;
                lambda = (undefined, function (caseScrut) {
                  let first13, first03, xe, ye, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53;
                  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                    first03 = caseScrut[0];
                    first13 = caseScrut[1];
                    xe = first03;
                    ye = first13;
                    tmp48 = xe === xk;
                    tmp49 = NofibPrelude.min(y, yk);
                    tmp50 = tmp49 < ye;
                    tmp51 = NofibPrelude.max(y, yk);
                    tmp52 = ye < tmp51;
                    tmp53 = tmp50 && tmp52;
                    return tmp48 && tmp53
                  } else {
                    throw new globalThis.Error("match error");
                  }
                });
                tmp9 = lambda;
                tmp10 = mate.emptyAtAll(bd15, tmp9);
                tmp11 = tmp8 && tmp10;
                tmp12 = y === yk;
                lambda1 = (undefined, function (caseScrut) {
                  let first13, first03, xe, ye, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53;
                  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                    first03 = caseScrut[0];
                    first13 = caseScrut[1];
                    xe = first03;
                    ye = first13;
                    tmp48 = ye === yk;
                    tmp49 = NofibPrelude.min(x3, xk);
                    tmp50 = tmp49 < xe;
                    tmp51 = NofibPrelude.max(x3, xk);
                    tmp52 = xe < tmp51;
                    tmp53 = tmp50 && tmp52;
                    return tmp48 && tmp53
                  } else {
                    throw new globalThis.Error("match error");
                  }
                });
                tmp13 = lambda1;
                tmp14 = mate.emptyAtAll(bd15, tmp13);
                tmp15 = tmp12 && tmp14;
                return tmp11 || tmp15
              } else if (param instanceof mate.Bishop.class) {
                tmp16 = x3 + y;
                tmp17 = xk + yk;
                tmp18 = tmp16 === tmp17;
                lambda2 = (undefined, function (caseScrut) {
                  let first13, first03, xe, ye, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55;
                  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                    first03 = caseScrut[0];
                    first13 = caseScrut[1];
                    xe = first03;
                    ye = first13;
                    tmp48 = xe + ye;
                    tmp49 = xk + yk;
                    tmp50 = tmp48 === tmp49;
                    tmp51 = NofibPrelude.min(x3, xk);
                    tmp52 = tmp51 < xe;
                    tmp53 = NofibPrelude.max(x3, xk);
                    tmp54 = xe < tmp53;
                    tmp55 = tmp52 && tmp54;
                    return tmp50 && tmp55
                  } else {
                    throw new globalThis.Error("match error");
                  }
                });
                tmp19 = lambda2;
                tmp20 = mate.emptyAtAll(bd15, tmp19);
                tmp21 = tmp18 && tmp20;
                tmp22 = x3 - y;
                tmp23 = xk - yk;
                tmp24 = tmp22 === tmp23;
                lambda3 = (undefined, function (caseScrut) {
                  let first13, first03, xe, ye, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55;
                  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
                    first03 = caseScrut[0];
                    first13 = caseScrut[1];
                    xe = first03;
                    ye = first13;
                    tmp48 = xe - ye;
                    tmp49 = xk - yk;
                    tmp50 = tmp48 === tmp49;
                    tmp51 = NofibPrelude.min(x3, xk);
                    tmp52 = tmp51 < xe;
                    tmp53 = NofibPrelude.max(x3, xk);
                    tmp54 = xe < tmp53;
                    tmp55 = tmp52 && tmp54;
                    return tmp50 && tmp55
                  } else {
                    throw new globalThis.Error("match error");
                  }
                });
                tmp25 = lambda3;
                tmp26 = mate.emptyAtAll(bd15, tmp25);
                tmp27 = tmp24 && tmp26;
                return tmp21 || tmp27
              } else if (param instanceof mate.Knight.class) {
                tmp28 = x3 - xk;
                tmp29 = NofibPrelude.abs(tmp28);
                tmp30 = tmp29 === 2;
                tmp31 = y - yk;
                tmp32 = NofibPrelude.abs(tmp31);
                tmp33 = tmp32 === 1;
                tmp34 = tmp30 && tmp33;
                tmp35 = x3 - xk;
                tmp36 = NofibPrelude.abs(tmp35);
                tmp37 = tmp36 === 1;
                tmp38 = y - yk;
                tmp39 = NofibPrelude.abs(tmp38);
                tmp40 = tmp39 === 2;
                tmp41 = tmp37 && tmp40;
                return tmp34 || tmp41
              } else if (param instanceof mate.Pawn.class) {
                tmp42 = x3 - xk;
                tmp43 = NofibPrelude.abs(tmp42);
                tmp44 = tmp43 === 1;
                if (c17 instanceof mate.Black.class) {
                  tmp45 = y + 1;
                  tmp46 = yk === tmp45;
                } else {
                  tmp47 = y - 1;
                  tmp46 = yk === tmp47;
                }
                return tmp44 && tmp46
              } else {
                throw new globalThis.Error("match error");
              }
            } else {
              throw new globalThis.Error("match error");
            }
          };
          return kthreat(k1)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = mate.opponent(c17);
    tmp1 = mate.forcesColoured(tmp, bd15);
    return mate.any(givesCheck, tmp1)
  } 
  static tryMove(c18, ksq, m1, bd16) {
    let first1, first0, k1, sq8, param0, param1, param2, sq_, mcp, mpp, p3, bd17, p_1, bd21, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, lambda, lambda1;
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
        lambda = (undefined, function (x3) {
          return x3
        });
        tmp1 = mate.maybe(p3, lambda, mpp);
        p_1 = tmp1;
        tmp2 = mate.putPieceAt(sq_, p_1, bd17);
        lambda1 = (undefined, function (dummy) {
          let tmp8, tmp9;
          tmp8 = mate.opponent(c18);
          tmp9 = mate.rmPieceAt(tmp8, sq_, bd17);
          return mate.putPieceAt(sq_, p_1, tmp9)
        });
        tmp3 = lambda1;
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
    let tmp, lambda;
    tmp = mate.forcesColoured(c20, bd18);
    lambda = (undefined, function (ksq2, ms1) {
      let tmp1, tmp2, lambda1;
      lambda1 = (undefined, function (rm, ms_) {
        let tmp3, tmp4, lambda2, lambda3;
        tmp3 = mate.tryMove(c20, ksq2, rm, bd18);
        lambda2 = (undefined, function (x3) {
          return x3
        });
        lambda3 = (undefined, function (h) {
          let lambda4;
          lambda4 = (undefined, function (t) {
            return NofibPrelude.Cons(h, t)
          });
          return lambda4
        });
        tmp4 = mate.maybe(lambda2, lambda3, tmp3);
        return runtime.safeCall(tmp4(ms_))
      });
      tmp1 = lambda1;
      tmp2 = mate.rawmoves(c20, ksq2, bd18);
      return NofibPrelude.foldr(tmp1, ms1, tmp2)
    });
    return NofibPrelude.foldr(lambda, NofibPrelude.Nil, tmp)
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
    let tmp, tmp1, tmp2, lambda, lambda1;
    tmp = NofibPrelude.enumFromTo(1, 8);
    lambda = (undefined, function (pp) {
      let tmp3;
      tmp3 = pp === " ";
      return BenchmarkPrelude.not(tmp3)
    });
    tmp1 = NofibPrelude.filter(lambda, x3);
    lambda1 = (undefined, function (a1, b) {
      return mate.parseSquare(r5, a1, b)
    });
    tmp2 = NofibPrelude.zipWith(lambda1, tmp, tmp1);
    return NofibPrelude.concat(tmp2)
  } 
  static parseBoard(ls4) {
    let addPiece, tmp, tmp1, tmp2, tmp3;
    addPiece = function addPiece(p_sq, x4) {
      let first1, first0, p3, sq8;
      if (globalThis.Array.isArray(p_sq) && p_sq.length === 2) {
        first0 = p_sq[0];
        first1 = p_sq[1];
        p3 = first0;
        sq8 = first1;
        return mate.putPieceAt(sq8, p3, x4)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = NofibPrelude.enumFromTo(1, 8);
    tmp1 = NofibPrelude.reverse(tmp);
    tmp2 = NofibPrelude.zipWith(mate.parseRank, tmp1, ls4);
    tmp3 = NofibPrelude.concat(tmp2);
    return NofibPrelude.foldr(addPiece, mate.#emptyBoard, tmp3)
  } 
  static parseProblem(s4) {
    let bdtxt_gltxt, first1, first0, bdtxt, gltxt, bd19, gl, tmp, tmp1, tmp2, tmp3, lambda;
    lambda = (undefined, function (x4) {
      let tmp4;
      tmp4 = mate.comment(x4);
      return BenchmarkPrelude.not(tmp4)
    });
    tmp = NofibPrelude.filter(lambda, s4);
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
    let param0, param1, h, t, tmp, lambda;
    if (x4 instanceof NofibPrelude.Cons.class) {
      param0 = x4.head;
      param1 = x4.tail;
      h = param0;
      t = param1;
      lambda = (undefined, function () {
        return mate.foldr_lz(f2, a1, t)
      });
      tmp = NofibPrelude.lazy(lambda);
      return runtime.safeCall(f2(h, tmp))
    } else if (x4 instanceof NofibPrelude.Nil.class) {
      return a1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static replies(bd19, c22, n) {
    let solnAnd, mds, scrut, scrut1, scrut2, tmp, tmp1;
    solnAnd = function solnAnd(mifb, rest) {
      let first1, first0, mif, b, sm, param0, s6, scrut3, param01, ms1, tmp2, tmp3, tmp4, tmp5;
      if (globalThis.Array.isArray(mifb) && mifb.length === 2) {
        first0 = mifb[0];
        first1 = mifb[1];
        mif = first0;
        b = first1;
        tmp2 = mate.opponent(c22);
        tmp3 = n - 1;
        tmp4 = mate.solution(b, tmp2, tmp3);
        sm = tmp4;
        if (sm instanceof NofibPrelude.None.class) {
          return NofibPrelude.None
        } else if (sm instanceof NofibPrelude.Some.class) {
          param0 = sm.x;
          s6 = param0;
          scrut3 = NofibPrelude.force(rest);
          if (scrut3 instanceof NofibPrelude.None.class) {
            return NofibPrelude.None
          } else if (scrut3 instanceof NofibPrelude.Some.class) {
            param01 = scrut3.x;
            ms1 = param01;
            tmp5 = NofibPrelude.Cons([
              mif,
              s6
            ], ms1);
            return NofibPrelude.Some(tmp5)
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
        return mate.foldr_lz(solnAnd, tmp1, mds)
      } else {
        throw globalThis.Error("n < 0");
      }
    }
  } 
  static solution(bd20, c23, n1) {
    let solnOr, scrut, mds, tmp;
    solnOr = function solnOr(mifb, other) {
      let first1, first0, mif, b, rsm, param0, rs, scrut1, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
      if (globalThis.Array.isArray(mifb) && mifb.length === 2) {
        first0 = mifb[0];
        first1 = mifb[1];
        mif = first0;
        b = first1;
        tmp1 = mate.opponent(c23);
        tmp2 = n1 - 1;
        tmp3 = mate.replies(b, tmp1, tmp2);
        rsm = tmp3;
        if (rsm instanceof NofibPrelude.None.class) {
          return NofibPrelude.force(other)
        } else if (rsm instanceof NofibPrelude.Some.class) {
          param0 = rsm.x;
          if (param0 instanceof NofibPrelude.Nil.class) {
            tmp4 = mate.opponent(c23);
            scrut1 = mate.kingincheck(tmp4, b);
            if (scrut1 === true) {
              tmp5 = mate.Solution(mif, NofibPrelude.Nil);
              return NofibPrelude.Some(tmp5)
            } else {
              return NofibPrelude.force(other)
            }
          } else {
            rs = param0;
            tmp6 = mate.Solution(mif, rs);
            return NofibPrelude.Some(tmp6)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    scrut = n1 > 0;
    if (scrut === true) {
      tmp = mate.moveDetailsFor(c23, bd20);
      mds = tmp;
      return mate.foldr_lz(solnOr, NofibPrelude.None, mds)
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
    let insert, ic, first1, first0, mif, s8, cs, tmp;
    if (globalThis.Array.isArray(mif_s) && mif_s.length === 2) {
      first0 = mif_s[0];
      first1 = mif_s[1];
      mif = first0;
      s8 = first1;
      insert = function insert(x5, ls6) {
        let param0, param1, y, ys2, scrut, tmp1, tmp2;
        if (ls6 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Cons(x5, NofibPrelude.Nil)
        } else if (ls6 instanceof NofibPrelude.Cons.class) {
          param0 = ls6.head;
          param1 = ls6.tail;
          y = param0;
          ys2 = param1;
          scrut = x5 > y;
          if (scrut === true) {
            tmp1 = insert(x5, ys2);
            return NofibPrelude.Cons(y, tmp1)
          } else {
            tmp2 = NofibPrelude.Cons(y, ys2);
            return NofibPrelude.Cons(x5, tmp2)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      };
      ic = function ic(ls6) {
        let param0, param1, first11, first01, mifs2, cs_, etc, a2, b, scrut, scrut1, scrut2, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, lambda, lambda1, lambda2, lambda3;
        if (ls6 instanceof NofibPrelude.Nil.class) {
          tmp1 = NofibPrelude.Cons(mif, NofibPrelude.Nil);
          return NofibPrelude.Cons([
            tmp1,
            cs
          ], NofibPrelude.Nil)
        } else if (ls6 instanceof NofibPrelude.Cons.class) {
          param0 = ls6.head;
          param1 = ls6.tail;
          if (globalThis.Array.isArray(param0) && param0.length === 2) {
            first01 = param0[0];
            first11 = param0[1];
            mifs2 = first01;
            cs_ = first11;
            etc = param1;
            tmp2 = mate.showSoln(cs, 1);
            a2 = tmp2;
            tmp3 = mate.showSoln(cs_, 1);
            b = tmp3;
            lambda = (undefined, function (x5, y) {
              return x5 < y
            });
            lambda1 = (undefined, function (x5, y) {
              return x5 > y
            });
            scrut2 = NofibPrelude.ltList(a2, b, lambda, lambda1);
            if (scrut2 === true) {
              tmp4 = NofibPrelude.Cons(mif, NofibPrelude.Nil);
              tmp5 = NofibPrelude.Cons([
                mifs2,
                cs_
              ], etc);
              return NofibPrelude.Cons([
                tmp4,
                cs
              ], tmp5)
            } else {
              scrut1 = NofibPrelude.listEq(a2, b);
              if (scrut1 === true) {
                tmp6 = insert(mif, mifs2);
                return NofibPrelude.Cons([
                  tmp6,
                  cs
                ], etc)
              } else {
                lambda2 = (undefined, function (x5, y) {
                  return x5 < y
                });
                lambda3 = (undefined, function (x5, y) {
                  return x5 > y
                });
                tmp7 = NofibPrelude.ltList(a2, b, lambda2, lambda3);
                scrut = BenchmarkPrelude.not(tmp7);
                if (scrut === true) {
                  tmp8 = ic(etc);
                  return NofibPrelude.Cons([
                    mifs2,
                    cs_
                  ], tmp8)
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
      tmp = mate.compact(s8);
      cs = tmp;
      return ic(ls5)
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
