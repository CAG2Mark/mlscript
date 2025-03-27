import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let go, lscomp2, lscomp1, lscomp21, lscomp11, find, logTen, lscomp, lscomp3, lscomp4, lscomp22, lscomp12, pp, strToInt, argsOk, all_digits, knights1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda14, lambda15, lambda16, lambda17, lambda18, lambda19, lambda20, lambda21, lambda22, lscomp2$, lscomp1$, lambda$, lscomp2$1, lambda$1, lscomp1$1, lambda$2, lambda$3, lambda$4, lscomp$, lambda$5, lambda$6, lambda$7, lscomp1$2, lscomp2$2, lambda$8, lambda$9;
lambda21 = (undefined, function (a, b) {
  let tmp;
  tmp = knights1.myIsDigit(a);
  return tmp && b
});
all_digits = function all_digits(s) {
  return NofibPrelude.foldr(lambda21, true, s)
};
lambda22 = (undefined, function (a, b) {
  let tmp;
  tmp = all_digits(a);
  return tmp && b
});
argsOk = function argsOk(ss) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.listLen(ss);
  tmp1 = tmp === 2;
  tmp2 = NofibPrelude.foldr(lambda22, true, ss);
  return tmp1 && tmp2
};
strToInt = function strToInt(y, xs) {
  let param0, param1, x, xs1, tmp, tmp1, tmp2, tmp3;
  if (xs instanceof NofibPrelude.Nil.class) {
    return y
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs1 = param1;
    tmp = 10 * y;
    tmp1 = runtime.safeCall(x.codePointAt(0));
    tmp2 = tmp1 - 48;
    tmp3 = tmp + tmp2;
    return strToInt(tmp3, xs1)
  } else {
    throw new globalThis.Error("match error");
  }
};
pp = function pp(xs) {
  let param0, param1, first1, first0, x, y, xs1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
  if (xs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      x = first0;
      y = first1;
      xs1 = param1;
      tmp = NofibPrelude.nofibStringToList("\nKnights tour with ");
      tmp1 = NofibPrelude.stringOfInt(x);
      tmp2 = NofibPrelude.nofibStringToList(tmp1);
      tmp3 = NofibPrelude.nofibStringToList(" backtracking moves\n");
      tmp4 = knights1.showChessSet(y);
      tmp5 = pp(xs1);
      tmp6 = NofibPrelude.append(tmp4, tmp5);
      tmp7 = NofibPrelude.append(tmp3, tmp6);
      tmp8 = NofibPrelude.append(tmp2, tmp7);
      return NofibPrelude.append(tmp, tmp8)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda20 = (undefined, function (x) {
  return strToInt(0, x)
});
lambda18 = (undefined, function () {
  return NofibPrelude.LzNil
});
lambda$9 = function lambda$(q, growFn, finFn) {
  let tmp, tmp1, tmp2;
  tmp = knights1.inquireFront_lz(q);
  tmp1 = knights1.removeFront_lz(q);
  tmp2 = knights1.depthSearch(tmp1, growFn, finFn);
  return NofibPrelude.LzCons(tmp, tmp2)
};
lambda19 = (undefined, function (q, growFn, finFn) {
  return () => {
    return lambda$9(q, growFn, finFn)
  }
});
lambda15 = (undefined, function () {
  return NofibPrelude.LzNil
});
lambda$8 = function lambda$(sze, h1, t1, h2, t2) {
  let tmp;
  tmp = lscomp2$2(sze, h1, t1, t2);
  return NofibPrelude.LzCons([
    h1,
    h2
  ], tmp)
};
lambda16 = (undefined, function (sze, h1, t1, h2, t2) {
  return () => {
    return lambda$8(sze, h1, t1, h2, t2)
  }
});
lscomp2$2 = function lscomp2$(sze, h1, t1, ls) {
  let param0, param1, h2, t2, lambda$this;
  if (ls instanceof NofibPrelude.Nil.class) {
    return lscomp1$2(sze, t1)
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h2 = param0;
    t2 = param1;
    lambda$this = runtime.safeCall(lambda16(sze, h1, t1, h2, t2));
    return NofibPrelude.lazy(lambda$this)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp22 = function lscomp2(sze, h1, t1) {
  return (ls) => {
    return lscomp2$2(sze, h1, t1, ls)
  }
};
lscomp1$2 = function lscomp1$(sze, ls) {
  let param0, param1, h1, t1, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.lazy(lambda15)
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h1 = param0;
    t1 = param1;
    tmp = NofibPrelude.enumFromTo(1, sze);
    return lscomp2$2(sze, h1, t1, tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp12 = function lscomp1(sze) {
  return (ls) => {
    return lscomp1$2(sze, ls)
  }
};
lambda17 = (undefined, function () {
  return NofibPrelude.LzNil
});
lambda11 = (undefined, function () {
  return NofibPrelude.LzNil
});
lambda13 = (undefined, function () {
  return NofibPrelude.LzNil
});
lambda$7 = function lambda$(h) {
  let tmp;
  tmp = NofibPrelude.lazy(lambda13);
  return NofibPrelude.LzCons(h, tmp)
};
lambda12 = (undefined, function (h) {
  return () => {
    return lambda$7(h)
  }
});
lambda14 = (undefined, function () {
  return NofibPrelude.LzNil
});
lscomp4 = function lscomp(ls) {
  let scrut, param0, param1, first1, first0, y, x, t, scrut1, tmp;
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
        tmp = lscomp4(t);
        return NofibPrelude.Cons(x, tmp)
      } else {
        return lscomp4(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda9 = (undefined, function () {
  return NofibPrelude.LzNil
});
lambda$6 = function lambda$(x, t) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = knights1.deleteFirst(x);
  tmp1 = knights1.possibleMoves(tmp);
  tmp2 = NofibPrelude.listLen(tmp1);
  tmp3 = lscomp3(t);
  return NofibPrelude.LzCons([
    tmp2,
    x
  ], tmp3)
};
lambda10 = (undefined, function (x, t) {
  return () => {
    return lambda$6(x, t)
  }
});
lscomp3 = function lscomp(ls) {
  let param0, param1, x, t, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.lazy(lambda9)
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    x = param0;
    t = param1;
    tmp = runtime.safeCall(lambda10(x, t));
    return NofibPrelude.lazy(tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$5 = function lambda$(board, b) {
  return knights1.moveKnight(board, b)
};
lambda8 = (undefined, function (board) {
  return (b) => {
    return lambda$5(board, b)
  }
});
lscomp$ = function lscomp$(board, ls) {
  let param0, param1, x, t, scrut, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    x = param0;
    t = param1;
    scrut = knights1.canMove(board, x);
    if (scrut === true) {
      tmp = lscomp$(board, t);
      return NofibPrelude.Cons(x, tmp)
    } else {
      return lscomp$(board, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp = function lscomp(board) {
  return (ls) => {
    return lscomp$(board, ls)
  }
};
logTen = function logTen(x) {
  let scrut, tmp, tmp1;
  scrut = x === 0;
  if (scrut === true) {
    return 0
  } else {
    tmp = NofibPrelude.intDiv(x, 10);
    tmp1 = logTen(tmp);
    return 1 + tmp1
  }
};
find = function find(x, xs) {
  let param0, param1, y, xs1, scrut, tmp;
  if (xs instanceof NofibPrelude.Nil.class) {
    throw globalThis.Error("Tile not used");
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    y = param0;
    xs1 = param1;
    scrut = NofibPrelude.eqTup2(x, y);
    if (scrut === true) {
      tmp = NofibPrelude.listLen(xs1);
      return 1 + tmp
    } else {
      return find(x, xs1)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$4 = function lambda$(ts_) {
  return knights1.myLast(ts_)
};
lambda7 = (undefined, function (ts_) {
  return () => {
    return lambda$4(ts_)
  }
});
lambda$3 = function lambda$(t) {
  return t
};
lambda6 = (undefined, function (t) {
  return () => {
    return lambda$3(t)
  }
});
lambda = (undefined, function () {
  return NofibPrelude.LzNil
});
lambda1 = (undefined, function () {
  return NofibPrelude.LzNil
});
lambda$2 = function lambda$(x, h, t) {
  let tmp;
  tmp = lscomp1$1(x, t);
  return NofibPrelude.LzCons(h, tmp)
};
lambda2 = (undefined, function (x, h, t) {
  return () => {
    return lambda$2(x, h, t)
  }
});
lscomp1$1 = function lscomp1$(x, ls) {
  let scrut, param0, param1, h, t, scrut1, lambda$this;
  scrut = NofibPrelude.force(ls);
  if (scrut instanceof NofibPrelude.LzNil.class) {
    return NofibPrelude.lazy(lambda1)
  } else if (scrut instanceof NofibPrelude.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    h = param0;
    t = param1;
    scrut1 = knights1.intChessSetComp(h, x);
    if (scrut1 === true) {
      lambda$this = runtime.safeCall(lambda2(x, h, t));
      return NofibPrelude.lazy(lambda$this)
    } else {
      return lscomp1$1(x, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp11 = function lscomp1(x) {
  return (ls) => {
    return lscomp1$1(x, ls)
  }
};
lambda3 = (undefined, function () {
  return NofibPrelude.LzNil
});
lambda$1 = function lambda$(x, h, t) {
  let tmp;
  tmp = lscomp2$1(x, t);
  return NofibPrelude.LzCons(h, tmp)
};
lambda4 = (undefined, function (x, h, t) {
  return () => {
    return lambda$1(x, h, t)
  }
});
lscomp2$1 = function lscomp2$(x, ls) {
  let scrut, param0, param1, h, t, scrut1, tmp, lambda$this;
  scrut = NofibPrelude.force(ls);
  if (scrut instanceof NofibPrelude.LzNil.class) {
    return NofibPrelude.lazy(lambda3)
  } else if (scrut instanceof NofibPrelude.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    h = param0;
    t = param1;
    tmp = knights1.intChessSetComp(h, x);
    scrut1 = BenchmarkPrelude.not(tmp);
    if (scrut1 === true) {
      lambda$this = runtime.safeCall(lambda4(x, h, t));
      return NofibPrelude.lazy(lambda$this)
    } else {
      return lscomp2$1(x, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp21 = function lscomp2(x) {
  return (ls) => {
    return lscomp2$1(x, ls)
  }
};
lambda$ = function lambda$(x, xs) {
  let tmp, tmp1;
  tmp = lscomp2$1(x, xs);
  tmp1 = knights1.quickSortIntChessSet(tmp);
  return NofibPrelude.LzCons(x, tmp1)
};
lambda5 = (undefined, function (x, xs) {
  return () => {
    return lambda$(x, xs)
  }
});
lscomp1$ = function lscomp1$(x, ls) {
  let param0, param1, h, t, scrut, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    scrut = knights1.intintComp(h, x);
    if (scrut === true) {
      tmp = lscomp1$(x, t);
      return NofibPrelude.Cons(h, tmp)
    } else {
      return lscomp1$(x, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp1 = function lscomp1(x) {
  return (ls) => {
    return lscomp1$(x, ls)
  }
};
lscomp2$ = function lscomp2$(x, ls) {
  let param0, param1, h, t, scrut, tmp, tmp1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    tmp = knights1.intintComp(h, x);
    scrut = BenchmarkPrelude.not(tmp);
    if (scrut === true) {
      tmp1 = lscomp2$(x, t);
      return NofibPrelude.Cons(h, tmp1)
    } else {
      return lscomp2$(x, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp2 = function lscomp2(x) {
  return (ls) => {
    return lscomp2$(x, ls)
  }
};
go = function go(h, t) {
  let param0, param1, head, t1;
  if (t instanceof NofibPrelude.Nil.class) {
    return h
  } else if (t instanceof NofibPrelude.Cons.class) {
    param0 = t.head;
    param1 = t.tail;
    head = param0;
    t1 = param1;
    return go(head, t1)
  } else {
    throw new globalThis.Error("match error");
  }
};
knights1 = class knights {
  static {
    knights1 = knights;
    let tmp, lambda23;
    this.createQueue = NofibPrelude.Nil;
    this.Board = function Board(a1, b1, c1, d1) {
      return new Board.class(a1, b1, c1, d1);
    };
    this.Board.class = class Board {
      constructor(a, b, c, d) {
        this.a = a;
        this.b = b;
        this.c = c;
        this.d = d;
      }
      toString() { return "Board(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.c) + ", " + globalThis.Predef.render(this.d) + ")"; }
    };
    this.Direction = class Direction {
      constructor() {}
      toString() { return "Direction"; }
    };
    const UL$class = class UL extends knights.Direction {
      constructor() {
        super();
      }
      toString() { return "UL"; }
    };
    this.UL = new UL$class;
    this.UL.class = UL$class;
    const UR$class = class UR extends knights.Direction {
      constructor() {
        super();
      }
      toString() { return "UR"; }
    };
    this.UR = new UR$class;
    this.UR.class = UR$class;
    const DL$class = class DL extends knights.Direction {
      constructor() {
        super();
      }
      toString() { return "DL"; }
    };
    this.DL = new DL$class;
    this.DL.class = DL$class;
    const DR$class = class DR extends knights.Direction {
      constructor() {
        super();
      }
      toString() { return "DR"; }
    };
    this.DR = new DR$class;
    this.DR.class = DR$class;
    const LU$class = class LU extends knights.Direction {
      constructor() {
        super();
      }
      toString() { return "LU"; }
    };
    this.LU = new LU$class;
    this.LU.class = LU$class;
    const LD$class = class LD extends knights.Direction {
      constructor() {
        super();
      }
      toString() { return "LD"; }
    };
    this.LD = new LD$class;
    this.LD.class = LD$class;
    const RU$class = class RU extends knights.Direction {
      constructor() {
        super();
      }
      toString() { return "RU"; }
    };
    this.RU = new RU$class;
    this.RU.class = RU$class;
    const RD$class = class RD extends knights.Direction {
      constructor() {
        super();
      }
      toString() { return "RD"; }
    };
    this.RD = new RD$class;
    this.RD.class = RD$class;
    lambda23 = (undefined, function () {
      let tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
      tmp1 = NofibPrelude.nofibStringToList("8");
      tmp2 = NofibPrelude.nofibStringToList("1");
      tmp3 = NofibPrelude.Cons(tmp2, NofibPrelude.Nil);
      tmp4 = NofibPrelude.Cons(tmp1, tmp3);
      tmp5 = knights.testKnights_nofib(tmp4);
      tmp6 = NofibPrelude.nofibListToString(tmp5);
      return BenchmarkPrelude.print(tmp6)
    });
    tmp = lambda23;
    BenchmarkPrelude.benchmark(tmp)
  }
  static myIsDigit(c) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = runtime.safeCall(c.codePointAt(0));
    tmp1 = tmp >= 48;
    tmp2 = runtime.safeCall(c.codePointAt(0));
    tmp3 = tmp2 <= 57;
    return tmp1 && tmp3
  } 
  static intintComp(a_b, c_d) {
    let first1, first0, a, b, first11, first01, c1, d, tmp, tmp1, tmp2, tmp3;
    if (globalThis.Array.isArray(a_b) && a_b.length === 2) {
      first0 = a_b[0];
      first1 = a_b[1];
      a = first0;
      b = first1;
      if (globalThis.Array.isArray(c_d) && c_d.length === 2) {
        first01 = c_d[0];
        first11 = c_d[1];
        c1 = first01;
        d = first11;
        tmp = a < c1;
        tmp1 = a === c1;
        tmp2 = b < d;
        tmp3 = tmp1 && tmp2;
        return tmp || tmp3
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static intChessSetComp(a_b1, c_d1) {
    let first1, first0, a, b, first11, first01, c1, d;
    if (globalThis.Array.isArray(a_b1) && a_b1.length === 2) {
      first0 = a_b1[0];
      first1 = a_b1[1];
      a = first0;
      b = first1;
      if (globalThis.Array.isArray(c_d1) && c_d1.length === 2) {
        first01 = c_d1[0];
        first11 = c_d1[1];
        c1 = first01;
        d = first11;
        return a < c1
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static myInit(a_t) {
    let param0, param1, a, t, a1, tmp;
    if (a_t instanceof NofibPrelude.Cons.class) {
      param0 = a_t.head;
      param1 = a_t.tail;
      a1 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else {
        a = param0;
        t = param1;
        tmp = knights.myInit(t);
        return NofibPrelude.Cons(a, tmp)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static myLast(a_t1) {
    let param0, param1, a, t;
    if (a_t1 instanceof NofibPrelude.Cons.class) {
      param0 = a_t1.head;
      param1 = a_t1.tail;
      a = param0;
      t = param1;
      return go(a, t)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static quickSortIntInt(xs) {
    let param0, param1, x, xs1, tmp, tmp1, tmp2, tmp3, tmp4;
    if (xs instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param0 = xs.head;
      param1 = xs.tail;
      x = param0;
      xs1 = param1;
      tmp = lscomp1$(x, xs1);
      tmp1 = knights.quickSortIntInt(tmp);
      tmp2 = lscomp2$(x, xs1);
      tmp3 = knights.quickSortIntInt(tmp2);
      tmp4 = NofibPrelude.Cons(x, tmp3);
      return NofibPrelude.append(tmp1, tmp4)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static quickSortIntChessSet(xs1) {
    let scrut, param0, param1, x, xs2, tmp, tmp1, tmp2, tmp3;
    scrut = NofibPrelude.force(xs1);
    if (scrut instanceof NofibPrelude.LzNil.class) {
      return NofibPrelude.lazy(lambda)
    } else if (scrut instanceof NofibPrelude.LzCons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      x = param0;
      xs2 = param1;
      tmp = lscomp1$1(x, xs2);
      tmp1 = knights.quickSortIntChessSet(tmp);
      tmp2 = runtime.safeCall(lambda5(x, xs2));
      tmp3 = NofibPrelude.lazy(tmp2);
      return NofibPrelude.append_lz_lz(tmp1, tmp3)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static sizeQueue(xs2) {
    return NofibPrelude.listLen(xs2)
  } 
  static emptyQueue(x) {
    return NofibPrelude.listEq(x, NofibPrelude.Nil)
  } 
  static removeBack(xs3) {
    let param0, param1, x1, xs4, x2, tmp;
    if (xs3 instanceof NofibPrelude.Cons.class) {
      param0 = xs3.head;
      param1 = xs3.tail;
      x2 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else {
        x1 = param0;
        xs4 = param1;
        tmp = knights.removeBack(xs4);
        return NofibPrelude.Cons(x1, tmp)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static removeFront(xs4) {
    let param0, param1, h, t;
    if (xs4 instanceof NofibPrelude.Cons.class) {
      param0 = xs4.head;
      param1 = xs4.tail;
      h = param0;
      t = param1;
      return t
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static inquireBack(xs5) {
    let param0, param1, x1, xs6, x2;
    if (xs5 instanceof NofibPrelude.Cons.class) {
      param0 = xs5.head;
      param1 = xs5.tail;
      x2 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return x2
      } else {
        x1 = param0;
        xs6 = param1;
        return knights.inquireBack(xs6)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static inquireFront(h_t) {
    return NofibPrelude.head(h_t)
  } 
  static addAllBack(list, q) {
    return NofibPrelude.append(q, list)
  } 
  static addAllFront(list1, q1) {
    return NofibPrelude.append(list1, q1)
  } 
  static addBack(x1, q2) {
    let tmp;
    tmp = NofibPrelude.Cons(x1, NofibPrelude.Nil);
    return NofibPrelude.append(q2, tmp)
  } 
  static addFront(x2, q3) {
    return NofibPrelude.Cons(x2, q3)
  } 
  static createBoard(x3, t) {
    let tmp, tmp1, lambda$this;
    lambda$this = runtime.safeCall(lambda6(t));
    tmp = NofibPrelude.lazy(lambda$this);
    tmp1 = NofibPrelude.Cons(t, NofibPrelude.Nil);
    return knights.Board(x3, 1, tmp, tmp1)
  } 
  static sizeBoard(b) {
    let param0, param1, param2, param3, a;
    if (b instanceof knights.Board.class) {
      param0 = b.a;
      param1 = b.b;
      param2 = b.c;
      param3 = b.d;
      a = param0;
      return a
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static noPieces(b1) {
    let param0, param1, param2, param3, n;
    if (b1 instanceof knights.Board.class) {
      param0 = b1.a;
      param1 = b1.b;
      param2 = b1.c;
      param3 = b1.d;
      n = param1;
      return n
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static addPiece(t1, b2) {
    let param0, param1, param2, param3, s, n, f, ts, tmp, tmp1;
    if (b2 instanceof knights.Board.class) {
      param0 = b2.a;
      param1 = b2.b;
      param2 = b2.c;
      param3 = b2.d;
      s = param0;
      n = param1;
      f = param2;
      ts = param3;
      tmp = n + 1;
      tmp1 = NofibPrelude.Cons(t1, ts);
      return knights.Board(s, tmp, f, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static deleteFirst(b3) {
    let param0, param1, param2, param3, s, n, f, ts, ts_, tmp, tmp1, tmp2, lambda$this;
    if (b3 instanceof knights.Board.class) {
      param0 = b3.a;
      param1 = b3.b;
      param2 = b3.c;
      param3 = b3.d;
      s = param0;
      n = param1;
      f = param2;
      ts = param3;
      tmp = knights.myInit(ts);
      ts_ = tmp;
      tmp1 = n - 1;
      lambda$this = runtime.safeCall(lambda7(ts_));
      tmp2 = NofibPrelude.lazy(lambda$this);
      return knights.Board(s, tmp1, tmp2, ts_)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static positionPiece(x4, b4) {
    let param0, param1, param2, param3, n, ts, tmp;
    if (b4 instanceof knights.Board.class) {
      param0 = b4.a;
      param1 = b4.b;
      param2 = b4.c;
      param3 = b4.d;
      n = param1;
      ts = param3;
      tmp = n - x4;
      return NofibPrelude.atIndex(tmp, ts)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static lastPiece(b5) {
    let param0, param1, param2, param3, param01, param11, t2, ts;
    if (b5 instanceof knights.Board.class) {
      param0 = b5.a;
      param1 = b5.b;
      param2 = b5.c;
      param3 = b5.d;
      if (param3 instanceof NofibPrelude.Cons.class) {
        param01 = param3.head;
        param11 = param3.tail;
        t2 = param01;
        ts = param11;
        return t2
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static firstPiece(b6) {
    let param0, param1, param2, param3, f;
    if (b6 instanceof knights.Board.class) {
      param0 = b6.a;
      param1 = b6.b;
      param2 = b6.c;
      param3 = b6.d;
      f = param2;
      return NofibPrelude.force(f)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static pieceAtTile(x5, b7) {
    let param0, param1, param2, param3, ts;
    if (b7 instanceof knights.Board.class) {
      param0 = b7.a;
      param1 = b7.b;
      param2 = b7.c;
      param3 = b7.d;
      ts = param3;
      return find(x5, ts)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static tup2InList(y, xs6) {
    let param0, param1, x6, xs7, scrut;
    if (xs6 instanceof NofibPrelude.Nil.class) {
      return false
    } else if (xs6 instanceof NofibPrelude.Cons.class) {
      param0 = xs6.head;
      param1 = xs6.tail;
      x6 = param0;
      xs7 = param1;
      scrut = NofibPrelude.eqTup2(y, x6);
      if (scrut === true) {
        return true
      } else {
        return knights.tup2InList(y, xs7)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static isSquareFree(x6, b8) {
    let param0, param1, param2, param3, ts, tmp;
    if (b8 instanceof knights.Board.class) {
      param0 = b8.a;
      param1 = b8.b;
      param2 = b8.c;
      param3 = b8.d;
      ts = param3;
      tmp = knights.tup2InList(x6, ts);
      return BenchmarkPrelude.not(tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static assignMoveNo(t2, size, z) {
    let param0, param1, first1, first0, x7, y1, t3, tmp, tmp1, tmp2, tmp3, tmp4;
    if (t2 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (t2 instanceof NofibPrelude.Cons.class) {
      param0 = t2.head;
      param1 = t2.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        x7 = first0;
        y1 = first1;
        t3 = param1;
        tmp = y1 - 1;
        tmp1 = tmp * size;
        tmp2 = tmp1 + x7;
        tmp3 = z - 1;
        tmp4 = knights.assignMoveNo(t3, size, tmp3);
        return NofibPrelude.Cons([
          tmp2,
          z
        ], tmp4)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static spaces(s, y1) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = logTen(s);
    tmp1 = logTen(y1);
    tmp2 = tmp - tmp1;
    tmp3 = tmp2 + 1;
    return NofibPrelude.replicate(tmp3, " ")
  } 
  static printBoard(s1, n, xs7) {
    let param0, param1, first1, first0, i, j, xs8, scrut, scrut1, scrut2, scrut3, scrut4, scrut5, scrut6, scrut7, scrut8, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75, tmp76, tmp77, tmp78, tmp79, tmp80, tmp81;
    if (xs7 instanceof NofibPrelude.Nil.class) {
      tmp = s1 * s1;
      scrut8 = n > tmp;
      if (scrut8 === true) {
        return NofibPrelude.Nil
      } else {
        tmp1 = NofibPrelude.intMod(n, s1);
        scrut7 = tmp1 != 0;
        if (scrut7 === true) {
          tmp2 = s1 * s1;
          tmp3 = knights.spaces(tmp2, 1);
          tmp4 = n + 1;
          tmp5 = knights.printBoard(s1, tmp4, NofibPrelude.Nil);
          tmp6 = NofibPrelude.append(tmp3, tmp5);
          return NofibPrelude.Cons("*", tmp6)
        } else {
          tmp7 = NofibPrelude.intMod(n, s1);
          scrut6 = tmp7 === 0;
          if (scrut6 === true) {
            tmp8 = NofibPrelude.nofibStringToList("*\n");
            tmp9 = n + 1;
            tmp10 = knights.printBoard(s1, tmp9, NofibPrelude.Nil);
            return NofibPrelude.append(tmp8, tmp10)
          } else {
            throw globalThis.Error("printBoard empty list error");
          }
        }
      }
    } else if (xs7 instanceof NofibPrelude.Cons.class) {
      param0 = xs7.head;
      param1 = xs7.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        i = first0;
        j = first1;
        xs8 = param1;
        scrut4 = i === n;
        if (scrut4 === true) {
          tmp11 = NofibPrelude.intMod(n, s1);
          scrut5 = tmp11 === 0;
          if (scrut5 === true) {
            tmp12 = NofibPrelude.stringOfInt(j);
            tmp13 = NofibPrelude.nofibStringToList(tmp12);
            tmp14 = NofibPrelude.nofibStringToList("\n");
            tmp15 = n + 1;
            tmp16 = knights.printBoard(s1, tmp15, xs8);
            tmp17 = NofibPrelude.append(tmp14, tmp16);
            return NofibPrelude.append(tmp13, tmp17)
          } else {
            scrut2 = i === n;
            if (scrut2 === true) {
              tmp18 = NofibPrelude.intMod(n, s1);
              scrut3 = tmp18 != 0;
              if (scrut3 === true) {
                tmp19 = NofibPrelude.stringOfInt(j);
                tmp20 = NofibPrelude.nofibStringToList(tmp19);
                tmp21 = s1 * s1;
                tmp22 = knights.spaces(tmp21, j);
                tmp23 = n + 1;
                tmp24 = knights.printBoard(s1, tmp23, xs8);
                tmp25 = NofibPrelude.append(tmp22, tmp24);
                return NofibPrelude.append(tmp20, tmp25)
              } else {
                tmp26 = NofibPrelude.intMod(n, s1);
                scrut1 = tmp26 != 0;
                if (scrut1 === true) {
                  tmp27 = s1 * s1;
                  tmp28 = knights.spaces(tmp27, 1);
                  tmp29 = n + 1;
                  tmp30 = NofibPrelude.Cons([
                    i,
                    j
                  ], xs8);
                  tmp31 = knights.printBoard(s1, tmp29, tmp30);
                  tmp32 = NofibPrelude.append(tmp28, tmp31);
                  return NofibPrelude.Cons("*", tmp32)
                } else {
                  tmp33 = NofibPrelude.intMod(n, s1);
                  scrut = tmp33 === 0;
                  if (scrut === true) {
                    tmp34 = NofibPrelude.nofibStringToList("*\n");
                    tmp35 = n + 1;
                    tmp36 = NofibPrelude.Cons([
                      i,
                      j
                    ], xs8);
                    tmp37 = knights.printBoard(s1, tmp35, tmp36);
                    return NofibPrelude.append(tmp34, tmp37)
                  } else {
                    throw globalThis.Error("printBoard non-empty list error");
                  }
                }
              }
            } else {
              tmp38 = NofibPrelude.intMod(n, s1);
              scrut1 = tmp38 != 0;
              if (scrut1 === true) {
                tmp39 = s1 * s1;
                tmp40 = knights.spaces(tmp39, 1);
                tmp41 = n + 1;
                tmp42 = NofibPrelude.Cons([
                  i,
                  j
                ], xs8);
                tmp43 = knights.printBoard(s1, tmp41, tmp42);
                tmp44 = NofibPrelude.append(tmp40, tmp43);
                return NofibPrelude.Cons("*", tmp44)
              } else {
                tmp45 = NofibPrelude.intMod(n, s1);
                scrut = tmp45 === 0;
                if (scrut === true) {
                  tmp46 = NofibPrelude.nofibStringToList("*\n");
                  tmp47 = n + 1;
                  tmp48 = NofibPrelude.Cons([
                    i,
                    j
                  ], xs8);
                  tmp49 = knights.printBoard(s1, tmp47, tmp48);
                  return NofibPrelude.append(tmp46, tmp49)
                } else {
                  throw globalThis.Error("printBoard non-empty list error");
                }
              }
            }
          }
        } else {
          scrut2 = i === n;
          if (scrut2 === true) {
            tmp50 = NofibPrelude.intMod(n, s1);
            scrut3 = tmp50 != 0;
            if (scrut3 === true) {
              tmp51 = NofibPrelude.stringOfInt(j);
              tmp52 = NofibPrelude.nofibStringToList(tmp51);
              tmp53 = s1 * s1;
              tmp54 = knights.spaces(tmp53, j);
              tmp55 = n + 1;
              tmp56 = knights.printBoard(s1, tmp55, xs8);
              tmp57 = NofibPrelude.append(tmp54, tmp56);
              return NofibPrelude.append(tmp52, tmp57)
            } else {
              tmp58 = NofibPrelude.intMod(n, s1);
              scrut1 = tmp58 != 0;
              if (scrut1 === true) {
                tmp59 = s1 * s1;
                tmp60 = knights.spaces(tmp59, 1);
                tmp61 = n + 1;
                tmp62 = NofibPrelude.Cons([
                  i,
                  j
                ], xs8);
                tmp63 = knights.printBoard(s1, tmp61, tmp62);
                tmp64 = NofibPrelude.append(tmp60, tmp63);
                return NofibPrelude.Cons("*", tmp64)
              } else {
                tmp65 = NofibPrelude.intMod(n, s1);
                scrut = tmp65 === 0;
                if (scrut === true) {
                  tmp66 = NofibPrelude.nofibStringToList("*\n");
                  tmp67 = n + 1;
                  tmp68 = NofibPrelude.Cons([
                    i,
                    j
                  ], xs8);
                  tmp69 = knights.printBoard(s1, tmp67, tmp68);
                  return NofibPrelude.append(tmp66, tmp69)
                } else {
                  throw globalThis.Error("printBoard non-empty list error");
                }
              }
            }
          } else {
            tmp70 = NofibPrelude.intMod(n, s1);
            scrut1 = tmp70 != 0;
            if (scrut1 === true) {
              tmp71 = s1 * s1;
              tmp72 = knights.spaces(tmp71, 1);
              tmp73 = n + 1;
              tmp74 = NofibPrelude.Cons([
                i,
                j
              ], xs8);
              tmp75 = knights.printBoard(s1, tmp73, tmp74);
              tmp76 = NofibPrelude.append(tmp72, tmp75);
              return NofibPrelude.Cons("*", tmp76)
            } else {
              tmp77 = NofibPrelude.intMod(n, s1);
              scrut = tmp77 === 0;
              if (scrut === true) {
                tmp78 = NofibPrelude.nofibStringToList("*\n");
                tmp79 = n + 1;
                tmp80 = NofibPrelude.Cons([
                  i,
                  j
                ], xs8);
                tmp81 = knights.printBoard(s1, tmp79, tmp80);
                return NofibPrelude.append(tmp78, tmp81)
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
  } 
  static move(d, x_y) {
    let first1, first0, x7, y2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15;
    if (globalThis.Array.isArray(x_y) && x_y.length === 2) {
      first0 = x_y[0];
      first1 = x_y[1];
      x7 = first0;
      y2 = first1;
      if (d instanceof knights.UL.class) {
        tmp = x7 - 1;
        tmp1 = y2 - 2;
        return [
          tmp,
          tmp1
        ]
      } else if (d instanceof knights.UR.class) {
        tmp2 = x7 + 1;
        tmp3 = y2 - 2;
        return [
          tmp2,
          tmp3
        ]
      } else if (d instanceof knights.DL.class) {
        tmp4 = x7 - 1;
        tmp5 = y2 + 2;
        return [
          tmp4,
          tmp5
        ]
      } else if (d instanceof knights.DR.class) {
        tmp6 = x7 + 1;
        tmp7 = y2 + 2;
        return [
          tmp6,
          tmp7
        ]
      } else if (d instanceof knights.LU.class) {
        tmp8 = x7 - 2;
        tmp9 = y2 - 1;
        return [
          tmp8,
          tmp9
        ]
      } else if (d instanceof knights.LD.class) {
        tmp10 = x7 - 2;
        tmp11 = y2 + 1;
        return [
          tmp10,
          tmp11
        ]
      } else if (d instanceof knights.RU.class) {
        tmp12 = x7 + 2;
        tmp13 = y2 - 1;
        return [
          tmp12,
          tmp13
        ]
      } else if (d instanceof knights.RD.class) {
        tmp14 = x7 + 2;
        tmp15 = y2 + 1;
        return [
          tmp14,
          tmp15
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static startTour(st, size1) {
    let scrut, tmp;
    tmp = NofibPrelude.intMod(size1, 2);
    scrut = tmp === 0;
    if (scrut === true) {
      return knights.createBoard(size1, st)
    } else {
      throw globalThis.Error("Tour doesnt exist for odd size board");
    }
  } 
  static moveKnight(board, dir) {
    let tmp, tmp1;
    tmp = knights.lastPiece(board);
    tmp1 = knights.move(dir, tmp);
    return knights.addPiece(tmp1, board)
  } 
  static canMoveTo(x_y1, board1) {
    let first1, first0, x7, y2, sze, res, scrut, scrut1, scrut2, scrut3, scrut4, tmp, tmp1;
    if (globalThis.Array.isArray(x_y1) && x_y1.length === 2) {
      first0 = x_y1[0];
      first1 = x_y1[1];
      x7 = first0;
      y2 = first1;
      tmp = knights.sizeBoard(board1);
      sze = tmp;
      scrut = x7 >= 1;
      if (scrut === true) {
        scrut1 = x7 <= sze;
        if (scrut1 === true) {
          scrut2 = y2 >= 1;
          if (scrut2 === true) {
            scrut3 = y2 <= sze;
            if (scrut3 === true) {
              scrut4 = knights.isSquareFree(x_y1, board1);
              if (scrut4 === true) {
                tmp1 = true;
              } else {
                tmp1 = false;
              }
            } else {
              tmp1 = false;
            }
          } else {
            tmp1 = false;
          }
        } else {
          tmp1 = false;
        }
      } else {
        tmp1 = false;
      }
      res = tmp1;
      return res
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static canMove(board2, dir1) {
    let tmp, tmp1;
    tmp = knights.lastPiece(board2);
    tmp1 = knights.move(dir1, tmp);
    return knights.canMoveTo(tmp1, board2)
  } 
  static canJumpFirst(board3) {
    let tmp, tmp1;
    tmp = knights.firstPiece(board3);
    tmp1 = knights.deleteFirst(board3);
    return knights.canMoveTo(tmp, tmp1)
  } 
  static tourFinished(board4) {
    let sze, tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = knights.sizeBoard(board4);
    sze = tmp;
    tmp1 = knights.noPieces(board4);
    tmp2 = sze * sze;
    tmp3 = tmp1 === tmp2;
    tmp4 = knights.canJumpFirst(board4);
    return tmp3 && tmp4
  } 
  static possibleMoves(board5) {
    let res, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    tmp = NofibPrelude.Cons(knights.RD, NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons(knights.RU, tmp);
    tmp2 = NofibPrelude.Cons(knights.LD, tmp1);
    tmp3 = NofibPrelude.Cons(knights.LU, tmp2);
    tmp4 = NofibPrelude.Cons(knights.DR, tmp3);
    tmp5 = NofibPrelude.Cons(knights.DL, tmp4);
    tmp6 = NofibPrelude.Cons(knights.UR, tmp5);
    tmp7 = NofibPrelude.Cons(knights.UL, tmp6);
    tmp8 = lscomp$(board5, tmp7);
    res = tmp8;
    return res
  } 
  static deadEnd(board6) {
    let tmp, tmp1;
    tmp = knights.possibleMoves(board6);
    tmp1 = NofibPrelude.listLen(tmp);
    return tmp1 === 0
  } 
  static allDescend(board7) {
    let tmp, lambda$this;
    tmp = knights.possibleMoves(board7);
    lambda$this = runtime.safeCall(lambda8(board7));
    return NofibPrelude.map(lambda$this, tmp)
  } 
  static descAndNo(board8) {
    let tmp;
    tmp = knights.allDescend(board8);
    return lscomp3(tmp)
  } 
  static singleDescend(board9) {
    let tmp;
    tmp = knights.descAndNo(board9);
    return lscomp4(tmp)
  } 
  static descendents(board10) {
    let singles, scrut, res, scrut1, param0, param1, h, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, lambda$this;
    tmp = knights.canJumpFirst(board10);
    tmp1 = knights.firstPiece(board10);
    tmp2 = knights.addPiece(tmp1, board10);
    tmp3 = knights.deadEnd(tmp2);
    scrut3 = tmp && tmp3;
    if (scrut3 === true) {
      return NofibPrelude.lazy(lambda11)
    } else {
      tmp4 = knights.singleDescend(board10);
      singles = tmp4;
      tmp5 = NofibPrelude.listLen(singles);
      scrut = tmp5;
      scrut2 = scrut === 0;
      if (scrut2 === true) {
        tmp6 = knights.descAndNo(board10);
        tmp7 = knights.quickSortIntChessSet(tmp6);
        tmp8 = NofibPrelude.map_lz(NofibPrelude.snd, tmp7);
      } else {
        scrut1 = scrut === 1;
        if (scrut1 === true) {
          if (singles instanceof NofibPrelude.Cons.class) {
            param0 = singles.head;
            param1 = singles.tail;
            h = param0;
            if (param1 instanceof NofibPrelude.Nil.class) {
              lambda$this = runtime.safeCall(lambda12(h));
              tmp9 = NofibPrelude.lazy(lambda$this);
            } else {
              throw globalThis.Error("unreachable");
            }
          } else {
            throw globalThis.Error("unreachable");
          }
          tmp8 = tmp9;
        } else {
          tmp8 = NofibPrelude.lazy(lambda14);
        }
      }
      res = tmp8;
      return res
    }
  } 
  static showChessSet(b9) {
    let param0, param1, param2, param3, sze, n1, f, ts, sortedTrail, tmp, tmp1;
    if (b9 instanceof knights.Board.class) {
      param0 = b9.a;
      param1 = b9.b;
      param2 = b9.c;
      param3 = b9.d;
      sze = param0;
      n1 = param1;
      f = param2;
      ts = param3;
      tmp = knights.assignMoveNo(ts, sze, n1);
      tmp1 = knights.quickSortIntInt(tmp);
      sortedTrail = tmp1;
      return knights.printBoard(sze, 1, sortedTrail)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static root(sze) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    tmp = sze * sze;
    tmp1 = 1 - tmp;
    tmp2 = NofibPrelude.repeat(tmp1);
    tmp3 = NofibPrelude.enumFromTo(1, sze);
    tmp4 = lscomp1$2(sze, tmp3);
    tmp5 = sze * sze;
    tmp6 = NofibPrelude.replicate_lz(tmp5, sze);
    tmp7 = NofibPrelude.zipWith_lz_lz(knights.startTour, tmp4, tmp6);
    tmp8 = NofibPrelude.zip_lz_lz(tmp2, tmp7);
    tmp9 = NofibPrelude.lazy(lambda17);
    return NofibPrelude.append_lz_lz(tmp8, tmp9)
  } 
  static grow(x_y2) {
    let first1, first0, x7, y2, tmp, tmp1, tmp2;
    if (globalThis.Array.isArray(x_y2) && x_y2.length === 2) {
      first0 = x_y2[0];
      first1 = x_y2[1];
      x7 = first0;
      y2 = first1;
      tmp = x7 + 1;
      tmp1 = NofibPrelude.repeat(tmp);
      tmp2 = knights.descendents(y2);
      return NofibPrelude.zip_lz_lz(tmp1, tmp2)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static isFinished(x_y3) {
    let first1, first0, x7, y2;
    if (globalThis.Array.isArray(x_y3) && x_y3.length === 2) {
      first0 = x_y3[0];
      first1 = x_y3[1];
      x7 = first0;
      y2 = first1;
      return knights.tourFinished(y2)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static emptyQueue_lz(x7) {
    let scrut;
    scrut = NofibPrelude.force(x7);
    if (scrut instanceof NofibPrelude.LzNil.class) {
      return true
    } else {
      return false
    }
  } 
  static removeFront_lz(xs8) {
    let scrut, param0, param1, h, t3;
    scrut = NofibPrelude.force(xs8);
    if (scrut instanceof NofibPrelude.LzCons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      h = param0;
      t3 = param1;
      return t3
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static inquireFront_lz(h_t1) {
    let scrut, param0, param1, h, t3;
    scrut = NofibPrelude.force(h_t1);
    if (scrut instanceof NofibPrelude.LzCons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      h = param0;
      t3 = param1;
      return h
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static addAllFront_lz(list2, q4) {
    return NofibPrelude.append_lz_lz(list2, q4)
  } 
  static depthSearch(q5, growFn, finFn) {
    let scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    scrut1 = knights.emptyQueue_lz(q5);
    if (scrut1 === true) {
      return NofibPrelude.lazy(lambda18)
    } else {
      tmp = knights.inquireFront_lz(q5);
      scrut = runtime.safeCall(finFn(tmp));
      if (scrut === true) {
        tmp1 = runtime.safeCall(lambda19(q5, growFn, finFn));
        return NofibPrelude.lazy(tmp1)
      } else {
        tmp2 = knights.inquireFront_lz(q5);
        tmp3 = runtime.safeCall(growFn(tmp2));
        tmp4 = knights.removeFront_lz(q5);
        tmp5 = knights.addAllFront_lz(tmp3, tmp4);
        return knights.depthSearch(tmp5, growFn, finFn)
      }
    }
  } 
  static printTour(ss) {
    let scrut, param0, param1, size2, param01, param11, number, tmp, tmp1, tmp2;
    scrut = NofibPrelude.map(lambda20, ss);
    if (scrut instanceof NofibPrelude.Cons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      size2 = param0;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        number = param01;
        if (param11 instanceof NofibPrelude.Nil.class) {
          tmp = knights.root(size2);
          tmp1 = knights.depthSearch(tmp, knights.grow, knights.isFinished);
          tmp2 = NofibPrelude.take_lz(number, tmp1);
          return pp(tmp2)
        } else {
          throw globalThis.Error("printTour error");
        }
      } else {
        throw globalThis.Error("printTour error");
      }
    } else {
      throw globalThis.Error("printTour error");
    }
  } 
  static testKnights_nofib(ss1) {
    let usageString, scrut;
    usageString = "\nUsage: knights <board size> <no solutions> \n";
    scrut = argsOk(ss1);
    if (scrut === true) {
      return knights.printTour(ss1)
    } else {
      throw globalThis.Error(usageString);
    }
  }
  static toString() { return "knights"; }
};
let knights = knights1; export default knights;
