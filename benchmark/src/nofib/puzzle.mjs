import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let minAcc, lscomp3, lscomp2, lscomp1, puzzle1, lambda, lambda1, lambda2, lambda3, lambda$, lambda$1, lambda$2, lscomp2$, lscomp3$, lscomp1$;
lscomp1$ = function lscomp1$(source, dest, location, countdown, history, newHistory, newLocation, ls) {
  let param0, param1, item, xs, scrut, newDest, scrut1, newTime, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    item = param0;
    xs = param1;
    tmp = puzzle1.position(item, dest);
    scrut = puzzle1.bankEq(tmp, location);
    if (scrut === true) {
      tmp1 = puzzle1.updateState(dest, item, newLocation);
      newDest = tmp1;
      scrut1 = puzzle1.notSeen(newDest, history);
      if (scrut1 === true) {
        tmp2 = puzzle1.u2times(item);
        tmp3 = countdown + tmp2;
        newTime = tmp3;
        tmp4 = puzzle1.transfer(source, newDest, newLocation, newTime, newHistory);
        tmp5 = lscomp1$(source, dest, location, countdown, history, newHistory, newLocation, xs);
        return NofibPrelude.Cons(tmp4, tmp5)
      } else {
        return lscomp1$(source, dest, location, countdown, history, newHistory, newLocation, xs)
      }
    } else {
      return lscomp1$(source, dest, location, countdown, history, newHistory, newLocation, xs)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp1 = function lscomp1(source, dest, location, countdown, history, newHistory, newLocation) {
  return (ls) => {
    return lscomp1$(source, dest, location, countdown, history, newHistory, newLocation, ls)
  }
};
lscomp3$ = function lscomp3$(source, dest, location, countdown, history, newHistory, newLocation, i, xs, ls) {
  let param0, param1, j, ys, scrut, scrut1, newDest, scrut2, newTime, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  if (ls instanceof NofibPrelude.Nil.class) {
    return lscomp2$(source, dest, location, countdown, history, newHistory, newLocation, xs)
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    j = param0;
    ys = param1;
    tmp = puzzle1.position(i, dest);
    scrut = puzzle1.bankEq(tmp, location);
    if (scrut === true) {
      tmp1 = puzzle1.position(j, dest);
      scrut1 = puzzle1.bankEq(tmp1, location);
      if (scrut1 === true) {
        tmp2 = puzzle1.updateState(dest, i, newLocation);
        tmp3 = puzzle1.updateState(tmp2, j, newLocation);
        newDest = tmp3;
        scrut2 = puzzle1.notSeen(newDest, history);
        if (scrut2 === true) {
          tmp4 = puzzle1.u2times(i);
          tmp5 = countdown + tmp4;
          newTime = tmp5;
          tmp6 = puzzle1.transfer(source, newDest, newLocation, newTime, newHistory);
          tmp7 = lscomp3$(source, dest, location, countdown, history, newHistory, newLocation, i, xs, ys);
          return NofibPrelude.Cons(tmp6, tmp7)
        } else {
          return lscomp3$(source, dest, location, countdown, history, newHistory, newLocation, i, xs, ys)
        }
      } else {
        return lscomp3$(source, dest, location, countdown, history, newHistory, newLocation, i, xs, ys)
      }
    } else {
      return lscomp3$(source, dest, location, countdown, history, newHistory, newLocation, i, xs, ys)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp3 = function lscomp3(source, dest, location, countdown, history, newHistory, newLocation, i, xs) {
  return (ls) => {
    return lscomp3$(source, dest, location, countdown, history, newHistory, newLocation, i, xs, ls)
  }
};
lscomp2$ = function lscomp2$(source, dest, location, countdown, history, newHistory, newLocation, ls) {
  let param0, param1, i, xs, tmp, tmp1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    i = param0;
    xs = param1;
    tmp = puzzle1.succItem(i);
    tmp1 = puzzle1.itemFromTo(tmp, puzzle1.Adam);
    return lscomp3$(source, dest, location, countdown, history, newHistory, newLocation, i, xs, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp2 = function lscomp2(source, dest, location, countdown, history, newHistory, newLocation) {
  return (ls) => {
    return lscomp2$(source, dest, location, countdown, history, newHistory, newLocation, ls)
  }
};
minAcc = function minAcc(minSoFar, mins, ls) {
  let param0, param1, history, next, total, scrut, scrut1, tmp, tmp1, tmp2;
  if (ls instanceof NofibPrelude.Nil.class) {
    return mins
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    history = param0;
    next = param1;
    tmp = puzzle1.totalTime(history);
    total = tmp;
    scrut1 = minSoFar < total;
    if (scrut1 === true) {
      return minAcc(minSoFar, mins, next)
    } else {
      scrut = minSoFar === total;
      if (scrut === true) {
        tmp1 = NofibPrelude.Cons(history, mins);
        return minAcc(minSoFar, tmp1, next)
      } else {
        tmp2 = NofibPrelude.Cons(history, NofibPrelude.Nil);
        return minAcc(total, tmp2, next)
      }
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$2 = function lambda$(history, timestate, acc, s) {
  let first1, first0, time, state, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
  if (globalThis.Array.isArray(timestate) && timestate.length === 2) {
    first0 = timestate[0];
    first1 = timestate[1];
    time = first0;
    state = first1;
    tmp = NofibPrelude.nofibStringToList("Time: ");
    tmp1 = puzzle1.totalTime(history);
    tmp2 = tmp1 - time;
    tmp3 = NofibPrelude.stringOfInt(tmp2);
    tmp4 = NofibPrelude.nofibStringToList(tmp3);
    tmp5 = runtime.safeCall(acc(s));
    tmp6 = puzzle1.writeState(state, tmp5);
    tmp7 = NofibPrelude.Cons("\n", tmp6);
    tmp8 = NofibPrelude.append(tmp4, tmp7);
    return NofibPrelude.append(tmp, tmp8)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda3 = (undefined, function (history, timestate, acc) {
  return (s) => {
    return lambda$2(history, timestate, acc, s)
  }
});
lambda$1 = function lambda$(history, timestate, acc) {
  return runtime.safeCall(lambda3(history, timestate, acc))
};
lambda1 = (undefined, function (history) {
  return (timestate, acc) => {
    return lambda$1(history, timestate, acc)
  }
});
lambda2 = (undefined, function (x) {
  return x
});
lambda$ = function lambda$(state, caseScrut) {
  let first1, first0, s, tmp;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    s = first1;
    tmp = puzzle1.stateEq(state, s);
    return BenchmarkPrelude.not(tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda = (undefined, function (state) {
  return (caseScrut) => {
    return lambda$(state, caseScrut)
  }
});
puzzle1 = class puzzle {
  static {
    puzzle1 = puzzle;
    let tmp, tmp1, tmp2, lambda4;
    this.ItemType = class ItemType {
      constructor() {}
      toString() { return "ItemType"; }
    };
    const Bono$class = class Bono extends puzzle.ItemType {
      constructor() {
        super();
      }
      toString() { return "Bono"; }
    };
    this.Bono = new Bono$class;
    this.Bono.class = Bono$class;
    const Edge$class = class Edge extends puzzle.ItemType {
      constructor() {
        super();
      }
      toString() { return "Edge"; }
    };
    this.Edge = new Edge$class;
    this.Edge.class = Edge$class;
    const Larry$class = class Larry extends puzzle.ItemType {
      constructor() {
        super();
      }
      toString() { return "Larry"; }
    };
    this.Larry = new Larry$class;
    this.Larry.class = Larry$class;
    const Adam$class = class Adam extends puzzle.ItemType {
      constructor() {
        super();
      }
      toString() { return "Adam"; }
    };
    this.Adam = new Adam$class;
    this.Adam.class = Adam$class;
    this.BankType = class BankType {
      constructor() {}
      toString() { return "BankType"; }
    };
    const LeftBank$class = class LeftBank extends puzzle.BankType {
      constructor() {
        super();
      }
      toString() { return "LeftBank"; }
    };
    this.LeftBank = new LeftBank$class;
    this.LeftBank.class = LeftBank$class;
    const RightBank$class = class RightBank extends puzzle.BankType {
      constructor() {
        super();
      }
      toString() { return "RightBank"; }
    };
    this.RightBank = new RightBank$class;
    this.RightBank.class = RightBank$class;
    this.State = function State(b1, e1, l1, a1) {
      return new State.class(b1, e1, l1, a1);
    };
    this.State.class = class State {
      constructor(b, e, l, a) {
        this.b = b;
        this.e = e;
        this.l = l;
        this.a = a;
      }
      toString() { return "State(" + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.e) + ", " + globalThis.Predef.render(this.l) + ", " + globalThis.Predef.render(this.a) + ")"; }
    };
    tmp = puzzle.State(puzzle.LeftBank, puzzle.LeftBank, puzzle.LeftBank, puzzle.LeftBank);
    this.initialState = tmp;
    tmp1 = puzzle.State(puzzle.RightBank, puzzle.RightBank, puzzle.RightBank, puzzle.RightBank);
    this.finalState = tmp1;
    lambda4 = (undefined, function () {
      let tmp3, tmp4, tmp5;
      tmp3 = NofibPrelude.Cons(2, NofibPrelude.Nil);
      tmp4 = puzzle.testPuzzle_nofib(tmp3);
      tmp5 = NofibPrelude.nofibListToString(tmp4);
      return BenchmarkPrelude.print(tmp5)
    });
    tmp2 = lambda4;
    BenchmarkPrelude.benchmark(tmp2)
  }
  static itemEq(a, b) {
    if (a instanceof puzzle.Bono.class) {
      if (b instanceof puzzle.Bono.class) {
        return true
      } else {
        return false
      }
    } else if (a instanceof puzzle.Edge.class) {
      if (b instanceof puzzle.Edge.class) {
        return true
      } else {
        return false
      }
    } else if (a instanceof puzzle.Larry.class) {
      if (b instanceof puzzle.Larry.class) {
        return true
      } else {
        return false
      }
    } else if (a instanceof puzzle.Adam.class) {
      if (b instanceof puzzle.Adam.class) {
        return true
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static succItem(i) {
    if (i instanceof puzzle.Bono.class) {
      return puzzle.Edge
    } else if (i instanceof puzzle.Edge.class) {
      return puzzle.Larry
    } else if (i instanceof puzzle.Larry.class) {
      return puzzle.Adam
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static isEnd(i1) {
    if (i1 instanceof puzzle.Bono.class) {
      return false
    } else if (i1 instanceof puzzle.Edge.class) {
      return false
    } else if (i1 instanceof puzzle.Larry.class) {
      return false
    } else if (i1 instanceof puzzle.Adam.class) {
      return true
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static itemFromTo(a1, b1) {
    let scrut, tmp, tmp1;
    scrut = puzzle.itemEq(a1, b1);
    if (scrut === true) {
      return NofibPrelude.Cons(a1, NofibPrelude.Nil)
    } else {
      tmp = puzzle.succItem(a1);
      tmp1 = puzzle.itemFromTo(tmp, b1);
      return NofibPrelude.Cons(a1, tmp1)
    }
  } 
  static bankEq(a2, b2) {
    if (a2 instanceof puzzle.LeftBank.class) {
      if (b2 instanceof puzzle.LeftBank.class) {
        return true
      } else {
        return false
      }
    } else if (a2 instanceof puzzle.RightBank.class) {
      if (b2 instanceof puzzle.RightBank.class) {
        return true
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static stateEq(s1, s2) {
    let param0, param1, param2, param3, a3, b3, c, d, param01, param11, param21, param31, e, f, g, h, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    if (s1 instanceof puzzle.State.class) {
      param0 = s1.b;
      param1 = s1.e;
      param2 = s1.l;
      param3 = s1.a;
      a3 = param0;
      b3 = param1;
      c = param2;
      d = param3;
      if (s2 instanceof puzzle.State.class) {
        param01 = s2.b;
        param11 = s2.e;
        param21 = s2.l;
        param31 = s2.a;
        e = param01;
        f = param11;
        g = param21;
        h = param31;
        tmp = puzzle.bankEq(a3, e);
        tmp1 = puzzle.bankEq(b3, f);
        tmp2 = tmp && tmp1;
        tmp3 = puzzle.bankEq(c, g);
        tmp4 = tmp2 && tmp3;
        tmp5 = puzzle.bankEq(d, h);
        return tmp4 && tmp5
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static bonoPos(s) {
    let param0, param1, param2, param3, a3, b3, c, d;
    if (s instanceof puzzle.State.class) {
      param0 = s.b;
      param1 = s.e;
      param2 = s.l;
      param3 = s.a;
      a3 = param0;
      b3 = param1;
      c = param2;
      d = param3;
      return a3
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static edgePos(s3) {
    let param0, param1, param2, param3, a3, b3, c, d;
    if (s3 instanceof puzzle.State.class) {
      param0 = s3.b;
      param1 = s3.e;
      param2 = s3.l;
      param3 = s3.a;
      a3 = param0;
      b3 = param1;
      c = param2;
      d = param3;
      return b3
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static larryPos(s4) {
    let param0, param1, param2, param3, a3, b3, c, d;
    if (s4 instanceof puzzle.State.class) {
      param0 = s4.b;
      param1 = s4.e;
      param2 = s4.l;
      param3 = s4.a;
      a3 = param0;
      b3 = param1;
      c = param2;
      d = param3;
      return c
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static adamPos(s5) {
    let param0, param1, param2, param3, a3, b3, c, d;
    if (s5 instanceof puzzle.State.class) {
      param0 = s5.b;
      param1 = s5.e;
      param2 = s5.l;
      param3 = s5.a;
      a3 = param0;
      b3 = param1;
      c = param2;
      d = param3;
      return d
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static position(i2, s6) {
    if (i2 instanceof puzzle.Bono.class) {
      return puzzle.bonoPos(s6)
    } else if (i2 instanceof puzzle.Edge.class) {
      return puzzle.edgePos(s6)
    } else if (i2 instanceof puzzle.Larry.class) {
      return puzzle.larryPos(s6)
    } else if (i2 instanceof puzzle.Adam.class) {
      return puzzle.adamPos(s6)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static updateState(s7, i3, pos) {
    let param0, param1, param2, param3, a3, b3, c, d;
    if (s7 instanceof puzzle.State.class) {
      param0 = s7.b;
      param1 = s7.e;
      param2 = s7.l;
      param3 = s7.a;
      a3 = param0;
      b3 = param1;
      c = param2;
      d = param3;
      if (i3 instanceof puzzle.Bono.class) {
        return puzzle.State(pos, b3, c, d)
      } else if (i3 instanceof puzzle.Edge.class) {
        return puzzle.State(a3, pos, c, d)
      } else if (i3 instanceof puzzle.Larry.class) {
        return puzzle.State(a3, b3, pos, d)
      } else if (i3 instanceof puzzle.Adam.class) {
        return puzzle.State(a3, b3, c, pos)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static opposite(b3) {
    if (b3 instanceof puzzle.LeftBank.class) {
      return puzzle.RightBank
    } else if (b3 instanceof puzzle.RightBank.class) {
      return puzzle.LeftBank
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static notSeen(state, states) {
    let tmp;
    tmp = runtime.safeCall(lambda(state));
    return NofibPrelude.all(tmp, states)
  } 
  static writeItem(i4, b4, rest) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    if (i4 instanceof puzzle.Bono.class) {
      if (b4 instanceof puzzle.LeftBank.class) {
        tmp = NofibPrelude.nofibStringToList("    Bono |                    |\n");
        return NofibPrelude.append(tmp, rest)
      } else if (b4 instanceof puzzle.RightBank.class) {
        tmp1 = NofibPrelude.nofibStringToList("         |                    | Bono\n");
        return NofibPrelude.append(tmp1, rest)
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (i4 instanceof puzzle.Edge.class) {
      if (b4 instanceof puzzle.LeftBank.class) {
        tmp2 = NofibPrelude.nofibStringToList("The Edge |                    |\n");
        return NofibPrelude.append(tmp2, rest)
      } else if (b4 instanceof puzzle.RightBank.class) {
        tmp3 = NofibPrelude.nofibStringToList("         |                    | The Edge\n");
        return NofibPrelude.append(tmp3, rest)
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (i4 instanceof puzzle.Larry.class) {
      if (b4 instanceof puzzle.LeftBank.class) {
        tmp4 = NofibPrelude.nofibStringToList("   Larry |                    |\n");
        return NofibPrelude.append(tmp4, rest)
      } else if (b4 instanceof puzzle.RightBank.class) {
        tmp5 = NofibPrelude.nofibStringToList("         |                    | Larry\n");
        return NofibPrelude.append(tmp5, rest)
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (i4 instanceof puzzle.Adam.class) {
      if (b4 instanceof puzzle.LeftBank.class) {
        tmp6 = NofibPrelude.nofibStringToList("    Adam |                    |\n");
        return NofibPrelude.append(tmp6, rest)
      } else if (b4 instanceof puzzle.RightBank.class) {
        tmp7 = NofibPrelude.nofibStringToList("         |                    | Adam\n");
        return NofibPrelude.append(tmp7, rest)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static writeState(state1, s8) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10;
    tmp = NofibPrelude.nofibStringToList("----------------------------------------\n");
    tmp1 = puzzle.bonoPos(state1);
    tmp2 = puzzle.edgePos(state1);
    tmp3 = puzzle.larryPos(state1);
    tmp4 = puzzle.adamPos(state1);
    tmp5 = NofibPrelude.nofibStringToList("----------------------------------------\n");
    tmp6 = NofibPrelude.append(tmp5, s8);
    tmp7 = puzzle.writeItem(puzzle.Adam, tmp4, tmp6);
    tmp8 = puzzle.writeItem(puzzle.Larry, tmp3, tmp7);
    tmp9 = puzzle.writeItem(puzzle.Edge, tmp2, tmp8);
    tmp10 = puzzle.writeItem(puzzle.Bono, tmp1, tmp9);
    return NofibPrelude.append(tmp, tmp10)
  } 
  static totalTime(history) {
    let param0, param1, first1, first0, time;
    if (history instanceof NofibPrelude.Cons.class) {
      param0 = history.head;
      param1 = history.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        time = first0;
        return time
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static writeHistory(history1, x) {
    let tmp, lambda$this;
    if (history1 instanceof NofibPrelude.Nil.class) {
      return x
    } else {
      lambda$this = runtime.safeCall(lambda1(history1));
      tmp = NofibPrelude.foldr(lambda$this, lambda2, history1);
      return runtime.safeCall(tmp(x))
    }
  } 
  static writeSolutions(solutions, count, s9) {
    let param0, param1, item, next, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    if (solutions instanceof NofibPrelude.Nil.class) {
      return s9
    } else if (solutions instanceof NofibPrelude.Cons.class) {
      param0 = solutions.head;
      param1 = solutions.tail;
      item = param0;
      next = param1;
      tmp = NofibPrelude.nofibStringToList("Solution ");
      tmp1 = NofibPrelude.stringOfInt(count);
      tmp2 = NofibPrelude.nofibStringToList(tmp1);
      tmp3 = count + 1;
      tmp4 = puzzle.writeSolutions(next, tmp3, s9);
      tmp5 = puzzle.writeHistory(item, tmp4);
      tmp6 = NofibPrelude.Cons("\n", tmp5);
      tmp7 = NofibPrelude.append(tmp2, tmp6);
      return NofibPrelude.append(tmp, tmp7)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static minSolutions(history2) {
    let param0, param1, history3, next, tmp, tmp1, tmp2;
    if (history2 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (history2 instanceof NofibPrelude.Cons.class) {
      param0 = history2.head;
      param1 = history2.tail;
      history3 = param0;
      next = param1;
      tmp = puzzle.totalTime(history3);
      tmp1 = NofibPrelude.Cons(history3, NofibPrelude.Nil);
      tmp2 = minAcc(tmp, tmp1, next);
      return NofibPrelude.reverse(tmp2)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static u2times(i5) {
    if (i5 instanceof puzzle.Bono.class) {
      return 10
    } else if (i5 instanceof puzzle.Edge.class) {
      return 5
    } else if (i5 instanceof puzzle.Larry.class) {
      return 2
    } else if (i5 instanceof puzzle.Adam.class) {
      return 1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static transfer(source, dest, location, countdown, history3) {
    let newHistory, newLocation, moveOne, moveTwo, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    scrut = puzzle.stateEq(source, dest);
    if (scrut === true) {
      tmp = NofibPrelude.Cons([
        countdown,
        dest
      ], history3);
      return NofibPrelude.Cons(tmp, NofibPrelude.Nil)
    } else {
      tmp1 = NofibPrelude.Cons([
        countdown,
        dest
      ], history3);
      newHistory = tmp1;
      tmp2 = puzzle.opposite(location);
      newLocation = tmp2;
      tmp3 = puzzle.itemFromTo(puzzle.Bono, puzzle.Adam);
      tmp4 = lscomp1$(source, dest, location, countdown, history3, newHistory, newLocation, tmp3);
      tmp5 = NofibPrelude.concat(tmp4);
      moveOne = tmp5;
      tmp6 = puzzle.itemFromTo(puzzle.Bono, puzzle.Larry);
      tmp7 = lscomp2$(source, dest, location, countdown, history3, newHistory, newLocation, tmp6);
      tmp8 = NofibPrelude.concat(tmp7);
      moveTwo = tmp8;
      return NofibPrelude.append(moveOne, moveTwo)
    }
  } 
  static testPuzzle_nofib(x1) {
    let time, scrut, solutions1, mins, tmp, tmp1, tmp2, tmp3;
    tmp = NofibPrelude.listLen(x1);
    scrut = tmp === 1;
    if (scrut === true) {
      tmp1 = 0;
    } else {
      throw globalThis.Error("puzzle expects exactly one argument");
    }
    time = tmp1;
    tmp2 = puzzle.transfer(puzzle.initialState, puzzle.finalState, puzzle.RightBank, time, NofibPrelude.Nil);
    solutions1 = tmp2;
    tmp3 = puzzle.minSolutions(solutions1);
    mins = tmp3;
    return puzzle.writeSolutions(mins, 1, NofibPrelude.Nil)
  }
  static toString() { return "puzzle"; }
};
let puzzle = puzzle1; export default puzzle;
