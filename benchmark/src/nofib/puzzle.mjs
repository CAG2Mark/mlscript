import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let u2times, succItem, stateEq, minSolutions, writeSolutions, RightBank1, opposite, itemFromTo, larryPos, testPuzzle_nofib, LeftBank1, isEnd, writeState, bankEq, notSeen, bonoPos, updateState, transfer, edgePos, Larry1, Adam1, Bono1, BankType1, writeHistory, writeItem, position, ItemType1, itemEq, Edge1, State1, adamPos, totalTime, initialState, finalState, tmp, tmp1, tmp2, lambda;
itemEq = function itemEq(a, b) {
  if (a instanceof Bono1.class) {
    if (b instanceof Bono1.class) {
      return true
    } else {
      return false
    }
  } else if (a instanceof Edge1.class) {
    if (b instanceof Edge1.class) {
      return true
    } else {
      return false
    }
  } else if (a instanceof Larry1.class) {
    if (b instanceof Larry1.class) {
      return true
    } else {
      return false
    }
  } else if (a instanceof Adam1.class) {
    if (b instanceof Adam1.class) {
      return true
    } else {
      return false
    }
  } else {
    return false
  }
};
succItem = function succItem(i) {
  if (i instanceof Bono1.class) {
    return Edge1
  } else if (i instanceof Edge1.class) {
    return Larry1
  } else if (i instanceof Larry1.class) {
    return Adam1
  } else {
    throw new globalThis.Error("match error");
  }
};
isEnd = function isEnd(i) {
  if (i instanceof Bono1.class) {
    return false
  } else if (i instanceof Edge1.class) {
    return false
  } else if (i instanceof Larry1.class) {
    return false
  } else if (i instanceof Adam1.class) {
    return true
  } else {
    throw new globalThis.Error("match error");
  }
};
itemFromTo = function itemFromTo(a, b) {
  let scrut, tmp3, tmp4;
  scrut = itemEq(a, b);
  if (scrut === true) {
    return NofibPrelude.Cons(a, NofibPrelude.Nil)
  } else {
    tmp3 = succItem(a);
    tmp4 = itemFromTo(tmp3, b);
    return NofibPrelude.Cons(a, tmp4)
  }
};
bankEq = function bankEq(a, b) {
  if (a instanceof LeftBank1.class) {
    if (b instanceof LeftBank1.class) {
      return true
    } else {
      return false
    }
  } else if (a instanceof RightBank1.class) {
    if (b instanceof RightBank1.class) {
      return true
    } else {
      return false
    }
  } else {
    return false
  }
};
stateEq = function stateEq(s1, s2) {
  let param0, param1, param2, param3, a, b, c, d, param01, param11, param21, param31, e, f, g, h, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
  if (s1 instanceof State1.class) {
    param0 = s1.b;
    param1 = s1.e;
    param2 = s1.l;
    param3 = s1.a;
    a = param0;
    b = param1;
    c = param2;
    d = param3;
    if (s2 instanceof State1.class) {
      param01 = s2.b;
      param11 = s2.e;
      param21 = s2.l;
      param31 = s2.a;
      e = param01;
      f = param11;
      g = param21;
      h = param31;
      tmp3 = bankEq(a, e);
      tmp4 = bankEq(b, f);
      tmp5 = tmp3 && tmp4;
      tmp6 = bankEq(c, g);
      tmp7 = tmp5 && tmp6;
      tmp8 = bankEq(d, h);
      return tmp7 && tmp8
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
bonoPos = function bonoPos(s) {
  let param0, param1, param2, param3, a, b, c, d;
  if (s instanceof State1.class) {
    param0 = s.b;
    param1 = s.e;
    param2 = s.l;
    param3 = s.a;
    a = param0;
    b = param1;
    c = param2;
    d = param3;
    return a
  } else {
    throw new globalThis.Error("match error");
  }
};
edgePos = function edgePos(s) {
  let param0, param1, param2, param3, a, b, c, d;
  if (s instanceof State1.class) {
    param0 = s.b;
    param1 = s.e;
    param2 = s.l;
    param3 = s.a;
    a = param0;
    b = param1;
    c = param2;
    d = param3;
    return b
  } else {
    throw new globalThis.Error("match error");
  }
};
larryPos = function larryPos(s) {
  let param0, param1, param2, param3, a, b, c, d;
  if (s instanceof State1.class) {
    param0 = s.b;
    param1 = s.e;
    param2 = s.l;
    param3 = s.a;
    a = param0;
    b = param1;
    c = param2;
    d = param3;
    return c
  } else {
    throw new globalThis.Error("match error");
  }
};
adamPos = function adamPos(s) {
  let param0, param1, param2, param3, a, b, c, d;
  if (s instanceof State1.class) {
    param0 = s.b;
    param1 = s.e;
    param2 = s.l;
    param3 = s.a;
    a = param0;
    b = param1;
    c = param2;
    d = param3;
    return d
  } else {
    throw new globalThis.Error("match error");
  }
};
position = function position(i, s) {
  if (i instanceof Bono1.class) {
    return bonoPos(s)
  } else if (i instanceof Edge1.class) {
    return edgePos(s)
  } else if (i instanceof Larry1.class) {
    return larryPos(s)
  } else if (i instanceof Adam1.class) {
    return adamPos(s)
  } else {
    throw new globalThis.Error("match error");
  }
};
updateState = function updateState(s, i, pos) {
  let param0, param1, param2, param3, a, b, c, d;
  if (s instanceof State1.class) {
    param0 = s.b;
    param1 = s.e;
    param2 = s.l;
    param3 = s.a;
    a = param0;
    b = param1;
    c = param2;
    d = param3;
    if (i instanceof Bono1.class) {
      return State1(pos, b, c, d)
    } else if (i instanceof Edge1.class) {
      return State1(a, pos, c, d)
    } else if (i instanceof Larry1.class) {
      return State1(a, b, pos, d)
    } else if (i instanceof Adam1.class) {
      return State1(a, b, c, pos)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
opposite = function opposite(b) {
  if (b instanceof LeftBank1.class) {
    return RightBank1
  } else if (b instanceof RightBank1.class) {
    return LeftBank1
  } else {
    throw new globalThis.Error("match error");
  }
};
notSeen = function notSeen(state, states) {
  let tmp3, lambda1;
  lambda1 = (undefined, function (caseScrut) {
    let first1, first0, s, tmp4;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      s = first1;
      tmp4 = stateEq(state, s);
      return BenchmarkPrelude.not(tmp4)
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp3 = lambda1;
  return NofibPrelude.all(tmp3, states)
};
writeItem = function writeItem(i, b, rest) {
  let tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10;
  if (i instanceof Bono1.class) {
    if (b instanceof LeftBank1.class) {
      tmp3 = NofibPrelude.nofibStringToList("    Bono |                    |\n");
      return NofibPrelude.append(tmp3, rest)
    } else if (b instanceof RightBank1.class) {
      tmp4 = NofibPrelude.nofibStringToList("         |                    | Bono\n");
      return NofibPrelude.append(tmp4, rest)
    } else {
      throw new globalThis.Error("match error");
    }
  } else if (i instanceof Edge1.class) {
    if (b instanceof LeftBank1.class) {
      tmp5 = NofibPrelude.nofibStringToList("The Edge |                    |\n");
      return NofibPrelude.append(tmp5, rest)
    } else if (b instanceof RightBank1.class) {
      tmp6 = NofibPrelude.nofibStringToList("         |                    | The Edge\n");
      return NofibPrelude.append(tmp6, rest)
    } else {
      throw new globalThis.Error("match error");
    }
  } else if (i instanceof Larry1.class) {
    if (b instanceof LeftBank1.class) {
      tmp7 = NofibPrelude.nofibStringToList("   Larry |                    |\n");
      return NofibPrelude.append(tmp7, rest)
    } else if (b instanceof RightBank1.class) {
      tmp8 = NofibPrelude.nofibStringToList("         |                    | Larry\n");
      return NofibPrelude.append(tmp8, rest)
    } else {
      throw new globalThis.Error("match error");
    }
  } else if (i instanceof Adam1.class) {
    if (b instanceof LeftBank1.class) {
      tmp9 = NofibPrelude.nofibStringToList("    Adam |                    |\n");
      return NofibPrelude.append(tmp9, rest)
    } else if (b instanceof RightBank1.class) {
      tmp10 = NofibPrelude.nofibStringToList("         |                    | Adam\n");
      return NofibPrelude.append(tmp10, rest)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
writeState = function writeState(state, s) {
  let tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13;
  tmp3 = NofibPrelude.nofibStringToList("----------------------------------------\n");
  tmp4 = bonoPos(state);
  tmp5 = edgePos(state);
  tmp6 = larryPos(state);
  tmp7 = adamPos(state);
  tmp8 = NofibPrelude.nofibStringToList("----------------------------------------\n");
  tmp9 = NofibPrelude.append(tmp8, s);
  tmp10 = writeItem(Adam1, tmp7, tmp9);
  tmp11 = writeItem(Larry1, tmp6, tmp10);
  tmp12 = writeItem(Edge1, tmp5, tmp11);
  tmp13 = writeItem(Bono1, tmp4, tmp12);
  return NofibPrelude.append(tmp3, tmp13)
};
totalTime = function totalTime(history) {
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
};
writeHistory = function writeHistory(history, x) {
  let tmp3, lambda1, lambda2;
  if (history instanceof NofibPrelude.Nil.class) {
    return x
  } else {
    lambda1 = (undefined, function (timestate, acc) {
      let lambda3;
      lambda3 = (undefined, function (s) {
        let first1, first0, time, state, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12;
        if (globalThis.Array.isArray(timestate) && timestate.length === 2) {
          first0 = timestate[0];
          first1 = timestate[1];
          time = first0;
          state = first1;
          tmp4 = NofibPrelude.nofibStringToList("Time: ");
          tmp5 = totalTime(history);
          tmp6 = tmp5 - time;
          tmp7 = NofibPrelude.stringOfInt(tmp6);
          tmp8 = NofibPrelude.nofibStringToList(tmp7);
          tmp9 = runtime.safeCall(acc(s));
          tmp10 = writeState(state, tmp9);
          tmp11 = NofibPrelude.Cons("\n", tmp10);
          tmp12 = NofibPrelude.append(tmp8, tmp11);
          return NofibPrelude.append(tmp4, tmp12)
        } else {
          throw new globalThis.Error("match error");
        }
      });
      return lambda3
    });
    lambda2 = (undefined, function (x1) {
      return x1
    });
    tmp3 = NofibPrelude.foldr(lambda1, lambda2, history);
    return runtime.safeCall(tmp3(x))
  }
};
writeSolutions = function writeSolutions(solutions, count, s) {
  let param0, param1, item, next, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10;
  if (solutions instanceof NofibPrelude.Nil.class) {
    return s
  } else if (solutions instanceof NofibPrelude.Cons.class) {
    param0 = solutions.head;
    param1 = solutions.tail;
    item = param0;
    next = param1;
    tmp3 = NofibPrelude.nofibStringToList("Solution ");
    tmp4 = NofibPrelude.stringOfInt(count);
    tmp5 = NofibPrelude.nofibStringToList(tmp4);
    tmp6 = count + 1;
    tmp7 = writeSolutions(next, tmp6, s);
    tmp8 = writeHistory(item, tmp7);
    tmp9 = NofibPrelude.Cons("\n", tmp8);
    tmp10 = NofibPrelude.append(tmp5, tmp9);
    return NofibPrelude.append(tmp3, tmp10)
  } else {
    throw new globalThis.Error("match error");
  }
};
minSolutions = function minSolutions(history) {
  let minAcc, param0, param1, history1, next, tmp3, tmp4, tmp5;
  if (history instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (history instanceof NofibPrelude.Cons.class) {
    param0 = history.head;
    param1 = history.tail;
    history1 = param0;
    next = param1;
    minAcc = function minAcc(minSoFar, mins, ls) {
      let param01, param11, history2, next1, total, scrut, scrut1, tmp6, tmp7, tmp8;
      if (ls instanceof NofibPrelude.Nil.class) {
        return mins
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param01 = ls.head;
        param11 = ls.tail;
        history2 = param01;
        next1 = param11;
        tmp6 = totalTime(history2);
        total = tmp6;
        scrut1 = minSoFar < total;
        if (scrut1 === true) {
          return minAcc(minSoFar, mins, next1)
        } else {
          scrut = minSoFar === total;
          if (scrut === true) {
            tmp7 = NofibPrelude.Cons(history2, mins);
            return minAcc(minSoFar, tmp7, next1)
          } else {
            tmp8 = NofibPrelude.Cons(history2, NofibPrelude.Nil);
            return minAcc(total, tmp8, next1)
          }
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp3 = totalTime(history1);
    tmp4 = NofibPrelude.Cons(history1, NofibPrelude.Nil);
    tmp5 = minAcc(tmp3, tmp4, next);
    return NofibPrelude.reverse(tmp5)
  } else {
    throw new globalThis.Error("match error");
  }
};
u2times = function u2times(i) {
  if (i instanceof Bono1.class) {
    return 10
  } else if (i instanceof Edge1.class) {
    return 5
  } else if (i instanceof Larry1.class) {
    return 2
  } else if (i instanceof Adam1.class) {
    return 1
  } else {
    throw new globalThis.Error("match error");
  }
};
transfer = function transfer(source, dest, location, countdown, history) {
  let lscomp2, lscomp1, newHistory, newLocation, moveOne, moveTwo, scrut, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
  scrut = stateEq(source, dest);
  if (scrut === true) {
    tmp3 = NofibPrelude.Cons([
      countdown,
      dest
    ], history);
    return NofibPrelude.Cons(tmp3, NofibPrelude.Nil)
  } else {
    lscomp1 = function lscomp1(ls) {
      let param0, param1, item, xs, scrut1, newDest, scrut2, newTime, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        item = param0;
        xs = param1;
        tmp12 = position(item, dest);
        scrut1 = bankEq(tmp12, location);
        if (scrut1 === true) {
          tmp13 = updateState(dest, item, newLocation);
          newDest = tmp13;
          scrut2 = notSeen(newDest, history);
          if (scrut2 === true) {
            tmp14 = u2times(item);
            tmp15 = countdown + tmp14;
            newTime = tmp15;
            tmp16 = transfer(source, newDest, newLocation, newTime, newHistory);
            tmp17 = lscomp1(xs);
            return NofibPrelude.Cons(tmp16, tmp17)
          } else {
            return lscomp1(xs)
          }
        } else {
          return lscomp1(xs)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    lscomp2 = function lscomp2(ls) {
      let lscomp3, param0, param1, i, xs, tmp12, tmp13;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        i = param0;
        xs = param1;
        lscomp3 = function lscomp3(ls1) {
          let param01, param11, j, ys, scrut1, scrut2, newDest, scrut3, newTime, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21;
          if (ls1 instanceof NofibPrelude.Nil.class) {
            return lscomp2(xs)
          } else if (ls1 instanceof NofibPrelude.Cons.class) {
            param01 = ls1.head;
            param11 = ls1.tail;
            j = param01;
            ys = param11;
            tmp14 = position(i, dest);
            scrut1 = bankEq(tmp14, location);
            if (scrut1 === true) {
              tmp15 = position(j, dest);
              scrut2 = bankEq(tmp15, location);
              if (scrut2 === true) {
                tmp16 = updateState(dest, i, newLocation);
                tmp17 = updateState(tmp16, j, newLocation);
                newDest = tmp17;
                scrut3 = notSeen(newDest, history);
                if (scrut3 === true) {
                  tmp18 = u2times(i);
                  tmp19 = countdown + tmp18;
                  newTime = tmp19;
                  tmp20 = transfer(source, newDest, newLocation, newTime, newHistory);
                  tmp21 = lscomp3(ys);
                  return NofibPrelude.Cons(tmp20, tmp21)
                } else {
                  return lscomp3(ys)
                }
              } else {
                return lscomp3(ys)
              }
            } else {
              return lscomp3(ys)
            }
          } else {
            throw new globalThis.Error("match error");
          }
        };
        tmp12 = succItem(i);
        tmp13 = itemFromTo(tmp12, Adam1);
        return lscomp3(tmp13)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp4 = NofibPrelude.Cons([
      countdown,
      dest
    ], history);
    newHistory = tmp4;
    tmp5 = opposite(location);
    newLocation = tmp5;
    tmp6 = itemFromTo(Bono1, Adam1);
    tmp7 = lscomp1(tmp6);
    tmp8 = NofibPrelude.concat(tmp7);
    moveOne = tmp8;
    tmp9 = itemFromTo(Bono1, Larry1);
    tmp10 = lscomp2(tmp9);
    tmp11 = NofibPrelude.concat(tmp10);
    moveTwo = tmp11;
    return NofibPrelude.append(moveOne, moveTwo)
  }
};
testPuzzle_nofib = function testPuzzle_nofib(x) {
  let time, scrut, solutions, mins, tmp3, tmp4, tmp5, tmp6;
  tmp3 = NofibPrelude.listLen(x);
  scrut = tmp3 === 1;
  if (scrut === true) {
    tmp4 = 0;
  } else {
    throw globalThis.Error("puzzle expects exactly one argument");
  }
  time = tmp4;
  tmp5 = transfer(initialState, finalState, RightBank1, time, NofibPrelude.Nil);
  solutions = tmp5;
  tmp6 = minSolutions(solutions);
  mins = tmp6;
  return writeSolutions(mins, 1, NofibPrelude.Nil)
};
ItemType1 = class ItemType {
  constructor() {}
  toString() { return "ItemType"; }
};
const Bono$class = class Bono extends ItemType1 {
  constructor() {
    super();
  }
  toString() { return "Bono"; }
}; Bono1 = new Bono$class;
Bono1.class = Bono$class;
const Edge$class = class Edge extends ItemType1 {
  constructor() {
    super();
  }
  toString() { return "Edge"; }
}; Edge1 = new Edge$class;
Edge1.class = Edge$class;
const Larry$class = class Larry extends ItemType1 {
  constructor() {
    super();
  }
  toString() { return "Larry"; }
}; Larry1 = new Larry$class;
Larry1.class = Larry$class;
const Adam$class = class Adam extends ItemType1 {
  constructor() {
    super();
  }
  toString() { return "Adam"; }
}; Adam1 = new Adam$class;
Adam1.class = Adam$class;
BankType1 = class BankType {
  constructor() {}
  toString() { return "BankType"; }
};
const LeftBank$class = class LeftBank extends BankType1 {
  constructor() {
    super();
  }
  toString() { return "LeftBank"; }
}; LeftBank1 = new LeftBank$class;
LeftBank1.class = LeftBank$class;
const RightBank$class = class RightBank extends BankType1 {
  constructor() {
    super();
  }
  toString() { return "RightBank"; }
}; RightBank1 = new RightBank$class;
RightBank1.class = RightBank$class;
State1 = function State(b1, e1, l1, a1) {
  return new State.class(b1, e1, l1, a1);
};
State1.class = class State {
  constructor(b, e, l, a) {
    this.b = b;
    this.e = e;
    this.l = l;
    this.a = a;
  }
  toString() { return "State(" + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.e) + ", " + globalThis.Predef.render(this.l) + ", " + globalThis.Predef.render(this.a) + ")"; }
};
tmp = State1(LeftBank1, LeftBank1, LeftBank1, LeftBank1);
initialState = tmp;
tmp1 = State1(RightBank1, RightBank1, RightBank1, RightBank1);
finalState = tmp1;
lambda = (undefined, function () {
  let tmp3, tmp4, tmp5;
  tmp3 = NofibPrelude.Cons(2, NofibPrelude.Nil);
  tmp4 = testPuzzle_nofib(tmp3);
  tmp5 = NofibPrelude.nofibListToString(tmp4);
  return BenchmarkPrelude.print(tmp5)
});
tmp2 = lambda;
BenchmarkPrelude.benchmark(tmp2)