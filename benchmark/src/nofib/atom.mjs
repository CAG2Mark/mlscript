import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let propagate, show, dotMult, testforce, dotPlus, testAtom_nofib, scalarMut, State1, runExperiment, lambda;
dotPlus = function dotPlus(fs, gs) {
  let param0, param1, f, fs1, param01, param11, g, gs1, tmp, tmp1;
  if (fs instanceof NofibPrelude.Nil.class) {
    return gs
  } else {
    if (gs instanceof NofibPrelude.Nil.class) {
      return fs
    } else {
      if (fs instanceof NofibPrelude.Cons.class) {
        param0 = fs.head;
        param1 = fs.tail;
        f = param0;
        fs1 = param1;
        if (gs instanceof NofibPrelude.Cons.class) {
          param01 = gs.head;
          param11 = gs.tail;
          g = param01;
          gs1 = param11;
          tmp = f + g;
          tmp1 = dotPlus(fs1, gs1);
          return NofibPrelude.Cons(tmp, tmp1)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    }
  }
};
dotMult = function dotMult(fs, gs) {
  let param0, param1, f, fs1, param01, param11, g, gs1, tmp, tmp1;
  if (fs instanceof NofibPrelude.Cons.class) {
    param0 = fs.head;
    param1 = fs.tail;
    f = param0;
    fs1 = param1;
    if (gs instanceof NofibPrelude.Cons.class) {
      param01 = gs.head;
      param11 = gs.tail;
      g = param01;
      gs1 = param11;
      tmp = f * g;
      tmp1 = dotMult(fs1, gs1);
      return NofibPrelude.Cons(tmp, tmp1)
    } else {
      return NofibPrelude.Nil
    }
  } else {
    return NofibPrelude.Nil
  }
};
scalarMut = function scalarMut(c, fs) {
  let param0, param1, f, fs1, tmp, tmp1;
  if (fs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (fs instanceof NofibPrelude.Cons.class) {
    param0 = fs.head;
    param1 = fs.tail;
    f = param0;
    fs1 = param1;
    tmp = c * f;
    tmp1 = scalarMut(c, fs1);
    return NofibPrelude.Cons(tmp, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
testforce = function testforce(k, ss) {
  let tmp, lambda1;
  lambda1 = (undefined, function () {
    let scrut, param0, param1, param01, param11, pos, vel, atoms, tmp1, tmp2, tmp3, tmp4;
    scrut = NofibPrelude.force(ss);
    if (scrut instanceof NofibPrelude.LzCons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      if (param0 instanceof State1.class) {
        param01 = param0.position;
        param11 = param0.velocity;
        pos = param01;
        vel = param11;
        atoms = param1;
        tmp1 = - 1.0;
        tmp2 = scalarMut(tmp1, k);
        tmp3 = dotMult(tmp2, pos);
        tmp4 = testforce(k, atoms);
        return NofibPrelude.LzCons(tmp3, tmp4)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp = lambda1;
  return NofibPrelude.lazy(tmp)
};
show = function show(s) {
  let lscomp, param0, param1, pos, vel, tmp;
  lscomp = function lscomp(ls) {
    let param01, param11, component, t, tmp1, tmp2, tmp3;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param01 = ls.head;
      param11 = ls.tail;
      component = param01;
      t = param11;
      tmp1 = NofibPrelude.stringOfFloat(component);
      tmp2 = NofibPrelude.stringConcat(tmp1, "\t");
      tmp3 = lscomp(t);
      return NofibPrelude.Cons(tmp2, tmp3)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  if (s instanceof State1.class) {
    param0 = s.position;
    param1 = s.velocity;
    pos = param0;
    vel = param1;
    tmp = lscomp(pos);
    return NofibPrelude.stringListConcat(tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
propagate = function propagate(dt, aforce, state) {
  let param0, param1, pos, vel, tmp, tmp1, tmp2, tmp3;
  if (state instanceof State1.class) {
    param0 = state.position;
    param1 = state.velocity;
    pos = param0;
    vel = param1;
    tmp = scalarMut(dt, vel);
    tmp1 = dotPlus(pos, tmp);
    tmp2 = scalarMut(dt, aforce);
    tmp3 = dotPlus(vel, tmp2);
    return State1(tmp1, tmp3)
  } else {
    throw new globalThis.Error("match error");
  }
};
runExperiment = function runExperiment(law, dt, param, init) {
  let tmp, lambda1;
  lambda1 = (undefined, function () {
    let stream, tmp1, tmp2, tmp3, lambda2;
    tmp1 = runExperiment(law, dt, param, init);
    stream = tmp1;
    tmp2 = runtime.safeCall(law(param, stream));
    lambda2 = (undefined, function (x, y) {
      return propagate(dt, x, y)
    });
    tmp3 = NofibPrelude.zipWith_lz_lz(lambda2, tmp2, stream);
    return NofibPrelude.LzCons(init, tmp3)
  });
  tmp = lambda1;
  return NofibPrelude.lazy(tmp)
};
testAtom_nofib = function testAtom_nofib(n) {
  let lscomp, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
  lscomp = function lscomp(ls) {
    let param0, param1, state, t, tmp7, tmp8, tmp9;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      state = param0;
      t = param1;
      tmp7 = show(state);
      tmp8 = NofibPrelude.stringConcat(tmp7, "\n");
      tmp9 = lscomp(t);
      return NofibPrelude.Cons(tmp8, tmp9)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp = NofibPrelude.Cons(1.0, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(1.0, NofibPrelude.Nil);
  tmp2 = NofibPrelude.Cons(0.0, NofibPrelude.Nil);
  tmp3 = State1(tmp1, tmp2);
  tmp4 = runExperiment(testforce, 0.02, tmp, tmp3);
  tmp5 = NofibPrelude.take_lz(n, tmp4);
  tmp6 = lscomp(tmp5);
  return NofibPrelude.stringListConcat(tmp6)
};
State1 = function State(position1, velocity1) {
  return new State.class(position1, velocity1);
};
State1.class = class State {
  constructor(position, velocity) {
    this.position = position;
    this.velocity = velocity;
  }
  toString() { return "State(" + globalThis.Predef.render(this.position) + ", " + globalThis.Predef.render(this.velocity) + ")"; }
};
lambda = (undefined, function () {
  return testAtom_nofib(20)
});
BenchmarkPrelude.benchmark(lambda)