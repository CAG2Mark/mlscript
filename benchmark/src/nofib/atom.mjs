import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let lscomp, lscomp1, atom1, lambda, lambda1, lambda2, lambda$, lambda$1, lambda$2;
lscomp1 = function lscomp(ls) {
  let param0, param1, state, t, tmp, tmp1, tmp2;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    state = param0;
    t = param1;
    tmp = atom1.show(state);
    tmp1 = NofibPrelude.stringConcat(tmp, "\n");
    tmp2 = lscomp1(t);
    return NofibPrelude.Cons(tmp1, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$2 = function lambda$(dt, x, y) {
  return atom1.propagate(dt, x, y)
};
lambda2 = (undefined, function (dt) {
  return (x, y) => {
    return lambda$2(dt, x, y)
  }
});
lambda$1 = function lambda$(law, dt, param, init) {
  let stream, tmp, tmp1, tmp2, lambda$this;
  tmp = atom1.runExperiment(law, dt, param, init);
  stream = tmp;
  tmp1 = runtime.safeCall(law(param, stream));
  lambda$this = runtime.safeCall(lambda2(dt));
  tmp2 = NofibPrelude.zipWith_lz_lz(lambda$this, tmp1, stream);
  return NofibPrelude.LzCons(init, tmp2)
};
lambda1 = (undefined, function (law, dt, param, init) {
  return () => {
    return lambda$1(law, dt, param, init)
  }
});
lscomp = function lscomp(ls) {
  let param0, param1, component, t, tmp, tmp1, tmp2;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    component = param0;
    t = param1;
    tmp = NofibPrelude.stringOfFloat(component);
    tmp1 = NofibPrelude.stringConcat(tmp, "\t");
    tmp2 = lscomp(t);
    return NofibPrelude.Cons(tmp1, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$ = function lambda$(k, ss) {
  let scrut, param0, param1, param01, param11, pos, vel, atoms, tmp, tmp1, tmp2, tmp3;
  scrut = NofibPrelude.force(ss);
  if (scrut instanceof NofibPrelude.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    if (param0 instanceof atom1.State.class) {
      param01 = param0.position;
      param11 = param0.velocity;
      pos = param01;
      vel = param11;
      atoms = param1;
      tmp = - 1.0;
      tmp1 = atom1.scalarMut(tmp, k);
      tmp2 = atom1.dotMult(tmp1, pos);
      tmp3 = atom1.testforce(k, atoms);
      return NofibPrelude.LzCons(tmp2, tmp3)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda = (undefined, function (k, ss) {
  return () => {
    return lambda$(k, ss)
  }
});
atom1 = class atom {
  static {
    atom1 = atom;
    let lambda3;
    this.State = function State(position1, velocity1) {
      return new State.class(position1, velocity1);
    };
    this.State.class = class State {
      constructor(position, velocity) {
        this.position = position;
        this.velocity = velocity;
      }
      toString() { return "State(" + globalThis.Predef.render(this.position) + ", " + globalThis.Predef.render(this.velocity) + ")"; }
    };
    lambda3 = (undefined, function () {
      return atom.testAtom_nofib(20)
    });
    BenchmarkPrelude.benchmark(lambda3)
  }
  static dotPlus(fs1, gs) {
    let param0, param1, f, fs2, param01, param11, g, gs1, tmp, tmp1;
    if (fs1 instanceof NofibPrelude.Nil.class) {
      return gs
    } else {
      if (gs instanceof NofibPrelude.Nil.class) {
        return fs1
      } else {
        if (fs1 instanceof NofibPrelude.Cons.class) {
          param0 = fs1.head;
          param1 = fs1.tail;
          f = param0;
          fs2 = param1;
          if (gs instanceof NofibPrelude.Cons.class) {
            param01 = gs.head;
            param11 = gs.tail;
            g = param01;
            gs1 = param11;
            tmp = f + g;
            tmp1 = atom.dotPlus(fs2, gs1);
            return NofibPrelude.Cons(tmp, tmp1)
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      }
    }
  } 
  static dotMult(fs2, gs1) {
    let param0, param1, f, fs3, param01, param11, g, gs2, tmp, tmp1;
    if (fs2 instanceof NofibPrelude.Cons.class) {
      param0 = fs2.head;
      param1 = fs2.tail;
      f = param0;
      fs3 = param1;
      if (gs1 instanceof NofibPrelude.Cons.class) {
        param01 = gs1.head;
        param11 = gs1.tail;
        g = param01;
        gs2 = param11;
        tmp = f * g;
        tmp1 = atom.dotMult(fs3, gs2);
        return NofibPrelude.Cons(tmp, tmp1)
      } else {
        return NofibPrelude.Nil
      }
    } else {
      return NofibPrelude.Nil
    }
  } 
  static scalarMut(c, fs3) {
    let param0, param1, f, fs4, tmp, tmp1;
    if (fs3 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (fs3 instanceof NofibPrelude.Cons.class) {
      param0 = fs3.head;
      param1 = fs3.tail;
      f = param0;
      fs4 = param1;
      tmp = c * f;
      tmp1 = atom.scalarMut(c, fs4);
      return NofibPrelude.Cons(tmp, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static testforce(k, ss) {
    let tmp;
    tmp = runtime.safeCall(lambda(k, ss));
    return NofibPrelude.lazy(tmp)
  } 
  static show(s) {
    let param0, param1, pos, vel, tmp;
    if (s instanceof atom.State.class) {
      param0 = s.position;
      param1 = s.velocity;
      pos = param0;
      vel = param1;
      tmp = lscomp(pos);
      return NofibPrelude.stringListConcat(tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static propagate(dt, aforce, state) {
    let param0, param1, pos, vel, tmp, tmp1, tmp2, tmp3;
    if (state instanceof atom.State.class) {
      param0 = state.position;
      param1 = state.velocity;
      pos = param0;
      vel = param1;
      tmp = atom.scalarMut(dt, vel);
      tmp1 = atom.dotPlus(pos, tmp);
      tmp2 = atom.scalarMut(dt, aforce);
      tmp3 = atom.dotPlus(vel, tmp2);
      return atom.State(tmp1, tmp3)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static runExperiment(law, dt1, param, init) {
    let tmp;
    tmp = runtime.safeCall(lambda1(law, dt1, param, init));
    return NofibPrelude.lazy(tmp)
  } 
  static testAtom_nofib(n) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = NofibPrelude.Cons(1.0, NofibPrelude.Nil);
    tmp1 = NofibPrelude.Cons(1.0, NofibPrelude.Nil);
    tmp2 = NofibPrelude.Cons(0.0, NofibPrelude.Nil);
    tmp3 = atom.State(tmp1, tmp2);
    tmp4 = atom.runExperiment(atom.testforce, 0.02, tmp, tmp3);
    tmp5 = NofibPrelude.take_lz(n, tmp4);
    tmp6 = lscomp1(tmp5);
    return NofibPrelude.stringListConcat(tmp6)
  }
  static toString() { return "atom"; }
};
let atom = atom1; export default atom;
