import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import Predef from "./../../../hkmc2/shared/src/test/mlscript-compile/Predef.mjs";
let r, l, go, f, lscomp, combine, go1, NofibPrelude1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda14, lambda15, lambda16, lambda17, lambda18, lambda19, lambda20, lambda21, lambda22, lambda$, lambda$1, lambda$2, lambda$3, lambda$4, lambda$5, lambda$6, lambda$7, lambda$8, lambda$9, lambda$10, lambda$11, lambda$12, lambda$13, lambda$14, lambda$15, go$;
go$ = function go$(s, i) {
  let scrut, tmp, tmp1, tmp2;
  scrut = i < s.length;
  if (scrut === true) {
    tmp = runtime.safeCall(s.charAt(i));
    tmp1 = i + 1;
    tmp2 = go$(s, tmp1);
    return NofibPrelude1.Cons(tmp, tmp2)
  } else {
    return NofibPrelude1.Nil
  }
};
go1 = function go(s) {
  return (i) => {
    return go$(s, i)
  }
};
lambda$15 = function lambda$(x) {
  let tmp;
  tmp = NofibPrelude1.repeat(x);
  return NofibPrelude1.LzCons(x, tmp)
};
lambda22 = (undefined, function (x) {
  return () => {
    return lambda$15(x)
  }
});
lambda$14 = function lambda$(a) {
  let tmp, tmp1;
  tmp = a + 1;
  tmp1 = NofibPrelude1.enumFrom(tmp);
  return NofibPrelude1.LzCons(a, tmp1)
};
lambda21 = (undefined, function (a) {
  return () => {
    return lambda$14(a)
  }
});
lambda19 = (undefined, function () {
  return NofibPrelude1.LzNil
});
lambda$13 = function lambda$(n, x) {
  let tmp, tmp1;
  tmp = n - 1;
  tmp1 = NofibPrelude1.replicate_lz(tmp, x);
  return NofibPrelude1.LzCons(x, tmp1)
};
lambda20 = (undefined, function (n, x) {
  return () => {
    return lambda$13(n, x)
  }
});
lambda$12 = function lambda$(xs, ys) {
  let scrut, param0, param1, h, t, tmp;
  scrut = NofibPrelude1.force(xs);
  if (scrut instanceof NofibPrelude1.LzNil.class) {
    return NofibPrelude1.force(ys)
  } else if (scrut instanceof NofibPrelude1.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    h = param0;
    t = param1;
    tmp = NofibPrelude1.append_lz_lz(t, ys);
    return NofibPrelude1.LzCons(h, tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda18 = (undefined, function (xs, ys) {
  return () => {
    return lambda$12(xs, ys)
  }
});
lambda$11 = function lambda$(ys, h, t) {
  let tmp;
  tmp = NofibPrelude1.append_nl_lz(t, ys);
  return NofibPrelude1.LzCons(h, tmp)
};
lambda17 = (undefined, function (ys, h, t) {
  return () => {
    return lambda$11(ys, h, t)
  }
});
lambda$10 = function lambda$(f1, x) {
  let tmp, tmp1;
  tmp = runtime.safeCall(f1(x));
  tmp1 = NofibPrelude1.iterate(f1, tmp);
  return NofibPrelude1.LzCons(x, tmp1)
};
lambda16 = (undefined, function (f1, x) {
  return () => {
    return lambda$10(f1, x)
  }
});
lambda$9 = function lambda$(f1, xss, yss) {
  let scrut, param0, param1, x, xs, scrut1, param01, param11, y, ys, tmp, tmp1;
  scrut = NofibPrelude1.force(xss);
  if (scrut instanceof NofibPrelude1.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    x = param0;
    xs = param1;
    scrut1 = NofibPrelude1.force(yss);
    if (scrut1 instanceof NofibPrelude1.LzCons.class) {
      param01 = scrut1.head;
      param11 = scrut1.tail;
      y = param01;
      ys = param11;
      tmp = runtime.safeCall(f1(x, y));
      tmp1 = NofibPrelude1.zipWith_lz_lz(f1, xs, ys);
      return NofibPrelude1.LzCons(tmp, tmp1)
    } else {
      return NofibPrelude1.LzNil
    }
  } else {
    return NofibPrelude1.LzNil
  }
};
lambda15 = (undefined, function (f1, xss, yss) {
  return () => {
    return lambda$9(f1, xss, yss)
  }
});
lambda$8 = function lambda$(x, xs, y, ys) {
  let tmp;
  tmp = NofibPrelude1.zip_lz_lz(xs, ys);
  return NofibPrelude1.LzCons([
    x,
    y
  ], tmp)
};
lambda12 = (undefined, function (x, xs, y, ys) {
  return () => {
    return lambda$8(x, xs, y, ys)
  }
});
lambda13 = (undefined, function () {
  return NofibPrelude1.LzNil
});
lambda14 = (undefined, function () {
  return NofibPrelude1.LzNil
});
lambda11 = (undefined, function () {
  return NofibPrelude1.LzNil
});
lambda$7 = function lambda$(n, ls) {
  let scrut, scrut1, param0, param1, h, t, tmp, tmp1;
  scrut = n > 0;
  if (scrut === true) {
    scrut1 = NofibPrelude1.force(ls);
    if (scrut1 instanceof NofibPrelude1.LzNil.class) {
      return NofibPrelude1.LzNil
    } else if (scrut1 instanceof NofibPrelude1.LzCons.class) {
      param0 = scrut1.head;
      param1 = scrut1.tail;
      h = param0;
      t = param1;
      tmp = n - 1;
      tmp1 = NofibPrelude1.take_lz_lz(tmp, t);
      return NofibPrelude1.LzCons(h, tmp1)
    } else {
      return NofibPrelude1.LzNil
    }
  } else {
    return NofibPrelude1.LzNil
  }
};
lambda10 = (undefined, function (n, ls) {
  return () => {
    return lambda$7(n, ls)
  }
});
lambda9 = (undefined, function (x, y) {
  return x == y
});
lambda$6 = function lambda$(eq, h, y) {
  let tmp;
  tmp = runtime.safeCall(eq(h, y));
  return Predef.not(tmp)
};
lambda8 = (undefined, function (eq, h) {
  return (y) => {
    return lambda$6(eq, h, y)
  }
});
lambda$5 = function lambda$(eq, ls) {
  let scrut, param0, param1, h, t, tmp, tmp1, lambda$this;
  scrut = NofibPrelude1.force(ls);
  if (scrut instanceof NofibPrelude1.LzNil.class) {
    return NofibPrelude1.LzNil
  } else if (scrut instanceof NofibPrelude1.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    h = param0;
    t = param1;
    lambda$this = runtime.safeCall(lambda8(eq, h));
    tmp = NofibPrelude1.filter_lz(lambda$this, t);
    tmp1 = NofibPrelude1.nubBy_lz(eq, tmp);
    return NofibPrelude1.LzCons(h, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda7 = (undefined, function (eq, ls) {
  return () => {
    return lambda$5(eq, ls)
  }
});
lambda$4 = function lambda$(p, ls) {
  let scrut, param0, param1, h, t, scrut1, tmp, tmp1;
  scrut = NofibPrelude1.force(ls);
  if (scrut instanceof NofibPrelude1.LzNil.class) {
    return NofibPrelude1.LzNil
  } else if (scrut instanceof NofibPrelude1.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    h = param0;
    t = param1;
    scrut1 = runtime.safeCall(p(h));
    if (scrut1 === true) {
      tmp = NofibPrelude1.filter_lz(p, t);
      return NofibPrelude1.LzCons(h, tmp)
    } else {
      tmp1 = NofibPrelude1.filter_lz(p, t);
      return NofibPrelude1.force(tmp1)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda6 = (undefined, function (p, ls) {
  return () => {
    return lambda$4(p, ls)
  }
});
lambda$3 = function lambda$(f1, ls) {
  let scrut, param0, param1, h, t, tmp, tmp1;
  scrut = NofibPrelude1.force(ls);
  if (scrut instanceof NofibPrelude1.LzNil.class) {
    return NofibPrelude1.LzNil
  } else if (scrut instanceof NofibPrelude1.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    h = param0;
    t = param1;
    tmp = runtime.safeCall(f1(h));
    tmp1 = NofibPrelude1.map_lz(f1, t);
    return NofibPrelude1.LzCons(tmp, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda5 = (undefined, function (f1, ls) {
  return () => {
    return lambda$3(f1, ls)
  }
});
lscomp = function lscomp(ls) {
  let param0, param1, h, t, param01, param11, hd, tl, tmp;
  if (ls instanceof NofibPrelude1.Nil.class) {
    return NofibPrelude1.Nil
  } else if (ls instanceof NofibPrelude1.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    if (h instanceof NofibPrelude1.Cons.class) {
      param01 = h.head;
      param11 = h.tail;
      hd = param01;
      tl = param11;
      tmp = lscomp(t);
      return NofibPrelude1.Cons([
        hd,
        tl
      ], tmp)
    } else {
      return lscomp(t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
combine = function combine(y, h, ys, t) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude1.Cons(y, h);
  tmp1 = NofibPrelude1.Cons(ys, t);
  tmp2 = NofibPrelude1.transpose(tmp1);
  return NofibPrelude1.Cons(tmp, tmp2)
};
f = function f(l1, a, b) {
  let param0, param1, first1, first0, x, y, t, tmp, tmp1, tmp2, tmp3;
  if (l1 instanceof NofibPrelude1.Nil.class) {
    tmp = NofibPrelude1.reverse(a);
    tmp1 = NofibPrelude1.reverse(b);
    return [
      tmp,
      tmp1
    ]
  } else if (l1 instanceof NofibPrelude1.Cons.class) {
    param0 = l1.head;
    param1 = l1.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      x = first0;
      y = first1;
      t = param1;
      tmp2 = NofibPrelude1.Cons(x, a);
      tmp3 = NofibPrelude1.Cons(y, b);
      return f(t, tmp2, tmp3)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
go = function go(xs, a) {
  let param0, param1, h, t, tmp;
  if (xs instanceof NofibPrelude1.Nil.class) {
    return a
  } else if (xs instanceof NofibPrelude1.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    h = param0;
    t = param1;
    tmp = a + h;
    return go(t, tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda4 = (undefined, function (x, y) {
  return x == y
});
lambda$2 = function lambda$(eq, acc, y) {
  return NofibPrelude1.deleteBy(eq, y, acc)
};
lambda3 = (undefined, function (eq) {
  return (acc, y) => {
    return lambda$2(eq, acc, y)
  }
});
lambda$1 = function lambda$(eq, h, y) {
  let tmp;
  tmp = runtime.safeCall(eq(h, y));
  return Predef.not(tmp)
};
lambda2 = (undefined, function (eq, h) {
  return (y) => {
    return lambda$1(eq, h, y)
  }
});
lambda1 = (undefined, function (x, y) {
  let scrut;
  scrut = x > y;
  if (scrut === true) {
    return x
  } else {
    return y
  }
});
l = function l(ls, a) {
  let param0, param1, h, t, tmp;
  if (ls instanceof NofibPrelude1.Nil.class) {
    return a
  } else if (ls instanceof NofibPrelude1.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    tmp = a + 1;
    return l(t, tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
r = function r(l$_, l1) {
  let param0, param1, x, xs, tmp;
  if (l1 instanceof NofibPrelude1.Cons.class) {
    param0 = l1.head;
    param1 = l1.tail;
    x = param0;
    xs = param1;
    tmp = NofibPrelude1.Cons(x, l$_);
    return r(tmp, xs)
  } else {
    return l$_
  }
};
lambda$ = function lambda$(f1, g, x) {
  let tmp;
  tmp = runtime.safeCall(g(x));
  return runtime.safeCall(f1(tmp))
};
lambda = (undefined, function (f1, g) {
  return (x) => {
    return lambda$(f1, g, x)
  }
});
NofibPrelude1 = class NofibPrelude {
  static {
    NofibPrelude1 = NofibPrelude;
    this.Option = class Option {
      constructor() {}
      toString() { return "Option"; }
    };
    this.Some = function Some(x1) {
      return new Some.class(x1);
    };
    this.Some.class = class Some extends NofibPrelude.Option {
      constructor(x) {
        super();
        this.x = x;
      }
      toString() { return "Some(" + globalThis.Predef.render(this.x) + ")"; }
    };
    const None$class = class None extends NofibPrelude.Option {
      constructor() {
        super();
      }
      toString() { return "None"; }
    };
    this.None = new None$class;
    this.None.class = None$class;
    this.Lazy = function Lazy(init1) {
      return new Lazy.class(init1);
    };
    this.Lazy.class = class Lazy {
      constructor(init) {
        this.init = init;
        this.cached = NofibPrelude.None;
      }
      get() {
        let scrut, v, param0, v1, tmp, tmp1;
        scrut = this.cached;
        if (scrut instanceof NofibPrelude.Some.class) {
          param0 = scrut.x;
          v1 = param0;
          return v1
        } else {
          tmp = runtime.safeCall(this.init());
          v = tmp;
          tmp1 = NofibPrelude.Some(v);
          this.cached = tmp1;
          return v
        }
      }
      toString() { return "Lazy(" + globalThis.Predef.render(this.init) + ")"; }
    };
    this.List = class List {
      constructor() {}
      toString() { return "List"; }
    };
    this.Cons = function Cons(head1, tail1) {
      return new Cons.class(head1, tail1);
    };
    this.Cons.class = class Cons extends NofibPrelude.List {
      constructor(head, tail) {
        super();
        this.head = head;
        this.tail = tail;
      }
      toString() {
        let tmp, tmp1, tmp2;
        tmp = NofibPrelude.Cons(this.head, this.tail);
        tmp1 = NofibPrelude._internal_cons_to_str(tmp);
        tmp2 = "[" + tmp1;
        return tmp2 + "]"
      }
    };
    const Nil$class = class Nil extends NofibPrelude.List {
      constructor() {
        super();
      }
      toString() {
        return "[]"
      }
    };
    this.Nil = new Nil$class;
    this.Nil.class = Nil$class;
    this.LzList = class LzList {
      constructor() {}
      toString() { return "LzList"; }
    };
    this.LzCons = function LzCons(head1, tail1) {
      return new LzCons.class(head1, tail1);
    };
    this.LzCons.class = class LzCons extends NofibPrelude.LzList {
      constructor(head, tail) {
        super();
        this.head = head;
        this.tail = tail;
      }
      toString() { return "LzCons(" + globalThis.Predef.render(this.head) + ", " + globalThis.Predef.render(this.tail) + ")"; }
    };
    const LzNil$class = class LzNil extends NofibPrelude.LzList {
      constructor() {
        super();
      }
      toString() { return "LzNil"; }
    };
    this.LzNil = new LzNil$class;
    this.LzNil.class = LzNil$class;
  }
  static fromSome(s) {
    let param0, x;
    if (s instanceof NofibPrelude.Some.class) {
      param0 = s.x;
      x = param0;
      return x
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static lazy(x) {
    return NofibPrelude.Lazy(x)
  } 
  static force(x1) {
    if (x1 instanceof NofibPrelude.Lazy.class) {
      return x1.get()
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static _internal_cons_to_str(ls) {
    let param0, param1, h, t, h1, tmp, tmp1, tmp2;
    if (ls instanceof NofibPrelude.Nil.class) {
      return ""
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      h1 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return Predef.render(h1)
      } else {
        h = param0;
        t = param1;
        tmp = Predef.render(h);
        tmp1 = tmp + ",";
        tmp2 = NofibPrelude._internal_cons_to_str(t);
        return tmp1 + tmp2
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static ltList(xs, ys, lt, gt) {
    let param0, param1, x2, xs1, param01, param11, y, ys1, scrut, scrut1;
    if (xs instanceof NofibPrelude.Nil.class) {
      if (ys instanceof NofibPrelude.Nil.class) {
        return false
      } else {
        return true
      }
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param0 = xs.head;
      param1 = xs.tail;
      x2 = param0;
      xs1 = param1;
      if (ys instanceof NofibPrelude.Nil.class) {
        return false
      } else if (ys instanceof NofibPrelude.Cons.class) {
        param01 = ys.head;
        param11 = ys.tail;
        y = param01;
        ys1 = param11;
        scrut1 = runtime.safeCall(lt(x2, y));
        if (scrut1 === true) {
          return true
        } else {
          scrut = runtime.safeCall(gt(x2, y));
          if (scrut === true) {
            return false
          } else {
            return NofibPrelude.ltList(xs1, ys1, lt, gt)
          }
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static list(...args) {
    let rest, first0, x2, xs1, tmp;
    if (globalThis.Array.isArray(args) && args.length === 0) {
      return NofibPrelude.Nil
    } else if (globalThis.Array.isArray(args) && args.length >= 1) {
      first0 = args[0];
      rest = runtime.safeCall(globalThis.Predef.tupleSlice(args, 1, 0));
      x2 = first0;
      xs1 = rest;
      tmp = NofibPrelude.list(...xs1);
      return NofibPrelude.Cons(x2, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static ltTup2(t1, t2, lt1, gt1, lt2) {
    let first1, first0, a, b, first11, first01, c, d, scrut, scrut1;
    if (globalThis.Array.isArray(t1) && t1.length === 2) {
      first0 = t1[0];
      first1 = t1[1];
      a = first0;
      b = first1;
      if (globalThis.Array.isArray(t2) && t2.length === 2) {
        first01 = t2[0];
        first11 = t2[1];
        c = first01;
        d = first11;
        scrut1 = runtime.safeCall(lt1(a, c));
        if (scrut1 === true) {
          return true
        } else {
          scrut = runtime.safeCall(gt1(a, c));
          if (scrut === true) {
            return false
          } else {
            return runtime.safeCall(lt2(b, d))
          }
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static eqTup2(t11, t21) {
    let first1, first0, a, b, first11, first01, c, d, scrut, scrut1;
    if (globalThis.Array.isArray(t11) && t11.length === 2) {
      first0 = t11[0];
      first1 = t11[1];
      a = first0;
      b = first1;
      if (globalThis.Array.isArray(t21) && t21.length === 2) {
        first01 = t21[0];
        first11 = t21[1];
        c = first01;
        d = first11;
        scrut = a == c;
        if (scrut === true) {
          scrut1 = b == d;
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
  } 
  static compose(f1, g) {
    return runtime.safeCall(lambda(f1, g))
  } 
  static snd(x2) {
    let first1, first0, f2, s1;
    if (globalThis.Array.isArray(x2) && x2.length === 2) {
      first0 = x2[0];
      first1 = x2[1];
      f2 = first0;
      s1 = first1;
      return s1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static fst(x3) {
    let first1, first0, f2, s1;
    if (globalThis.Array.isArray(x3) && x3.length === 2) {
      first0 = x3[0];
      first1 = x3[1];
      f2 = first0;
      s1 = first1;
      return f2
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static until(p, f2, i) {
    let scrut, tmp;
    scrut = runtime.safeCall(p(i));
    if (scrut === true) {
      return i
    } else {
      tmp = runtime.safeCall(f2(i));
      return NofibPrelude.until(p, f2, tmp)
    }
  } 
  static flip(f3, x4, y) {
    let tmp;
    tmp = runtime.safeCall(f3(y));
    return runtime.safeCall(tmp(x4))
  } 
  static power(a, n) {
    return globalThis.Math.pow(a, n)
  } 
  static intDiv(a1, b) {
    let tmp;
    tmp = a1 / b;
    return runtime.safeCall(globalThis.Math.floor(tmp))
  } 
  static intQuot(a2, b1) {
    let tmp;
    tmp = a2 / b1;
    return runtime.safeCall(globalThis.Math.trunc(tmp))
  } 
  static intMod(a3, b2) {
    let tmp, tmp1;
    tmp = NofibPrelude.intDiv(a3, b2);
    tmp1 = b2 * tmp;
    return a3 - tmp1
  } 
  static intRem(a4, b3) {
    let tmp, tmp1;
    tmp = NofibPrelude.intQuot(a4, b3);
    tmp1 = b3 * tmp;
    return a4 - tmp1
  } 
  static quotRem(a5, b4) {
    let tmp, tmp1;
    tmp = NofibPrelude.intQuot(a5, b4);
    tmp1 = NofibPrelude.intRem(a5, b4);
    return [
      tmp,
      tmp1
    ]
  } 
  static divMod(a6, b5) {
    let tmp, tmp1;
    tmp = NofibPrelude.intDiv(a6, b5);
    tmp1 = NofibPrelude.intMod(a6, b5);
    return [
      tmp,
      tmp1
    ]
  } 
  static max(a7, b6) {
    return globalThis.Math.max(a7, b6)
  } 
  static min(a8, b7) {
    return globalThis.Math.min(a8, b7)
  } 
  static abs(x5) {
    return runtime.safeCall(globalThis.Math.abs(x5))
  } 
  static head(l1) {
    let param0, param1, h, t;
    if (l1 instanceof NofibPrelude.Cons.class) {
      param0 = l1.head;
      param1 = l1.tail;
      h = param0;
      t = param1;
      return h
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static tail(l2) {
    let param0, param1, h, t;
    if (l2 instanceof NofibPrelude.Cons.class) {
      param0 = l2.head;
      param1 = l2.tail;
      h = param0;
      t = param1;
      return t
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static while_(p1, f4, x6) {
    let scrut, tmp;
    scrut = runtime.safeCall(p1(x6));
    if (scrut === true) {
      tmp = runtime.safeCall(f4(x6));
      return NofibPrelude.while_(p1, f4, tmp)
    } else {
      return x6
    }
  } 
  static reverse(l3) {
    return r(NofibPrelude.Nil, l3)
  } 
  static map(f5, xs1) {
    let param0, param1, x7, xs2, tmp, tmp1;
    if (xs1 instanceof NofibPrelude.Cons.class) {
      param0 = xs1.head;
      param1 = xs1.tail;
      x7 = param0;
      xs2 = param1;
      tmp = runtime.safeCall(f5(x7));
      tmp1 = NofibPrelude.map(f5, xs2);
      return NofibPrelude.Cons(tmp, tmp1)
    } else if (xs1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static listLen(ls1) {
    return l(ls1, 0)
  } 
  static listEq(xs2, ys1) {
    let param0, param1, hx, tx, param01, param11, hy, ty, scrut;
    if (xs2 instanceof NofibPrelude.Nil.class) {
      if (ys1 instanceof NofibPrelude.Nil.class) {
        return true
      } else {
        return false
      }
    } else if (xs2 instanceof NofibPrelude.Cons.class) {
      param0 = xs2.head;
      param1 = xs2.tail;
      hx = param0;
      tx = param1;
      if (ys1 instanceof NofibPrelude.Cons.class) {
        param01 = ys1.head;
        param11 = ys1.tail;
        hy = param01;
        ty = param11;
        scrut = hx == hy;
        if (scrut === true) {
          return NofibPrelude.listEq(tx, ty)
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
  static listEqBy(f6, a9, b8) {
    let param0, param1, x7, xs3, param01, param11, y1, ys2, tmp, tmp1;
    if (a9 instanceof NofibPrelude.Nil.class) {
      if (b8 instanceof NofibPrelude.Nil.class) {
        return true
      } else {
        return false
      }
    } else if (a9 instanceof NofibPrelude.Cons.class) {
      param0 = a9.head;
      param1 = a9.tail;
      x7 = param0;
      xs3 = param1;
      if (b8 instanceof NofibPrelude.Cons.class) {
        param01 = b8.head;
        param11 = b8.tail;
        y1 = param01;
        ys2 = param11;
        tmp = runtime.safeCall(f6(x7, y1));
        tmp1 = NofibPrelude.listEqBy(f6, xs3, ys2);
        return tmp && tmp1
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static listNeq(xs3, ys2) {
    let param0, param1, hx, tx, param01, param11, hy, ty, scrut;
    if (xs3 instanceof NofibPrelude.Nil.class) {
      if (ys2 instanceof NofibPrelude.Nil.class) {
        return false
      } else {
        return true
      }
    } else if (xs3 instanceof NofibPrelude.Cons.class) {
      param0 = xs3.head;
      param1 = xs3.tail;
      hx = param0;
      tx = param1;
      if (ys2 instanceof NofibPrelude.Cons.class) {
        param01 = ys2.head;
        param11 = ys2.tail;
        hy = param01;
        ty = param11;
        scrut = hx == hy;
        if (scrut === true) {
          return NofibPrelude.listNeq(tx, ty)
        } else {
          return true
        }
      } else {
        return true
      }
    } else {
      return true
    }
  } 
  static enumFromTo(a10, b9) {
    let scrut, tmp, tmp1;
    scrut = a10 <= b9;
    if (scrut === true) {
      tmp = a10 + 1;
      tmp1 = NofibPrelude.enumFromTo(tmp, b9);
      return NofibPrelude.Cons(a10, tmp1)
    } else {
      return NofibPrelude.Nil
    }
  } 
  static enumFromThenTo(a11, t, b10) {
    let scrut, tmp, tmp1, tmp2;
    scrut = a11 <= b10;
    if (scrut === true) {
      tmp = 2 * t;
      tmp1 = tmp - a11;
      tmp2 = NofibPrelude.enumFromThenTo(t, tmp1, b10);
      return NofibPrelude.Cons(a11, tmp2)
    } else {
      return NofibPrelude.Nil
    }
  } 
  static drop(n1, ls2) {
    let param0, param1, h, t3, scrut, tmp;
    if (ls2 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls2 instanceof NofibPrelude.Cons.class) {
      param0 = ls2.head;
      param1 = ls2.tail;
      h = param0;
      t3 = param1;
      scrut = n1 <= 0;
      if (scrut === true) {
        return ls2
      } else {
        tmp = n1 - 1;
        return NofibPrelude.drop(tmp, t3)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static take(n2, ls3) {
    let param0, param1, h, t3, scrut, tmp, tmp1;
    if (ls3 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls3 instanceof NofibPrelude.Cons.class) {
      param0 = ls3.head;
      param1 = ls3.tail;
      h = param0;
      t3 = param1;
      scrut = n2 <= 0;
      if (scrut === true) {
        return NofibPrelude.Nil
      } else {
        tmp = n2 - 1;
        tmp1 = NofibPrelude.take(tmp, t3);
        return NofibPrelude.Cons(h, tmp1)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static splitAt(n3, ls4) {
    let tmp, tmp1;
    tmp = NofibPrelude.take(n3, ls4);
    tmp1 = NofibPrelude.drop(n3, ls4);
    return [
      tmp,
      tmp1
    ]
  } 
  static zip(xs4, ys3) {
    let param0, param1, x7, xs5, param01, param11, y1, ys4, tmp;
    if (xs4 instanceof NofibPrelude.Cons.class) {
      param0 = xs4.head;
      param1 = xs4.tail;
      x7 = param0;
      xs5 = param1;
      if (ys3 instanceof NofibPrelude.Cons.class) {
        param01 = ys3.head;
        param11 = ys3.tail;
        y1 = param01;
        ys4 = param11;
        tmp = NofibPrelude.zip(xs5, ys4);
        return NofibPrelude.Cons([
          x7,
          y1
        ], tmp)
      } else {
        return NofibPrelude.Nil
      }
    } else {
      return NofibPrelude.Nil
    }
  } 
  static inList(x7, ls5) {
    let param0, param1, h, t3, scrut;
    if (ls5 instanceof NofibPrelude.Cons.class) {
      param0 = ls5.head;
      param1 = ls5.tail;
      h = param0;
      t3 = param1;
      scrut = x7 === h;
      if (scrut === true) {
        return true
      } else {
        return NofibPrelude.inList(x7, t3)
      }
    } else if (ls5 instanceof NofibPrelude.Nil.class) {
      return false
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static notElem(x8, ls6) {
    let tmp;
    tmp = NofibPrelude.inList(x8, ls6);
    return Predef.not(tmp)
  } 
  static append(xs5, ys4) {
    let param0, param1, x9, xs6, tmp;
    if (xs5 instanceof NofibPrelude.Nil.class) {
      return ys4
    } else if (xs5 instanceof NofibPrelude.Cons.class) {
      param0 = xs5.head;
      param1 = xs5.tail;
      x9 = param0;
      xs6 = param1;
      tmp = NofibPrelude.append(xs6, ys4);
      return NofibPrelude.Cons(x9, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static concat(ls7) {
    let param0, param1, x9, xs6, tmp;
    if (ls7 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls7 instanceof NofibPrelude.Cons.class) {
      param0 = ls7.head;
      param1 = ls7.tail;
      x9 = param0;
      xs6 = param1;
      tmp = NofibPrelude.concat(xs6);
      return NofibPrelude.append(x9, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static filter(f7, ls8) {
    let param0, param1, h, t3, scrut, tmp;
    if (ls8 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls8 instanceof NofibPrelude.Cons.class) {
      param0 = ls8.head;
      param1 = ls8.tail;
      h = param0;
      t3 = param1;
      scrut = runtime.safeCall(f7(h));
      if (scrut === true) {
        tmp = NofibPrelude.filter(f7, t3);
        return NofibPrelude.Cons(h, tmp)
      } else {
        return NofibPrelude.filter(f7, t3)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static all(p2, ls9) {
    let param0, param1, h, t3, scrut;
    if (ls9 instanceof NofibPrelude.Nil.class) {
      return true
    } else if (ls9 instanceof NofibPrelude.Cons.class) {
      param0 = ls9.head;
      param1 = ls9.tail;
      h = param0;
      t3 = param1;
      scrut = runtime.safeCall(p2(h));
      if (scrut === true) {
        return NofibPrelude.all(p2, t3)
      } else {
        return false
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static orList(ls10) {
    let param0, param1, h, t3;
    if (ls10 instanceof NofibPrelude.Nil.class) {
      return false
    } else if (ls10 instanceof NofibPrelude.Cons.class) {
      param0 = ls10.head;
      param1 = ls10.tail;
      h = param0;
      t3 = param1;
      if (h === true) {
        return true
      } else {
        return NofibPrelude.orList(t3)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static dropWhile(f8, ls11) {
    let param0, param1, h, t3, scrut;
    if (ls11 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls11 instanceof NofibPrelude.Cons.class) {
      param0 = ls11.head;
      param1 = ls11.tail;
      h = param0;
      t3 = param1;
      scrut = runtime.safeCall(f8(h));
      if (scrut === true) {
        return NofibPrelude.dropWhile(f8, t3)
      } else {
        return NofibPrelude.Cons(h, t3)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static foldl(f9, a12, xs6) {
    let param0, param1, h, t3, tmp;
    if (xs6 instanceof NofibPrelude.Nil.class) {
      return a12
    } else if (xs6 instanceof NofibPrelude.Cons.class) {
      param0 = xs6.head;
      param1 = xs6.tail;
      h = param0;
      t3 = param1;
      tmp = runtime.safeCall(f9(a12, h));
      return NofibPrelude.foldl(f9, tmp, t3)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static scanl(f10, q, ls12) {
    let param0, param1, x9, xs7, tmp, tmp1;
    if (ls12 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(q, NofibPrelude.Nil)
    } else if (ls12 instanceof NofibPrelude.Cons.class) {
      param0 = ls12.head;
      param1 = ls12.tail;
      x9 = param0;
      xs7 = param1;
      tmp = runtime.safeCall(f10(q, x9));
      tmp1 = NofibPrelude.scanl(f10, tmp, xs7);
      return NofibPrelude.Cons(q, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static scanr(f11, q1, ls13) {
    let param0, param1, x9, xs7, scrut, param01, param11, q2, t3, tmp, tmp1;
    if (ls13 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(q1, NofibPrelude.Nil)
    } else if (ls13 instanceof NofibPrelude.Cons.class) {
      param0 = ls13.head;
      param1 = ls13.tail;
      x9 = param0;
      xs7 = param1;
      scrut = NofibPrelude.scanr(f11, q1, xs7);
      if (scrut instanceof NofibPrelude.Cons.class) {
        param01 = scrut.head;
        param11 = scrut.tail;
        q2 = param01;
        t3 = param11;
        tmp = runtime.safeCall(f11(x9, q2));
        tmp1 = NofibPrelude.Cons(q2, t3);
        return NofibPrelude.Cons(tmp, tmp1)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static foldr(f12, z, xs7) {
    let param0, param1, h, t3, tmp;
    if (xs7 instanceof NofibPrelude.Nil.class) {
      return z
    } else if (xs7 instanceof NofibPrelude.Cons.class) {
      param0 = xs7.head;
      param1 = xs7.tail;
      h = param0;
      t3 = param1;
      tmp = NofibPrelude.foldr(f12, z, t3);
      return runtime.safeCall(f12(h, tmp))
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static foldl1(f13, ls14) {
    let param0, param1, x9, xs8;
    if (ls14 instanceof NofibPrelude.Cons.class) {
      param0 = ls14.head;
      param1 = ls14.tail;
      x9 = param0;
      xs8 = param1;
      return NofibPrelude.foldl(f13, x9, xs8)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static foldr1(f14, ls15) {
    let param0, param1, x9, xs8, x10, tmp;
    if (ls15 instanceof NofibPrelude.Cons.class) {
      param0 = ls15.head;
      param1 = ls15.tail;
      x10 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return x10
      } else {
        x9 = param0;
        xs8 = param1;
        tmp = NofibPrelude.foldr1(f14, xs8);
        return runtime.safeCall(f14(x9, tmp))
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static maximum(xs8) {
    return NofibPrelude.foldl1(lambda1, xs8)
  } 
  static nubBy(eq, ls16) {
    let param0, param1, h, t3, tmp, tmp1, lambda$this;
    if (ls16 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls16 instanceof NofibPrelude.Cons.class) {
      param0 = ls16.head;
      param1 = ls16.tail;
      h = param0;
      t3 = param1;
      lambda$this = runtime.safeCall(lambda2(eq, h));
      tmp = NofibPrelude.filter(lambda$this, t3);
      tmp1 = NofibPrelude.nubBy(eq, tmp);
      return NofibPrelude.Cons(h, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static zipWith(f15, xss, yss) {
    let param0, param1, x9, xs9, param01, param11, y1, ys5, tmp, tmp1;
    if (xss instanceof NofibPrelude.Cons.class) {
      param0 = xss.head;
      param1 = xss.tail;
      x9 = param0;
      xs9 = param1;
      if (yss instanceof NofibPrelude.Cons.class) {
        param01 = yss.head;
        param11 = yss.tail;
        y1 = param01;
        ys5 = param11;
        tmp = runtime.safeCall(f15(x9, y1));
        tmp1 = NofibPrelude.zipWith(f15, xs9, ys5);
        return NofibPrelude.Cons(tmp, tmp1)
      } else {
        return NofibPrelude.Nil
      }
    } else {
      return NofibPrelude.Nil
    }
  } 
  static deleteBy(eq1, x9, ys5) {
    let param0, param1, y1, ys6, scrut, tmp;
    if (ys5 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ys5 instanceof NofibPrelude.Cons.class) {
      param0 = ys5.head;
      param1 = ys5.tail;
      y1 = param0;
      ys6 = param1;
      scrut = runtime.safeCall(eq1(x9, y1));
      if (scrut === true) {
        return ys6
      } else {
        tmp = NofibPrelude.deleteBy(eq1, x9, ys6);
        return NofibPrelude.Cons(y1, tmp)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static unionBy(eq2, xs9, ys6) {
    let tmp, tmp1, lambda$this;
    tmp = NofibPrelude.nubBy(eq2, ys6);
    lambda$this = runtime.safeCall(lambda3(eq2));
    tmp1 = NofibPrelude.foldl(lambda$this, tmp, xs9);
    return NofibPrelude.append(xs9, tmp1)
  } 
  static union(xs10, ys7) {
    return NofibPrelude.unionBy(lambda4, xs10, ys7)
  } 
  static atIndex(i1, ls17) {
    let param0, param1, h, t3, scrut, tmp;
    if (ls17 instanceof NofibPrelude.Cons.class) {
      param0 = ls17.head;
      param1 = ls17.tail;
      h = param0;
      t3 = param1;
      scrut = i1 == 0;
      if (scrut === true) {
        return h
      } else {
        tmp = i1 - 1;
        return NofibPrelude.atIndex(tmp, t3)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static sum(xs11) {
    return go(xs11, 0)
  } 
  static null_(ls18) {
    if (ls18 instanceof NofibPrelude.Nil.class) {
      return true
    } else {
      return false
    }
  } 
  static replicate(n4, x10) {
    let scrut, tmp, tmp1;
    scrut = n4 == 0;
    if (scrut === true) {
      return NofibPrelude.Nil
    } else {
      tmp = n4 - 1;
      tmp1 = NofibPrelude.replicate(tmp, x10);
      return NofibPrelude.Cons(x10, tmp1)
    }
  } 
  static unzip(l4) {
    return f(l4, NofibPrelude.Nil, NofibPrelude.Nil)
  } 
  static zip3(xs12, ys8, zs) {
    let param0, param1, x11, xs13, param01, param11, y1, ys9, param02, param12, z1, zs1, tmp;
    if (xs12 instanceof NofibPrelude.Cons.class) {
      param0 = xs12.head;
      param1 = xs12.tail;
      x11 = param0;
      xs13 = param1;
      if (ys8 instanceof NofibPrelude.Cons.class) {
        param01 = ys8.head;
        param11 = ys8.tail;
        y1 = param01;
        ys9 = param11;
        if (zs instanceof NofibPrelude.Cons.class) {
          param02 = zs.head;
          param12 = zs.tail;
          z1 = param02;
          zs1 = param12;
          tmp = NofibPrelude.zip3(xs13, ys9, zs1);
          return NofibPrelude.Cons([
            x11,
            y1,
            z1
          ], tmp)
        } else {
          return NofibPrelude.Nil
        }
      } else {
        return NofibPrelude.Nil
      }
    } else {
      return NofibPrelude.Nil
    }
  } 
  static transpose(xss1) {
    let param0, param1, param01, param11, x11, xs13, xss2, scrut, first1, first0, hds, tls, xss3, tmp;
    if (xss1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xss1 instanceof NofibPrelude.Cons.class) {
      param0 = xss1.head;
      param1 = xss1.tail;
      if (param0 instanceof NofibPrelude.Nil.class) {
        xss3 = param1;
        return NofibPrelude.transpose(xss3)
      } else if (param0 instanceof NofibPrelude.Cons.class) {
        param01 = param0.head;
        param11 = param0.tail;
        x11 = param01;
        xs13 = param11;
        xss2 = param1;
        tmp = lscomp(xss2);
        scrut = NofibPrelude.unzip(tmp);
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first0 = scrut[0];
          first1 = scrut[1];
          hds = first0;
          tls = first1;
          return combine(x11, hds, xs13, tls)
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
  static break_(p3, ls19) {
    let param0, param1, x11, xs13, scrut, first1, first0, ys9, zs1, scrut1, tmp, tmp1;
    if (ls19 instanceof NofibPrelude.Nil.class) {
      return [
        NofibPrelude.Nil,
        NofibPrelude.Nil
      ]
    } else if (ls19 instanceof NofibPrelude.Cons.class) {
      param0 = ls19.head;
      param1 = ls19.tail;
      x11 = param0;
      xs13 = param1;
      scrut1 = runtime.safeCall(p3(x11));
      if (scrut1 === true) {
        tmp = NofibPrelude.Cons(x11, xs13);
        return [
          NofibPrelude.Nil,
          tmp
        ]
      } else {
        scrut = NofibPrelude.break_(p3, xs13);
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first0 = scrut[0];
          first1 = scrut[1];
          ys9 = first0;
          zs1 = first1;
          tmp1 = NofibPrelude.Cons(x11, ys9);
          return [
            tmp1,
            zs1
          ]
        } else {
          throw new globalThis.Error("match error");
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static flatMap(f16, ls20) {
    let param0, param1, h, t3, tmp, tmp1;
    if (ls20 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls20 instanceof NofibPrelude.Cons.class) {
      param0 = ls20.head;
      param1 = ls20.tail;
      h = param0;
      t3 = param1;
      tmp = runtime.safeCall(f16(h));
      tmp1 = NofibPrelude.flatMap(f16, t3);
      return NofibPrelude.append(tmp, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static map_lz(f17, ls21) {
    let tmp;
    tmp = runtime.safeCall(lambda5(f17, ls21));
    return NofibPrelude.lazy(tmp)
  } 
  static filter_lz(p4, ls22) {
    let tmp;
    tmp = runtime.safeCall(lambda6(p4, ls22));
    return NofibPrelude.Lazy(tmp)
  } 
  static nubBy_lz(eq3, ls23) {
    let tmp;
    tmp = runtime.safeCall(lambda7(eq3, ls23));
    return NofibPrelude.Lazy(tmp)
  } 
  static nub_lz(ls24) {
    return NofibPrelude.nubBy_lz(lambda9, ls24)
  } 
  static take_lz(n5, ls25) {
    let scrut, scrut1, param0, param1, h, t3, tmp, tmp1;
    scrut = n5 > 0;
    if (scrut === true) {
      scrut1 = NofibPrelude.force(ls25);
      if (scrut1 instanceof NofibPrelude.LzNil.class) {
        return NofibPrelude.Nil
      } else if (scrut1 instanceof NofibPrelude.LzCons.class) {
        param0 = scrut1.head;
        param1 = scrut1.tail;
        h = param0;
        t3 = param1;
        tmp = n5 - 1;
        tmp1 = NofibPrelude.take_lz(tmp, t3);
        return NofibPrelude.Cons(h, tmp1)
      } else {
        return NofibPrelude.Nil
      }
    } else {
      return NofibPrelude.Nil
    }
  } 
  static take_lz_lz(n6, ls26) {
    let tmp;
    tmp = runtime.safeCall(lambda10(n6, ls26));
    return NofibPrelude.lazy(tmp)
  } 
  static drop_lz(n7, ls27) {
    let scrut, param0, param1, h, t3, scrut1, tmp;
    scrut1 = n7 <= 0;
    if (scrut1 === true) {
      return ls27
    } else {
      scrut = NofibPrelude.force(ls27);
      if (scrut instanceof NofibPrelude.LzNil.class) {
        return NofibPrelude.lazy(lambda11)
      } else if (scrut instanceof NofibPrelude.LzCons.class) {
        param0 = scrut.head;
        param1 = scrut.tail;
        h = param0;
        t3 = param1;
        tmp = n7 - 1;
        return NofibPrelude.drop_lz(tmp, t3)
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  static splitAt_lz(n8, ls28) {
    let tmp, tmp1;
    tmp = NofibPrelude.take_lz(n8, ls28);
    tmp1 = NofibPrelude.drop_lz(n8, ls28);
    return [
      tmp,
      tmp1
    ]
  } 
  static zip_lz_nl(xs13, ys9) {
    let scrut, param0, param1, x11, xs14, param01, param11, y1, ys10, tmp;
    scrut = NofibPrelude.force(xs13);
    if (scrut instanceof NofibPrelude.LzCons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      x11 = param0;
      xs14 = param1;
      if (ys9 instanceof NofibPrelude.Cons.class) {
        param01 = ys9.head;
        param11 = ys9.tail;
        y1 = param01;
        ys10 = param11;
        tmp = NofibPrelude.zip_lz_nl(xs14, ys10);
        return NofibPrelude.Cons([
          x11,
          y1
        ], tmp)
      } else {
        return NofibPrelude.Nil
      }
    } else {
      return NofibPrelude.Nil
    }
  } 
  static zip_lz_lz(xs14, ys10) {
    let scrut, param0, param1, x11, xs15, scrut1, param01, param11, y1, ys11, lambda$this;
    scrut = NofibPrelude.force(xs14);
    if (scrut instanceof NofibPrelude.LzCons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      x11 = param0;
      xs15 = param1;
      scrut1 = NofibPrelude.force(ys10);
      if (scrut1 instanceof NofibPrelude.LzCons.class) {
        param01 = scrut1.head;
        param11 = scrut1.tail;
        y1 = param01;
        ys11 = param11;
        lambda$this = runtime.safeCall(lambda12(x11, xs15, y1, ys11));
        return NofibPrelude.lazy(lambda$this)
      } else {
        return NofibPrelude.lazy(lambda13)
      }
    } else {
      return NofibPrelude.lazy(lambda14)
    }
  } 
  static zipWith_lz_lz(f18, xss2, yss1) {
    let tmp;
    tmp = runtime.safeCall(lambda15(f18, xss2, yss1));
    return NofibPrelude.lazy(tmp)
  } 
  static zipWith_lz_nl(f19, xss3, yss2) {
    let scrut, param0, param1, x11, xs15, param01, param11, y1, ys11, tmp, tmp1;
    scrut = NofibPrelude.force(xss3);
    if (scrut instanceof NofibPrelude.LzCons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      x11 = param0;
      xs15 = param1;
      if (yss2 instanceof NofibPrelude.Cons.class) {
        param01 = yss2.head;
        param11 = yss2.tail;
        y1 = param01;
        ys11 = param11;
        tmp = runtime.safeCall(f19(x11, y1));
        tmp1 = NofibPrelude.zipWith_lz_nl(f19, xs15, ys11);
        return NofibPrelude.Cons(tmp, tmp1)
      } else {
        return NofibPrelude.Nil
      }
    } else {
      return NofibPrelude.Nil
    }
  } 
  static iterate(f20, x11) {
    let tmp;
    tmp = runtime.safeCall(lambda16(f20, x11));
    return NofibPrelude.lazy(tmp)
  } 
  static append_nl_lz(xs15, ys11) {
    let param0, param1, h, t3, lambda$this;
    if (xs15 instanceof NofibPrelude.Nil.class) {
      return ys11
    } else if (xs15 instanceof NofibPrelude.Cons.class) {
      param0 = xs15.head;
      param1 = xs15.tail;
      h = param0;
      t3 = param1;
      lambda$this = runtime.safeCall(lambda17(ys11, h, t3));
      return NofibPrelude.lazy(lambda$this)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static append_lz_lz(xs16, ys12) {
    let tmp;
    tmp = runtime.safeCall(lambda18(xs16, ys12));
    return NofibPrelude.lazy(tmp)
  } 
  static replicate_lz(n9, x12) {
    let scrut, lambda$this;
    scrut = n9 == 0;
    if (scrut === true) {
      return NofibPrelude.lazy(lambda19)
    } else {
      lambda$this = runtime.safeCall(lambda20(n9, x12));
      return NofibPrelude.lazy(lambda$this)
    }
  } 
  static enumFrom(a13) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda21(a13));
    return NofibPrelude.lazy(lambda$this)
  } 
  static head_lz(ls29) {
    let scrut, param0, param1, h, t3;
    scrut = NofibPrelude.force(ls29);
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
  static repeat(x13) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda22(x13));
    return NofibPrelude.lazy(lambda$this)
  } 
  static stringOfFloat(x14) {
    return x14 + ""
  } 
  static stringOfInt(x15) {
    return x15 + ""
  } 
  static stringConcat(x16, y1) {
    return x16 + y1
  } 
  static stringListConcat(ls30) {
    let param0, param1, h, t3, tmp;
    if (ls30 instanceof NofibPrelude.Nil.class) {
      return ""
    } else if (ls30 instanceof NofibPrelude.Cons.class) {
      param0 = ls30.head;
      param1 = ls30.tail;
      h = param0;
      t3 = param1;
      tmp = NofibPrelude.stringListConcat(t3);
      return NofibPrelude.stringConcat(h, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static sqrt(x17) {
    return runtime.safeCall(globalThis.Math.sqrt(x17))
  } 
  static tan(x18) {
    return runtime.safeCall(globalThis.Math.tan(x18))
  } 
  static sin(x19) {
    return runtime.safeCall(globalThis.Math.sin(x19))
  } 
  static cos(x20) {
    return runtime.safeCall(globalThis.Math.cos(x20))
  } 
  static round(x21) {
    return runtime.safeCall(globalThis.Math.round(x21))
  } 
  static int_of_char(x22) {
    return runtime.safeCall(x22.charCodeAt(0))
  } 
  static nofibStringToList(s1) {
    return go$(s1, 0)
  } 
  static nofibListToString(ls31) {
    let param0, param1, h, t3, tmp;
    if (ls31 instanceof NofibPrelude.Nil.class) {
      return ""
    } else if (ls31 instanceof NofibPrelude.Cons.class) {
      param0 = ls31.head;
      param1 = ls31.tail;
      h = param0;
      t3 = param1;
      tmp = NofibPrelude.nofibListToString(t3);
      return h + tmp
    } else {
      throw new globalThis.Error("match error");
    }
  }
  static toString() { return "NofibPrelude"; }
};
let NofibPrelude = NofibPrelude1; export default NofibPrelude;
