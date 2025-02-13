import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import Predef from "./../../../hkmc2/shared/src/test/mlscript-compile/Predef.mjs";
let NofibPrelude1;
NofibPrelude1 = class NofibPrelude {
  static {
    this.Option = class Option {
      constructor() {}
      toString() { return "Option"; }
    };
    this.Some = function Some(x1) { return new Some.class(x1); };
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
    this.Lazy = function Lazy(init1) { return new Lazy.class(init1); };
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
    this.Cons = function Cons(head1, tail1) { return new Cons.class(head1, tail1); };
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
    this.LzCons = function LzCons(head1, tail1) { return new LzCons.class(head1, tail1); };
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
  static compose(f, g) {
    return (x2) => {
      let tmp;
      tmp = runtime.safeCall(g(x2));
      return runtime.safeCall(f(tmp))
    }
  } 
  static snd(x2) {
    let first1, first0, f1, s1;
    if (globalThis.Array.isArray(x2) && x2.length === 2) {
      first0 = x2[0];
      first1 = x2[1];
      f1 = first0;
      s1 = first1;
      return s1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static fst(x3) {
    let first1, first0, f1, s1;
    if (globalThis.Array.isArray(x3) && x3.length === 2) {
      first0 = x3[0];
      first1 = x3[1];
      f1 = first0;
      s1 = first1;
      return f1
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static until(p, f1, i) {
    let scrut, tmp;
    scrut = runtime.safeCall(p(i));
    if (scrut === true) {
      return i
    } else {
      tmp = runtime.safeCall(f1(i));
      return NofibPrelude.until(p, f1, tmp)
    }
  } 
  static flip(f2, x4, y) {
    let tmp;
    tmp = runtime.safeCall(f2(y));
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
  static head(l) {
    let param0, param1, h, t;
    if (l instanceof NofibPrelude.Cons.class) {
      param0 = l.head;
      param1 = l.tail;
      h = param0;
      t = param1;
      return h
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static tail(l1) {
    let param0, param1, h, t;
    if (l1 instanceof NofibPrelude.Cons.class) {
      param0 = l1.head;
      param1 = l1.tail;
      h = param0;
      t = param1;
      return t
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static while_(p1, f3, x6) {
    let scrut, tmp;
    scrut = runtime.safeCall(p1(x6));
    if (scrut === true) {
      tmp = runtime.safeCall(f3(x6));
      return NofibPrelude.while_(p1, f3, tmp)
    } else {
      return x6
    }
  } 
  static reverse(l2) {
    let r;
    r = function r(l$_, l3) {
      let param0, param1, x7, xs1, tmp;
      if (l3 instanceof NofibPrelude.Cons.class) {
        param0 = l3.head;
        param1 = l3.tail;
        x7 = param0;
        xs1 = param1;
        tmp = NofibPrelude.Cons(x7, l$_);
        return r(tmp, xs1)
      } else {
        return l$_
      }
    };
    return r(NofibPrelude.Nil, l2)
  } 
  static map(f4, xs1) {
    let param0, param1, x7, xs2, tmp, tmp1;
    if (xs1 instanceof NofibPrelude.Cons.class) {
      param0 = xs1.head;
      param1 = xs1.tail;
      x7 = param0;
      xs2 = param1;
      tmp = runtime.safeCall(f4(x7));
      tmp1 = NofibPrelude.map(f4, xs2);
      return NofibPrelude.Cons(tmp, tmp1)
    } else if (xs1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static listLen(ls1) {
    let l3;
    l3 = function l(ls2, a9) {
      let param0, param1, h, t, tmp;
      if (ls2 instanceof NofibPrelude.Nil.class) {
        return a9
      } else if (ls2 instanceof NofibPrelude.Cons.class) {
        param0 = ls2.head;
        param1 = ls2.tail;
        h = param0;
        t = param1;
        tmp = a9 + 1;
        return l3(t, tmp)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    return l3(ls1, 0)
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
  static listEqBy(f5, a9, b8) {
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
        tmp = runtime.safeCall(f5(x7, y1));
        tmp1 = NofibPrelude.listEqBy(f5, xs3, ys2);
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
  static filter(f6, ls8) {
    let param0, param1, h, t3, scrut, tmp;
    if (ls8 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls8 instanceof NofibPrelude.Cons.class) {
      param0 = ls8.head;
      param1 = ls8.tail;
      h = param0;
      t3 = param1;
      scrut = runtime.safeCall(f6(h));
      if (scrut === true) {
        tmp = NofibPrelude.filter(f6, t3);
        return NofibPrelude.Cons(h, tmp)
      } else {
        return NofibPrelude.filter(f6, t3)
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
  static dropWhile(f7, ls11) {
    let param0, param1, h, t3, scrut;
    if (ls11 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls11 instanceof NofibPrelude.Cons.class) {
      param0 = ls11.head;
      param1 = ls11.tail;
      h = param0;
      t3 = param1;
      scrut = runtime.safeCall(f7(h));
      if (scrut === true) {
        return NofibPrelude.dropWhile(f7, t3)
      } else {
        return NofibPrelude.Cons(h, t3)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static foldl(f8, a12, xs6) {
    let param0, param1, h, t3, tmp;
    if (xs6 instanceof NofibPrelude.Nil.class) {
      return a12
    } else if (xs6 instanceof NofibPrelude.Cons.class) {
      param0 = xs6.head;
      param1 = xs6.tail;
      h = param0;
      t3 = param1;
      tmp = runtime.safeCall(f8(a12, h));
      return NofibPrelude.foldl(f8, tmp, t3)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static scanl(f9, q, ls12) {
    let param0, param1, x9, xs7, tmp, tmp1;
    if (ls12 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(q, NofibPrelude.Nil)
    } else if (ls12 instanceof NofibPrelude.Cons.class) {
      param0 = ls12.head;
      param1 = ls12.tail;
      x9 = param0;
      xs7 = param1;
      tmp = runtime.safeCall(f9(q, x9));
      tmp1 = NofibPrelude.scanl(f9, tmp, xs7);
      return NofibPrelude.Cons(q, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static scanr(f10, q1, ls13) {
    let param0, param1, x9, xs7, scrut, param01, param11, q2, t3, tmp, tmp1;
    if (ls13 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(q1, NofibPrelude.Nil)
    } else if (ls13 instanceof NofibPrelude.Cons.class) {
      param0 = ls13.head;
      param1 = ls13.tail;
      x9 = param0;
      xs7 = param1;
      scrut = NofibPrelude.scanr(f10, q1, xs7);
      if (scrut instanceof NofibPrelude.Cons.class) {
        param01 = scrut.head;
        param11 = scrut.tail;
        q2 = param01;
        t3 = param11;
        tmp = runtime.safeCall(f10(x9, q2));
        tmp1 = NofibPrelude.Cons(q2, t3);
        return NofibPrelude.Cons(tmp, tmp1)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static foldr(f11, z, xs7) {
    let param0, param1, h, t3, tmp;
    if (xs7 instanceof NofibPrelude.Nil.class) {
      return z
    } else if (xs7 instanceof NofibPrelude.Cons.class) {
      param0 = xs7.head;
      param1 = xs7.tail;
      h = param0;
      t3 = param1;
      tmp = NofibPrelude.foldr(f11, z, t3);
      return runtime.safeCall(f11(h, tmp))
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static foldl1(f12, ls14) {
    let param0, param1, x9, xs8;
    if (ls14 instanceof NofibPrelude.Cons.class) {
      param0 = ls14.head;
      param1 = ls14.tail;
      x9 = param0;
      xs8 = param1;
      return NofibPrelude.foldl(f12, x9, xs8)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static foldr1(f13, ls15) {
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
        tmp = NofibPrelude.foldr1(f13, xs8);
        return runtime.safeCall(f13(x9, tmp))
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static maximum(xs8) {
    return NofibPrelude.foldl1((x9, y1) => {
      let scrut;
      scrut = x9 > y1;
      if (scrut === true) {
        return x9
      } else {
        return y1
      }
    }, xs8)
  } 
  static nubBy(eq, ls16) {
    let param0, param1, h, t3, tmp, tmp1;
    if (ls16 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls16 instanceof NofibPrelude.Cons.class) {
      param0 = ls16.head;
      param1 = ls16.tail;
      h = param0;
      t3 = param1;
      tmp = NofibPrelude.filter((y1) => {
        let tmp2;
        tmp2 = runtime.safeCall(eq(h, y1));
        return Predef.not(tmp2)
      }, t3);
      tmp1 = NofibPrelude.nubBy(eq, tmp);
      return NofibPrelude.Cons(h, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static zipWith(f14, xss, yss) {
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
        tmp = runtime.safeCall(f14(x9, y1));
        tmp1 = NofibPrelude.zipWith(f14, xs9, ys5);
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
    let tmp, tmp1;
    tmp = NofibPrelude.nubBy(eq2, ys6);
    tmp1 = NofibPrelude.foldl((acc, y1) => {
      return NofibPrelude.deleteBy(eq2, y1, acc)
    }, tmp, xs9);
    return NofibPrelude.append(xs9, tmp1)
  } 
  static union(xs10, ys7) {
    return NofibPrelude.unionBy((x10, y1) => {
      return x10 == y1
    }, xs10, ys7)
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
    let go;
    go = function go(xs12, a13) {
      let param0, param1, h, t3, tmp;
      if (xs12 instanceof NofibPrelude.Nil.class) {
        return a13
      } else if (xs12 instanceof NofibPrelude.Cons.class) {
        param0 = xs12.head;
        param1 = xs12.tail;
        h = param0;
        t3 = param1;
        tmp = a13 + h;
        return go(t3, tmp)
      } else {
        throw new globalThis.Error("match error");
      }
    };
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
  static unzip(l3) {
    let f15;
    f15 = function f(l4, a13, b11) {
      let param0, param1, first1, first0, x11, y1, t3, tmp, tmp1, tmp2, tmp3;
      if (l4 instanceof NofibPrelude.Nil.class) {
        tmp = NofibPrelude.reverse(a13);
        tmp1 = NofibPrelude.reverse(b11);
        return [
          tmp,
          tmp1
        ]
      } else if (l4 instanceof NofibPrelude.Cons.class) {
        param0 = l4.head;
        param1 = l4.tail;
        if (globalThis.Array.isArray(param0) && param0.length === 2) {
          first0 = param0[0];
          first1 = param0[1];
          x11 = first0;
          y1 = first1;
          t3 = param1;
          tmp2 = NofibPrelude.Cons(x11, a13);
          tmp3 = NofibPrelude.Cons(y1, b11);
          return f15(t3, tmp2, tmp3)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    return f15(l3, NofibPrelude.Nil, NofibPrelude.Nil)
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
    let lscomp, combine, param0, param1, param01, param11, x11, xs13, xss2, scrut, first1, first0, hds, tls, xss3, tmp;
    lscomp = function lscomp(ls19) {
      let param02, param12, h, t3, param03, param13, hd, tl, tmp1;
      if (ls19 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls19 instanceof NofibPrelude.Cons.class) {
        param02 = ls19.head;
        param12 = ls19.tail;
        h = param02;
        t3 = param12;
        if (h instanceof NofibPrelude.Cons.class) {
          param03 = h.head;
          param13 = h.tail;
          hd = param03;
          tl = param13;
          tmp1 = lscomp(t3);
          return NofibPrelude.Cons([
            hd,
            tl
          ], tmp1)
        } else {
          return lscomp(t3)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    combine = function combine(y1, h, ys9, t3) {
      let tmp1, tmp2, tmp3;
      tmp1 = NofibPrelude.Cons(y1, h);
      tmp2 = NofibPrelude.Cons(ys9, t3);
      tmp3 = NofibPrelude.transpose(tmp2);
      return NofibPrelude.Cons(tmp1, tmp3)
    };
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
  static flatMap(f15, ls20) {
    let param0, param1, h, t3, tmp, tmp1;
    if (ls20 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls20 instanceof NofibPrelude.Cons.class) {
      param0 = ls20.head;
      param1 = ls20.tail;
      h = param0;
      t3 = param1;
      tmp = runtime.safeCall(f15(h));
      tmp1 = NofibPrelude.flatMap(f15, t3);
      return NofibPrelude.append(tmp, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static map_lz(f16, ls21) {
    let tmp;
    tmp = () => {
      let scrut, param0, param1, h, t3, tmp1, tmp2;
      scrut = NofibPrelude.force(ls21);
      if (scrut instanceof NofibPrelude.LzNil.class) {
        return NofibPrelude.LzNil
      } else if (scrut instanceof NofibPrelude.LzCons.class) {
        param0 = scrut.head;
        param1 = scrut.tail;
        h = param0;
        t3 = param1;
        tmp1 = runtime.safeCall(f16(h));
        tmp2 = NofibPrelude.map_lz(f16, t3);
        return NofibPrelude.LzCons(tmp1, tmp2)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    return NofibPrelude.lazy(tmp)
  } 
  static filter_lz(p4, ls22) {
    let tmp;
    tmp = () => {
      let scrut, param0, param1, h, t3, scrut1, tmp1, tmp2;
      scrut = NofibPrelude.force(ls22);
      if (scrut instanceof NofibPrelude.LzNil.class) {
        return NofibPrelude.LzNil
      } else if (scrut instanceof NofibPrelude.LzCons.class) {
        param0 = scrut.head;
        param1 = scrut.tail;
        h = param0;
        t3 = param1;
        scrut1 = runtime.safeCall(p4(h));
        if (scrut1 === true) {
          tmp1 = NofibPrelude.filter_lz(p4, t3);
          return NofibPrelude.LzCons(h, tmp1)
        } else {
          tmp2 = NofibPrelude.filter_lz(p4, t3);
          return NofibPrelude.force(tmp2)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    return NofibPrelude.Lazy(tmp)
  } 
  static nubBy_lz(eq3, ls23) {
    let tmp;
    tmp = () => {
      let scrut, param0, param1, h, t3, tmp1, tmp2;
      scrut = NofibPrelude.force(ls23);
      if (scrut instanceof NofibPrelude.LzNil.class) {
        return NofibPrelude.LzNil
      } else if (scrut instanceof NofibPrelude.LzCons.class) {
        param0 = scrut.head;
        param1 = scrut.tail;
        h = param0;
        t3 = param1;
        tmp1 = NofibPrelude.filter_lz((y1) => {
          let tmp3;
          tmp3 = runtime.safeCall(eq3(h, y1));
          return Predef.not(tmp3)
        }, t3);
        tmp2 = NofibPrelude.nubBy_lz(eq3, tmp1);
        return NofibPrelude.LzCons(h, tmp2)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    return NofibPrelude.Lazy(tmp)
  } 
  static nub_lz(ls24) {
    return NofibPrelude.nubBy_lz((x11, y1) => {
      return x11 == y1
    }, ls24)
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
    tmp = () => {
      let scrut, scrut1, param0, param1, h, t3, tmp1, tmp2;
      scrut = n6 > 0;
      if (scrut === true) {
        scrut1 = NofibPrelude.force(ls26);
        if (scrut1 instanceof NofibPrelude.LzNil.class) {
          return NofibPrelude.LzNil
        } else if (scrut1 instanceof NofibPrelude.LzCons.class) {
          param0 = scrut1.head;
          param1 = scrut1.tail;
          h = param0;
          t3 = param1;
          tmp1 = n6 - 1;
          tmp2 = NofibPrelude.take_lz_lz(tmp1, t3);
          return NofibPrelude.LzCons(h, tmp2)
        } else {
          return NofibPrelude.LzNil
        }
      } else {
        return NofibPrelude.LzNil
      }
    };
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
        return NofibPrelude.lazy(() => {
          return NofibPrelude.LzNil
        })
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
    let scrut, param0, param1, x11, xs15, scrut1, param01, param11, y1, ys11;
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
        return NofibPrelude.lazy(() => {
          let tmp;
          tmp = NofibPrelude.zip_lz_lz(xs15, ys11);
          return NofibPrelude.LzCons([
            x11,
            y1
          ], tmp)
        })
      } else {
        return NofibPrelude.lazy(() => {
          return NofibPrelude.LzNil
        })
      }
    } else {
      return NofibPrelude.lazy(() => {
        return NofibPrelude.LzNil
      })
    }
  } 
  static zipWith_lz_lz(f17, xss2, yss1) {
    let tmp;
    tmp = () => {
      let scrut, param0, param1, x11, xs15, scrut1, param01, param11, y1, ys11, tmp1, tmp2;
      scrut = NofibPrelude.force(xss2);
      if (scrut instanceof NofibPrelude.LzCons.class) {
        param0 = scrut.head;
        param1 = scrut.tail;
        x11 = param0;
        xs15 = param1;
        scrut1 = NofibPrelude.force(yss1);
        if (scrut1 instanceof NofibPrelude.LzCons.class) {
          param01 = scrut1.head;
          param11 = scrut1.tail;
          y1 = param01;
          ys11 = param11;
          tmp1 = runtime.safeCall(f17(x11, y1));
          tmp2 = NofibPrelude.zipWith_lz_lz(f17, xs15, ys11);
          return NofibPrelude.LzCons(tmp1, tmp2)
        } else {
          return NofibPrelude.LzNil
        }
      } else {
        return NofibPrelude.LzNil
      }
    };
    return NofibPrelude.lazy(tmp)
  } 
  static zipWith_lz_nl(f18, xss3, yss2) {
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
        tmp = runtime.safeCall(f18(x11, y1));
        tmp1 = NofibPrelude.zipWith_lz_nl(f18, xs15, ys11);
        return NofibPrelude.Cons(tmp, tmp1)
      } else {
        return NofibPrelude.Nil
      }
    } else {
      return NofibPrelude.Nil
    }
  } 
  static iterate(f19, x11) {
    return NofibPrelude.lazy(() => {
      let tmp, tmp1;
      tmp = runtime.safeCall(f19(x11));
      tmp1 = NofibPrelude.iterate(f19, tmp);
      return NofibPrelude.LzCons(x11, tmp1)
    })
  } 
  static append_nl_lz(xs15, ys11) {
    let param0, param1, h, t3;
    if (xs15 instanceof NofibPrelude.Nil.class) {
      return ys11
    } else if (xs15 instanceof NofibPrelude.Cons.class) {
      param0 = xs15.head;
      param1 = xs15.tail;
      h = param0;
      t3 = param1;
      return NofibPrelude.lazy(() => {
        let tmp;
        tmp = NofibPrelude.append_nl_lz(t3, ys11);
        return NofibPrelude.LzCons(h, tmp)
      })
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static append_lz_lz(xs16, ys12) {
    let tmp;
    tmp = () => {
      let scrut, param0, param1, h, t3, tmp1;
      scrut = NofibPrelude.force(xs16);
      if (scrut instanceof NofibPrelude.LzNil.class) {
        return NofibPrelude.force(ys12)
      } else if (scrut instanceof NofibPrelude.LzCons.class) {
        param0 = scrut.head;
        param1 = scrut.tail;
        h = param0;
        t3 = param1;
        tmp1 = NofibPrelude.append_lz_lz(t3, ys12);
        return NofibPrelude.LzCons(h, tmp1)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    return NofibPrelude.lazy(tmp)
  } 
  static replicate_lz(n9, x12) {
    let scrut;
    scrut = n9 == 0;
    if (scrut === true) {
      return NofibPrelude.lazy(() => {
        return NofibPrelude.LzNil
      })
    } else {
      return NofibPrelude.lazy(() => {
        let tmp, tmp1;
        tmp = n9 - 1;
        tmp1 = NofibPrelude.replicate_lz(tmp, x12);
        return NofibPrelude.LzCons(x12, tmp1)
      })
    }
  } 
  static enumFrom(a13) {
    return NofibPrelude.lazy(() => {
      let tmp, tmp1;
      tmp = a13 + 1;
      tmp1 = NofibPrelude.enumFrom(tmp);
      return NofibPrelude.LzCons(a13, tmp1)
    })
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
    return NofibPrelude.lazy(() => {
      let tmp;
      tmp = NofibPrelude.repeat(x13);
      return NofibPrelude.LzCons(x13, tmp)
    })
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
    let go;
    go = function go(i2) {
      let scrut, tmp, tmp1, tmp2;
      scrut = i2 < s1.length;
      if (scrut === true) {
        tmp = runtime.safeCall(s1.charAt(i2));
        tmp1 = i2 + 1;
        tmp2 = go(tmp1);
        return NofibPrelude.Cons(tmp, tmp2)
      } else {
        return NofibPrelude.Nil
      }
    };
    return go(0)
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
