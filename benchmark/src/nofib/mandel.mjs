import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let infiniteMandel, walkIt, lscomp2, windowToViewport, lscomp1, prettyRGB, mandel1, lambda, lambda1, lambda2, infiniteMandel$, lambda$, lambda$1, walkIt$, lambda$2, lscomp1$, lscomp2$, windowToViewport$, prettyRGB$;
prettyRGB$ = function prettyRGB$(lIMIT, s) {
  let t, tmp;
  tmp = lIMIT - s;
  t = tmp;
  return [
    s,
    t,
    t
  ]
};
prettyRGB = function prettyRGB(lIMIT) {
  return (s) => {
    return prettyRGB$(lIMIT, s)
  }
};
windowToViewport$ = function windowToViewport$(x, y, x_, y_, screenX, screenY, s, t) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  tmp = x_ - x;
  tmp1 = s * tmp;
  tmp2 = tmp1 / screenX;
  tmp3 = x + tmp2;
  tmp4 = y_ - y;
  tmp5 = t * tmp4;
  tmp6 = tmp5 / screenY;
  tmp7 = y + tmp6;
  return mandel1.Complex(tmp3, tmp7)
};
windowToViewport = function windowToViewport(x, y, x_, y_, screenX, screenY) {
  return (s, t) => {
    return windowToViewport$(x, y, x_, y_, screenX, screenY, s, t)
  }
};
lscomp2$ = function lscomp2$(x, y, x_, y_, screenX, screenY, t, t1, ls2) {
  let param0, param1, s, t2, tmp, tmp1;
  if (ls2 instanceof NofibPrelude.Nil.class) {
    return lscomp1$(x, y, x_, y_, screenX, screenY, t1)
  } else if (ls2 instanceof NofibPrelude.Cons.class) {
    param0 = ls2.head;
    param1 = ls2.tail;
    s = param0;
    t2 = param1;
    tmp = windowToViewport$(x, y, x_, y_, screenX, screenY, s, t);
    tmp1 = lscomp2$(x, y, x_, y_, screenX, screenY, t, t1, t2);
    return NofibPrelude.Cons(tmp, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp2 = function lscomp2(x, y, x_, y_, screenX, screenY, t, t1) {
  return (ls2) => {
    return lscomp2$(x, y, x_, y_, screenX, screenY, t, t1, ls2)
  }
};
lscomp1$ = function lscomp1$(x, y, x_, y_, screenX, screenY, ls1) {
  let param0, param1, t, t1, tmp;
  if (ls1 instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls1 instanceof NofibPrelude.Cons.class) {
    param0 = ls1.head;
    param1 = ls1.tail;
    t = param0;
    t1 = param1;
    tmp = NofibPrelude.enumFromTo(1, screenX);
    return lscomp2$(x, y, x_, y_, screenX, screenY, t, t1, tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp1 = function lscomp1(x, y, x_, y_, screenX, screenY) {
  return (ls1) => {
    return lscomp1$(x, y, x_, y_, screenX, screenY, ls1)
  }
};
lambda$2 = function lambda$(limit, radius, c) {
  return mandel1.whenDiverge(limit, radius, c)
};
lambda2 = (undefined, function (limit, radius) {
  return (c) => {
    return lambda$2(limit, radius, c)
  }
});
walkIt$ = function walkIt$(radius, ls) {
  let scrut, param0, param1, x, xs, scrut1, tmp;
  scrut = NofibPrelude.force(ls);
  if (scrut instanceof NofibPrelude.LzNil.class) {
    return 0
  } else if (scrut instanceof NofibPrelude.LzCons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    x = param0;
    xs = param1;
    scrut1 = mandel1.diverge(x, radius);
    if (scrut1 === true) {
      return 0
    } else {
      tmp = walkIt$(radius, xs);
      return 1 + tmp
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
walkIt = function walkIt(radius) {
  return (ls) => {
    return walkIt$(radius, ls)
  }
};
lambda$1 = function lambda$(c, z) {
  let tmp;
  tmp = mandel1.comp_times(z, z);
  return mandel1.comp_plus(tmp, c)
};
lambda1 = (undefined, function (c) {
  return (z) => {
    return lambda$1(c, z)
  }
});
lambda$ = function lambda$(c) {
  let tmp, tmp1, lambda$this;
  tmp = infiniteMandel$(c);
  lambda$this = runtime.safeCall(lambda1(c));
  tmp1 = NofibPrelude.map_lz(lambda$this, tmp);
  return NofibPrelude.LzCons(c, tmp1)
};
lambda = (undefined, function (c) {
  return () => {
    return lambda$(c)
  }
});
infiniteMandel$ = function infiniteMandel$(c) {
  let tmp;
  tmp = runtime.safeCall(lambda(c));
  return NofibPrelude.lazy(tmp)
};
infiniteMandel = function infiniteMandel(c) {
  return () => {
    return infiniteMandel$(c)
  }
};
mandel1 = class mandel {
  static {
    mandel1 = mandel;
    let lambda3;
    this.Pixmap = function Pixmap(a1, b1, c1, d1) {
      return new Pixmap.class(a1, b1, c1, d1);
    };
    this.Pixmap.class = class Pixmap {
      constructor(a, b, c, d) {
        this.a = a;
        this.b = b;
        this.c = c;
        this.d = d;
      }
      toString() { return "Pixmap(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ", " + globalThis.Predef.render(this.c) + ", " + globalThis.Predef.render(this.d) + ")"; }
    };
    this.Complex = function Complex(r1, i1) {
      return new Complex.class(r1, i1);
    };
    this.Complex.class = class Complex {
      constructor(r, i) {
        this.r = r;
        this.i = i;
      }
      toString() { return "Complex(" + globalThis.Predef.render(this.r) + ", " + globalThis.Predef.render(this.i) + ")"; }
    };
    lambda3 = (undefined, function () {
      let tmp;
      tmp = mandel.testMandel_nofib(0);
      return runtime.safeCall(tmp.toString())
    });
    BenchmarkPrelude.benchmark(lambda3)
  }
  static createPixmap(width, height, max, colours) {
    return mandel.Pixmap(width, height, max, colours)
  } 
  static comp_magnitude(c) {
    let param0, param1, a, b, tmp, tmp1, tmp2;
    if (c instanceof mandel.Complex.class) {
      param0 = c.r;
      param1 = c.i;
      a = param0;
      b = param1;
      tmp = a * a;
      tmp1 = b * b;
      tmp2 = tmp + tmp1;
      return NofibPrelude.sqrt(tmp2)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static comp_times(x, y) {
    let param0, param1, a, b, param01, param11, c1, d, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    if (x instanceof mandel.Complex.class) {
      param0 = x.r;
      param1 = x.i;
      a = param0;
      b = param1;
      if (y instanceof mandel.Complex.class) {
        param01 = y.r;
        param11 = y.i;
        c1 = param01;
        d = param11;
        tmp = a * c1;
        tmp1 = b * d;
        tmp2 = tmp - tmp1;
        tmp3 = a * d;
        tmp4 = b * c1;
        tmp5 = tmp3 + tmp4;
        return mandel.Complex(tmp2, tmp5)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static comp_plus(x1, y1) {
    let param0, param1, a, b, param01, param11, c1, d, tmp, tmp1;
    if (x1 instanceof mandel.Complex.class) {
      param0 = x1.r;
      param1 = x1.i;
      a = param0;
      b = param1;
      if (y1 instanceof mandel.Complex.class) {
        param01 = y1.r;
        param11 = y1.i;
        c1 = param01;
        d = param11;
        tmp = a + c1;
        tmp1 = b + d;
        return mandel.Complex(tmp, tmp1)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static mandel(c1) {
    return infiniteMandel$(c1)
  } 
  static diverge(cmplx, radius) {
    let tmp;
    tmp = mandel.comp_magnitude(cmplx);
    return tmp > radius
  } 
  static whenDiverge(limit, radius1, c2) {
    let tmp, tmp1;
    tmp = mandel.mandel(c2);
    tmp1 = NofibPrelude.take_lz_lz(limit, tmp);
    return walkIt$(radius1, tmp1)
  } 
  static parallelMandel(mat, limit1, radius2) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda2(limit1, radius2));
    return NofibPrelude.map(lambda$this, mat)
  } 
  static mandelset(x2, y2, x_, y_, screenX, screenY, lIMIT) {
    let result, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, prettyRGB$this;
    tmp = NofibPrelude.enumFromTo(1, screenY);
    tmp1 = lscomp1$(x2, y2, x_, y_, screenX, screenY, tmp);
    tmp2 = x_ - x2;
    tmp3 = y_ - y2;
    tmp4 = NofibPrelude.max(tmp2, tmp3);
    tmp5 = tmp4 / 2;
    tmp6 = mandel.parallelMandel(tmp1, lIMIT, tmp5);
    result = tmp6;
    prettyRGB$this = runtime.safeCall(prettyRGB(lIMIT));
    tmp7 = NofibPrelude.map(prettyRGB$this, result);
    return mandel.createPixmap(screenX, screenY, lIMIT, tmp7)
  } 
  static testMandel_nofib(dummy) {
    let minx, miny, maxx, maxy, screenX1, screenY1, limit2, tmp, tmp1;
    tmp = - 2.0;
    minx = tmp;
    tmp1 = - 2.0;
    miny = tmp1;
    maxx = 2.0;
    maxy = 2.0;
    screenX1 = 25;
    screenY1 = 25;
    limit2 = 75;
    return mandel.mandelset(minx, miny, maxx, maxy, screenX1, screenY1, limit2)
  }
  static toString() { return "mandel"; }
};
let mandel = mandel1; export default mandel;
