import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let sphere1;
sphere1 = class sphere {
  static #pi;
  static #epsilon;
  static #infinity;
  static #lookat;
  static #vup;
  static #fov;
  static #s2;
  static #testspheres;
  static #testlights;
  static #lookfrom;
  static #background;
  static {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, lambda;
    sphere.#pi = globalThis.Math.PI;
    sphere.#epsilon = 0.000001;
    sphere.#infinity = 100000000.0;
    this.Light = class Light {
      constructor() {}
      toString() { return "Light"; }
    };
    this.Directional = function Directional(x1, y1) {
      return new Directional.class(x1, y1);
    };
    this.Directional.class = class Directional extends sphere.Light {
      constructor(x, y) {
        super();
        this.x = x;
        this.y = y;
      }
      toString() { return "Directional(" + globalThis.Predef.render(this.x) + ", " + globalThis.Predef.render(this.y) + ")"; }
    };
    this.Point = function Point(x1, y1) {
      return new Point.class(x1, y1);
    };
    this.Point.class = class Point extends sphere.Light {
      constructor(x, y) {
        super();
        this.x = x;
        this.y = y;
      }
      toString() { return "Point(" + globalThis.Predef.render(this.x) + ", " + globalThis.Predef.render(this.y) + ")"; }
    };
    this.Surfspec = class Surfspec {
      constructor() {}
      toString() { return "Surfspec"; }
    };
    this.Ambient = function Ambient(v1) {
      return new Ambient.class(v1);
    };
    this.Ambient.class = class Ambient extends sphere.Surfspec {
      constructor(v) {
        super();
        this.v = v;
      }
      toString() { return "Ambient(" + globalThis.Predef.render(this.v) + ")"; }
    };
    this.Diffuse = function Diffuse(v1) {
      return new Diffuse.class(v1);
    };
    this.Diffuse.class = class Diffuse extends sphere.Surfspec {
      constructor(v) {
        super();
        this.v = v;
      }
      toString() { return "Diffuse(" + globalThis.Predef.render(this.v) + ")"; }
    };
    this.Specular = function Specular(v1) {
      return new Specular.class(v1);
    };
    this.Specular.class = class Specular extends sphere.Surfspec {
      constructor(v) {
        super();
        this.v = v;
      }
      toString() { return "Specular(" + globalThis.Predef.render(this.v) + ")"; }
    };
    this.Specpow = function Specpow(v1) {
      return new Specpow.class(v1);
    };
    this.Specpow.class = class Specpow extends sphere.Surfspec {
      constructor(v) {
        super();
        this.v = v;
      }
      toString() { return "Specpow(" + globalThis.Predef.render(this.v) + ")"; }
    };
    this.Reflect = function Reflect(v1) {
      return new Reflect.class(v1);
    };
    this.Reflect.class = class Reflect extends sphere.Surfspec {
      constructor(v) {
        super();
        this.v = v;
      }
      toString() { return "Reflect(" + globalThis.Predef.render(this.v) + ")"; }
    };
    this.Transmit = function Transmit(v1) {
      return new Transmit.class(v1);
    };
    this.Transmit.class = class Transmit extends sphere.Surfspec {
      constructor(v) {
        super();
        this.v = v;
      }
      toString() { return "Transmit(" + globalThis.Predef.render(this.v) + ")"; }
    };
    this.Refract = function Refract(v1) {
      return new Refract.class(v1);
    };
    this.Refract.class = class Refract extends sphere.Surfspec {
      constructor(v) {
        super();
        this.v = v;
      }
      toString() { return "Refract(" + globalThis.Predef.render(this.v) + ")"; }
    };
    this.Body = function Body(v1) {
      return new Body.class(v1);
    };
    this.Body.class = class Body extends sphere.Surfspec {
      constructor(v) {
        super();
        this.v = v;
      }
      toString() { return "Body(" + globalThis.Predef.render(this.v) + ")"; }
    };
    this.Sphere = function Sphere(pos1, radius1, surface1) {
      return new Sphere.class(pos1, radius1, surface1);
    };
    this.Sphere.class = class Sphere {
      constructor(pos, radius, surface) {
        this.pos = pos;
        this.radius = radius;
        this.surface = surface;
      }
      toString() { return "Sphere(" + globalThis.Predef.render(this.pos) + ", " + globalThis.Predef.render(this.radius) + ", " + globalThis.Predef.render(this.surface) + ")"; }
    };
    sphere.#lookat = [
      0.0,
      0.0,
      0.0
    ];
    sphere.#vup = [
      0.0,
      0.0,
      1.0
    ];
    sphere.#fov = 45.0;
    tmp = sphere.Ambient([
      0.035,
      0.0325,
      0.025
    ]);
    tmp1 = sphere.Diffuse([
      0.5,
      0.45,
      0.35
    ]);
    tmp2 = sphere.Specular([
      0.8,
      0.8,
      0.8
    ]);
    tmp3 = sphere.Specpow(3.0);
    tmp4 = sphere.Reflect(0.5);
    tmp5 = NofibPrelude.Cons(tmp4, NofibPrelude.Nil);
    tmp6 = NofibPrelude.Cons(tmp3, tmp5);
    tmp7 = NofibPrelude.Cons(tmp2, tmp6);
    tmp8 = NofibPrelude.Cons(tmp1, tmp7);
    tmp9 = NofibPrelude.Cons(tmp, tmp8);
    sphere.#s2 = tmp9;
    tmp10 = sphere.Sphere([
      0.0,
      0.0,
      0.0
    ], 0.5, sphere.#s2);
    tmp11 = sphere.Sphere([
      0.272166,
      0.272166,
      0.544331
    ], 0.166667, sphere.#s2);
    tmp12 = sphere.Sphere([
      0.643951,
      0.172546,
      0.0
    ], 0.166667, sphere.#s2);
    tmp13 = sphere.Sphere([
      0.172546,
      0.643951,
      0.0
    ], 0.166667, sphere.#s2);
    tmp14 = - 0.371785;
    tmp15 = sphere.Sphere([
      tmp14,
      0.0996195,
      0.544331
    ], 0.166667, sphere.#s2);
    tmp16 = - 0.471405;
    tmp17 = sphere.Sphere([
      tmp16,
      0.471405,
      0.0
    ], 0.166667, sphere.#s2);
    tmp18 = - 0.643951;
    tmp19 = - 0.172546;
    tmp20 = sphere.Sphere([
      tmp18,
      tmp19,
      0.0
    ], 0.166667, sphere.#s2);
    tmp21 = - 0.371785;
    tmp22 = sphere.Sphere([
      0.0996195,
      tmp21,
      0.544331
    ], 0.166667, sphere.#s2);
    tmp23 = - 0.172546;
    tmp24 = - 0.643951;
    tmp25 = sphere.Sphere([
      tmp23,
      tmp24,
      0.0
    ], 0.166667, sphere.#s2);
    tmp26 = - 0.471405;
    tmp27 = sphere.Sphere([
      0.471405,
      tmp26,
      0.0
    ], 0.166667, sphere.#s2);
    tmp28 = NofibPrelude.Cons(tmp27, NofibPrelude.Nil);
    tmp29 = NofibPrelude.Cons(tmp25, tmp28);
    tmp30 = NofibPrelude.Cons(tmp22, tmp29);
    tmp31 = NofibPrelude.Cons(tmp20, tmp30);
    tmp32 = NofibPrelude.Cons(tmp17, tmp31);
    tmp33 = NofibPrelude.Cons(tmp15, tmp32);
    tmp34 = NofibPrelude.Cons(tmp13, tmp33);
    tmp35 = NofibPrelude.Cons(tmp12, tmp34);
    tmp36 = NofibPrelude.Cons(tmp11, tmp35);
    tmp37 = NofibPrelude.Cons(tmp10, tmp36);
    sphere.#testspheres = tmp37;
    tmp38 = sphere.Point([
      4.0,
      3.0,
      2.0
    ], [
      0.288675,
      0.288675,
      0.288675
    ]);
    tmp39 = - 4.0;
    tmp40 = sphere.Point([
      1.0,
      tmp39,
      4.0
    ], [
      0.288675,
      0.288675,
      0.288675
    ]);
    tmp41 = - 3.0;
    tmp42 = sphere.Point([
      tmp41,
      1.0,
      5.0
    ], [
      0.288675,
      0.288675,
      0.288675
    ]);
    tmp43 = NofibPrelude.Cons(tmp42, NofibPrelude.Nil);
    tmp44 = NofibPrelude.Cons(tmp40, tmp43);
    tmp45 = NofibPrelude.Cons(tmp38, tmp44);
    sphere.#testlights = tmp45;
    sphere.#lookfrom = [
      2.1,
      1.3,
      1.7
    ];
    sphere.#background = [
      0.078,
      0.361,
      0.753
    ];
    lambda = (undefined, function () {
      return sphere.testSphere_nofib(30)
    });
    BenchmarkPrelude.benchmark(lambda)
  }
  static vecadd(a1, a2) {
    let first2, first1, first0, x1, y1, z1, first21, first11, first01, x2, y2, z2, tmp, tmp1, tmp2;
    if (globalThis.Array.isArray(a1) && a1.length === 3) {
      first0 = a1[0];
      first1 = a1[1];
      first2 = a1[2];
      x1 = first0;
      y1 = first1;
      z1 = first2;
      if (globalThis.Array.isArray(a2) && a2.length === 3) {
        first01 = a2[0];
        first11 = a2[1];
        first21 = a2[2];
        x2 = first01;
        y2 = first11;
        z2 = first21;
        tmp = x1 + x2;
        tmp1 = y1 + y2;
        tmp2 = z1 + z2;
        return [
          tmp,
          tmp1,
          tmp2
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static vecsub(a11, a21) {
    let first2, first1, first0, x1, y1, z1, first21, first11, first01, x2, y2, z2, tmp, tmp1, tmp2;
    if (globalThis.Array.isArray(a11) && a11.length === 3) {
      first0 = a11[0];
      first1 = a11[1];
      first2 = a11[2];
      x1 = first0;
      y1 = first1;
      z1 = first2;
      if (globalThis.Array.isArray(a21) && a21.length === 3) {
        first01 = a21[0];
        first11 = a21[1];
        first21 = a21[2];
        x2 = first01;
        y2 = first11;
        z2 = first21;
        tmp = x1 - x2;
        tmp1 = y1 - y2;
        tmp2 = z1 - z2;
        return [
          tmp,
          tmp1,
          tmp2
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static vecmult(a12, a22) {
    let first2, first1, first0, x1, y1, z1, first21, first11, first01, x2, y2, z2, tmp, tmp1, tmp2;
    if (globalThis.Array.isArray(a12) && a12.length === 3) {
      first0 = a12[0];
      first1 = a12[1];
      first2 = a12[2];
      x1 = first0;
      y1 = first1;
      z1 = first2;
      if (globalThis.Array.isArray(a22) && a22.length === 3) {
        first01 = a22[0];
        first11 = a22[1];
        first21 = a22[2];
        x2 = first01;
        y2 = first11;
        z2 = first21;
        tmp = x1 * x2;
        tmp1 = y1 * y2;
        tmp2 = z1 * z2;
        return [
          tmp,
          tmp1,
          tmp2
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static vecsum(param) {
    return NofibPrelude.foldr(sphere.vecadd, [
      0.0,
      0.0,
      0.0
    ], param)
  } 
  static vecnorm(xyz) {
    let first2, first1, first0, x, y, z, len, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    if (globalThis.Array.isArray(xyz) && xyz.length === 3) {
      first0 = xyz[0];
      first1 = xyz[1];
      first2 = xyz[2];
      x = first0;
      y = first1;
      z = first2;
      tmp = x * x;
      tmp1 = y * y;
      tmp2 = tmp + tmp1;
      tmp3 = z * z;
      tmp4 = tmp2 + tmp3;
      tmp5 = NofibPrelude.sqrt(tmp4);
      len = tmp5;
      tmp6 = x / len;
      tmp7 = y / len;
      tmp8 = z / len;
      return [
        [
          tmp6,
          tmp7,
          tmp8
        ],
        len
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static vecscale(xyz1, a) {
    let first2, first1, first0, x, y, z, tmp, tmp1, tmp2;
    if (globalThis.Array.isArray(xyz1) && xyz1.length === 3) {
      first0 = xyz1[0];
      first1 = xyz1[1];
      first2 = xyz1[2];
      x = first0;
      y = first1;
      z = first2;
      tmp = a * x;
      tmp1 = a * y;
      tmp2 = a * z;
      return [
        tmp,
        tmp1,
        tmp2
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static vecdot(x1, x2) {
    let first2, first1, first0, x11, y1, z1, first21, first11, first01, x21, y2, z2, tmp, tmp1, tmp2, tmp3;
    if (globalThis.Array.isArray(x1) && x1.length === 3) {
      first0 = x1[0];
      first1 = x1[1];
      first2 = x1[2];
      x11 = first0;
      y1 = first1;
      z1 = first2;
      if (globalThis.Array.isArray(x2) && x2.length === 3) {
        first01 = x2[0];
        first11 = x2[1];
        first21 = x2[2];
        x21 = first01;
        y2 = first11;
        z2 = first21;
        tmp = x11 * x21;
        tmp1 = y1 * y2;
        tmp2 = tmp + tmp1;
        tmp3 = z1 * z2;
        return tmp2 + tmp3
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static veccross(x11, x21) {
    let first2, first1, first0, x12, y1, z1, first21, first11, first01, x22, y2, z2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    if (globalThis.Array.isArray(x11) && x11.length === 3) {
      first0 = x11[0];
      first1 = x11[1];
      first2 = x11[2];
      x12 = first0;
      y1 = first1;
      z1 = first2;
      if (globalThis.Array.isArray(x21) && x21.length === 3) {
        first01 = x21[0];
        first11 = x21[1];
        first21 = x21[2];
        x22 = first01;
        y2 = first11;
        z2 = first21;
        tmp = y1 * z2;
        tmp1 = y2 * z1;
        tmp2 = tmp - tmp1;
        tmp3 = z1 * x22;
        tmp4 = z2 * x12;
        tmp5 = tmp3 - tmp4;
        tmp6 = x12 * y2;
        tmp7 = x22 * y1;
        tmp8 = tmp6 - tmp7;
        return [
          tmp2,
          tmp5,
          tmp8
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static is_zerovector(x) {
    let first2, first1, first0, x3, y, z, tmp, tmp1, tmp2, tmp3;
    if (globalThis.Array.isArray(x) && x.length === 3) {
      first0 = x[0];
      first1 = x[1];
      first2 = x[2];
      x3 = first0;
      y = first1;
      z = first2;
      tmp = x3 < sphere.#epsilon;
      tmp1 = y < sphere.#epsilon;
      tmp2 = tmp && tmp1;
      tmp3 = z < sphere.#epsilon;
      return tmp2 && tmp3
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static lightpos(p) {
    let param0, param1, pos, col;
    if (p instanceof sphere.Point.class) {
      param0 = p.x;
      param1 = p.y;
      pos = param0;
      col = param1;
      return pos
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static lightdir(d) {
    let param0, param1, dir, col, tmp;
    if (d instanceof sphere.Directional.class) {
      param0 = d.x;
      param1 = d.y;
      dir = param0;
      col = param1;
      tmp = sphere.vecnorm(dir);
      return NofibPrelude.fst(tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static lightcolour(x3) {
    let param0, param1, pos, col, param01, param11, dir, col1;
    if (x3 instanceof sphere.Directional.class) {
      param01 = x3.x;
      param11 = x3.y;
      dir = param01;
      col1 = param11;
      return col1
    } else if (x3 instanceof sphere.Point.class) {
      param0 = x3.x;
      param1 = x3.y;
      pos = param0;
      col = param1;
      return col
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static ambientsurf(ss) {
    let lscomp, tmp, tmp1, tmp2;
    lscomp = function lscomp(ls) {
      let param0, param1, x4, t, param01, s, tmp3;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        x4 = param0;
        t = param1;
        if (x4 instanceof sphere.Ambient.class) {
          param01 = x4.v;
          s = param01;
          tmp3 = lscomp(t);
          return NofibPrelude.Cons(s, tmp3)
        } else {
          return lscomp(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = lscomp(ss);
    tmp1 = NofibPrelude.Cons([
      0.0,
      0.0,
      0.0
    ], NofibPrelude.Nil);
    tmp2 = NofibPrelude.append(tmp, tmp1);
    return NofibPrelude.head(tmp2)
  } 
  static diffusesurf(ss1) {
    let lscomp, tmp, tmp1, tmp2;
    lscomp = function lscomp(ls) {
      let param0, param1, x4, t, param01, s, tmp3;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        x4 = param0;
        t = param1;
        if (x4 instanceof sphere.Diffuse.class) {
          param01 = x4.v;
          s = param01;
          tmp3 = lscomp(t);
          return NofibPrelude.Cons(s, tmp3)
        } else {
          return lscomp(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = lscomp(ss1);
    tmp1 = NofibPrelude.Cons([
      0.0,
      0.0,
      0.0
    ], NofibPrelude.Nil);
    tmp2 = NofibPrelude.append(tmp, tmp1);
    return NofibPrelude.head(tmp2)
  } 
  static specularsurf(ss2) {
    let lscomp, tmp, tmp1, tmp2;
    lscomp = function lscomp(ls) {
      let param0, param1, x4, t, param01, s, tmp3;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        x4 = param0;
        t = param1;
        if (x4 instanceof sphere.Specular.class) {
          param01 = x4.v;
          s = param01;
          tmp3 = lscomp(t);
          return NofibPrelude.Cons(s, tmp3)
        } else {
          return lscomp(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = lscomp(ss2);
    tmp1 = NofibPrelude.Cons([
      0.0,
      0.0,
      0.0
    ], NofibPrelude.Nil);
    tmp2 = NofibPrelude.append(tmp, tmp1);
    return NofibPrelude.head(tmp2)
  } 
  static specpowsurf(ss3) {
    let lscomp, tmp, tmp1, tmp2;
    lscomp = function lscomp(ls) {
      let param0, param1, x4, t, param01, s, tmp3;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        x4 = param0;
        t = param1;
        if (x4 instanceof sphere.Specpow.class) {
          param01 = x4.v;
          s = param01;
          tmp3 = lscomp(t);
          return NofibPrelude.Cons(s, tmp3)
        } else {
          return lscomp(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = lscomp(ss3);
    tmp1 = NofibPrelude.Cons(8.0, NofibPrelude.Nil);
    tmp2 = NofibPrelude.append(tmp, tmp1);
    return NofibPrelude.head(tmp2)
  } 
  static reflectsurf(ss4) {
    let lscomp, tmp, tmp1, tmp2;
    lscomp = function lscomp(ls) {
      let param0, param1, x4, t, param01, s, tmp3;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        x4 = param0;
        t = param1;
        if (x4 instanceof sphere.Reflect.class) {
          param01 = x4.v;
          s = param01;
          tmp3 = lscomp(t);
          return NofibPrelude.Cons(s, tmp3)
        } else {
          return lscomp(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = lscomp(ss4);
    tmp1 = NofibPrelude.Cons(0.0, NofibPrelude.Nil);
    tmp2 = NofibPrelude.append(tmp, tmp1);
    return NofibPrelude.head(tmp2)
  } 
  static transmitsurf(ss5) {
    let lscomp, tmp, tmp1, tmp2;
    lscomp = function lscomp(ls) {
      let param0, param1, x4, t, param01, s, tmp3;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        x4 = param0;
        t = param1;
        if (x4 instanceof sphere.Transmit.class) {
          param01 = x4.v;
          s = param01;
          tmp3 = lscomp(t);
          return NofibPrelude.Cons(s, tmp3)
        } else {
          return lscomp(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = lscomp(ss5);
    tmp1 = NofibPrelude.Cons(0.0, NofibPrelude.Nil);
    tmp2 = NofibPrelude.append(tmp, tmp1);
    return NofibPrelude.head(tmp2)
  } 
  static refractsurf(ss6) {
    let lscomp, tmp, tmp1, tmp2;
    lscomp = function lscomp(ls) {
      let param0, param1, x4, t, param01, s, tmp3;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        x4 = param0;
        t = param1;
        if (x4 instanceof sphere.Refract.class) {
          param01 = x4.v;
          s = param01;
          tmp3 = lscomp(t);
          return NofibPrelude.Cons(s, tmp3)
        } else {
          return lscomp(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = lscomp(ss6);
    tmp1 = NofibPrelude.Cons(1.0, NofibPrelude.Nil);
    tmp2 = NofibPrelude.append(tmp, tmp1);
    return NofibPrelude.head(tmp2)
  } 
  static bodysurf(ss7) {
    let lscomp, tmp, tmp1, tmp2;
    lscomp = function lscomp(ls) {
      let param0, param1, x4, t, param01, s, tmp3;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        x4 = param0;
        t = param1;
        if (x4 instanceof sphere.Body.class) {
          param01 = x4.v;
          s = param01;
          tmp3 = lscomp(t);
          return NofibPrelude.Cons(s, tmp3)
        } else {
          return lscomp(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = lscomp(ss7);
    tmp1 = NofibPrelude.Cons([
      1.0,
      1.0,
      1.0
    ], NofibPrelude.Nil);
    tmp2 = NofibPrelude.append(tmp, tmp1);
    return NofibPrelude.head(tmp2)
  } 
  static spheresurf(s) {
    let param0, param1, param2, pos, rad, surf;
    if (s instanceof sphere.Sphere.class) {
      param0 = s.pos;
      param1 = s.radius;
      param2 = s.surface;
      pos = param0;
      rad = param1;
      surf = param2;
      return surf
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static spherenormal(pos, sp) {
    let param0, param1, param2, spos, rad, tmp, tmp1;
    if (sp instanceof sphere.Sphere.class) {
      param0 = sp.pos;
      param1 = sp.radius;
      param2 = sp.surface;
      spos = param0;
      rad = param1;
      tmp = sphere.vecsub(pos, spos);
      tmp1 = 1 / rad;
      return sphere.vecscale(tmp, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static dtor(x4) {
    let tmp;
    tmp = x4 * sphere.#pi;
    return tmp / 180.0
  } 
  static camparams(lookfrom, lookat, vup, fov, winsize) {
    let initfirstray, scrut, first1, first0, lookdir, dist, scrut1, first11, first01, scrni, scrut2, first12, first02, scrnj, xfov, yfov, xwinsize, ywinsize, magx, magy, scrnx, scrny, firstray, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22;
    tmp = sphere.vecsub(lookat, lookfrom);
    initfirstray = tmp;
    scrut = sphere.vecnorm(initfirstray);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      lookdir = first0;
      dist = first1;
      tmp1 = sphere.veccross(lookdir, vup);
      scrut1 = sphere.vecnorm(tmp1);
      if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
        first01 = scrut1[0];
        first11 = scrut1[1];
        scrni = first01;
        tmp2 = sphere.veccross(scrni, lookdir);
        scrut2 = sphere.vecnorm(tmp2);
        if (globalThis.Array.isArray(scrut2) && scrut2.length === 2) {
          first02 = scrut2[0];
          first12 = scrut2[1];
          scrnj = first02;
          xfov = fov;
          yfov = fov;
          xwinsize = winsize;
          ywinsize = winsize;
          tmp3 = 2.0 * dist;
          tmp4 = xfov / 2;
          tmp5 = sphere.dtor(tmp4);
          tmp6 = NofibPrelude.tan(tmp5);
          tmp7 = tmp3 * tmp6;
          tmp8 = tmp7 / xwinsize;
          magx = tmp8;
          tmp9 = 2.0 * dist;
          tmp10 = yfov / 2;
          tmp11 = sphere.dtor(tmp10);
          tmp12 = NofibPrelude.tan(tmp11);
          tmp13 = tmp9 * tmp12;
          tmp14 = tmp13 / ywinsize;
          magy = tmp14;
          tmp15 = sphere.vecscale(scrni, magx);
          scrnx = tmp15;
          tmp16 = sphere.vecscale(scrnj, magy);
          scrny = tmp16;
          tmp17 = 0.5 * xwinsize;
          tmp18 = sphere.vecscale(scrnx, tmp17);
          tmp19 = 0.5 * ywinsize;
          tmp20 = sphere.vecscale(scrny, tmp19);
          tmp21 = sphere.vecadd(tmp18, tmp20);
          tmp22 = sphere.vecsub(initfirstray, tmp21);
          firstray = tmp22;
          return [
            firstray,
            scrnx,
            scrny
          ]
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
  static sphereintersect(pos1, dir, sp1) {
    let param0, param1, param2, spos, rad, m, bm, m2, disc, slo, shi, scrut, scrut1, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12;
    if (sp1 instanceof sphere.Sphere.class) {
      param0 = sp1.pos;
      param1 = sp1.radius;
      param2 = sp1.surface;
      spos = param0;
      rad = param1;
      tmp = sphere.vecsub(pos1, spos);
      m = tmp;
      tmp1 = sphere.vecdot(m, dir);
      bm = tmp1;
      tmp2 = sphere.vecdot(m, m);
      m2 = tmp2;
      tmp3 = bm * bm;
      tmp4 = tmp3 - m2;
      tmp5 = rad * rad;
      tmp6 = tmp4 + tmp5;
      disc = tmp6;
      tmp7 = - bm;
      tmp8 = NofibPrelude.sqrt(disc);
      tmp9 = tmp7 - tmp8;
      slo = tmp9;
      tmp10 = - bm;
      tmp11 = NofibPrelude.sqrt(disc);
      tmp12 = tmp10 + tmp11;
      shi = tmp12;
      scrut2 = disc < 0.0;
      if (scrut2 === true) {
        return [
          false,
          0.0
        ]
      } else {
        scrut = slo < 0.0;
        if (scrut === true) {
          scrut1 = shi < 0.0;
          if (scrut1 === true) {
            return [
              false,
              0.0
            ]
          } else {
            return [
              true,
              shi
            ]
          }
        } else {
          return [
            true,
            slo
          ]
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static trace(spheres, pos2, dir1) {
    let f, sphmap, dists, scrut, first1, first0, mindist, sp2, scrut1, tmp, tmp1, tmp2, tmp3;
    f = function f(d1s1, d2s2) {
      let first11, first01, d1, s1, first12, first02, d2, s2_, scrut2;
      if (globalThis.Array.isArray(d1s1) && d1s1.length === 2) {
        first01 = d1s1[0];
        first11 = d1s1[1];
        d1 = first01;
        s1 = first11;
        if (globalThis.Array.isArray(d2s2) && d2s2.length === 2) {
          first02 = d2s2[0];
          first12 = d2s2[1];
          d2 = first02;
          s2_ = first12;
          scrut2 = d1 < d2;
          if (scrut2 === true) {
            return [
              d1,
              s1
            ]
          } else {
            return [
              d2,
              s2_
            ]
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    sphmap = function sphmap(xss) {
      let param0, param1, x5, xs, scrut2, first11, first01, is_hit, where_hit, tmp4;
      if (xss instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (xss instanceof NofibPrelude.Cons.class) {
        param0 = xss.head;
        param1 = xss.tail;
        x5 = param0;
        xs = param1;
        scrut2 = sphere.sphereintersect(pos2, dir1, x5);
        if (globalThis.Array.isArray(scrut2) && scrut2.length === 2) {
          first01 = scrut2[0];
          first11 = scrut2[1];
          is_hit = first01;
          where_hit = first11;
          if (is_hit === true) {
            tmp4 = sphmap(xs);
            return NofibPrelude.Cons([
              where_hit,
              x5
            ], tmp4)
          } else {
            return sphmap(xs)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = sphmap(spheres);
    dists = tmp;
    scrut1 = NofibPrelude.null_(dists);
    if (scrut1 === true) {
      tmp1 = NofibPrelude.head(spheres);
      return [
        false,
        sphere.#infinity,
        tmp1
      ]
    } else {
      tmp2 = NofibPrelude.head(dists);
      tmp3 = NofibPrelude.tail(dists);
      scrut = NofibPrelude.foldr(f, tmp2, tmp3);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        mindist = first0;
        sp2 = first1;
        return [
          true,
          mindist,
          sp2
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  static refractray(newindex, olddir, innorm) {
    let dotp, matchIdent_17, scrut, first2, first1, first0, norm, k, nr, disc, t, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17;
    tmp = sphere.vecdot(olddir, innorm);
    tmp1 = - tmp;
    dotp = tmp1;
    scrut = dotp < 0.0;
    if (scrut === true) {
      tmp2 = - 1.0;
      tmp3 = sphere.vecscale(innorm, tmp2);
      tmp4 = - dotp;
      tmp5 = 1.0 / newindex;
      tmp6 = [
        tmp3,
        tmp4,
        tmp5
      ];
    } else {
      tmp6 = [
        innorm,
        dotp,
        newindex
      ];
    }
    matchIdent_17 = tmp6;
    if (globalThis.Array.isArray(matchIdent_17) && matchIdent_17.length === 3) {
      first0 = matchIdent_17[0];
      first1 = matchIdent_17[1];
      first2 = matchIdent_17[2];
      norm = first0;
      k = first1;
      nr = first2;
      tmp7 = nr * nr;
      tmp8 = k * k;
      tmp9 = 1.0 - tmp8;
      tmp10 = tmp7 * tmp9;
      tmp11 = 1.0 - tmp10;
      disc = tmp11;
      tmp12 = nr * k;
      tmp13 = NofibPrelude.sqrt(disc);
      tmp14 = tmp12 - tmp13;
      t = tmp14;
      scrut1 = disc < 0.0;
      if (scrut1 === true) {
        return [
          true,
          [
            0.0,
            0.0,
            0.0
          ]
        ]
      } else {
        tmp15 = sphere.vecscale(norm, t);
        tmp16 = sphere.vecscale(olddir, nr);
        tmp17 = sphere.vecadd(tmp15, tmp16);
        return [
          false,
          tmp17
        ]
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static lightdirection(l, pt) {
    let param0, param1, pos3, col, param01, param11, dir2, col1, tmp, tmp1, tmp2;
    if (l instanceof sphere.Directional.class) {
      param01 = l.x;
      param11 = l.y;
      dir2 = param01;
      col1 = param11;
      tmp = sphere.vecnorm(dir2);
      tmp1 = NofibPrelude.fst(tmp);
      return [
        tmp1,
        sphere.#infinity
      ]
    } else if (l instanceof sphere.Point.class) {
      param0 = l.x;
      param1 = l.y;
      pos3 = param0;
      col = param1;
      tmp2 = sphere.vecsub(pos3, pt);
      return sphere.vecnorm(tmp2)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static shadowed(pos3, dir2, lcolour) {
    let scrut, first2, first1, first0, is_hit, dist, sp2, scrut1, tmp, tmp1;
    tmp = sphere.vecscale(dir2, sphere.#epsilon);
    tmp1 = sphere.vecadd(pos3, tmp);
    scrut = sphere.trace(sphere.#testspheres, tmp1, dir2);
    if (globalThis.Array.isArray(scrut) && scrut.length === 3) {
      first0 = scrut[0];
      first1 = scrut[1];
      first2 = scrut[2];
      is_hit = first0;
      dist = first1;
      sp2 = first2;
      scrut1 = BenchmarkPrelude.not(is_hit);
      if (scrut1 === true) {
        return [
          false,
          lcolour
        ]
      } else {
        return [
          true,
          lcolour
        ]
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static lightray(l1, pos4, norm, refl, surf) {
    let scrut, first1, first0, ldir, dist, cosangle, scrut1, first11, first01, is_inshadow, lcolour1, diff, spow, spec, cosalpha, diffcont, speccont, scrut2, scrut3, bodycol, cosalpha1, diffcont1, speccont1, scrut4, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
    scrut = sphere.lightdirection(l1, pos4);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      ldir = first0;
      dist = first1;
      tmp = sphere.vecdot(ldir, norm);
      cosangle = tmp;
      tmp1 = sphere.lightcolour(l1);
      scrut1 = sphere.shadowed(pos4, ldir, tmp1);
      if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
        first01 = scrut1[0];
        first11 = scrut1[1];
        is_inshadow = first01;
        lcolour1 = first11;
        if (is_inshadow === true) {
          return [
            0.0,
            0.0,
            0.0
          ]
        } else {
          diff = sphere.diffusesurf(surf);
          spow = sphere.specpowsurf(surf);
          scrut3 = cosangle <= 0.0;
          if (scrut3 === true) {
            tmp2 = sphere.bodysurf(surf);
            bodycol = tmp2;
            tmp3 = sphere.vecdot(refl, ldir);
            tmp4 = - tmp3;
            cosalpha1 = tmp4;
            tmp5 = - cosangle;
            tmp6 = sphere.vecscale(diff, tmp5);
            tmp7 = sphere.vecmult(tmp6, lcolour1);
            diffcont1 = tmp7;
            scrut4 = cosalpha1 <= 0.0;
            if (scrut4 === true) {
              tmp8 = [
                0.0,
                0.0,
                0.0
              ];
            } else {
              tmp9 = NofibPrelude.power(cosalpha1, spow);
              tmp10 = sphere.vecscale(bodycol, tmp9);
              tmp8 = sphere.vecmult(tmp10, lcolour1);
            }
            speccont1 = tmp8;
            return sphere.vecadd(diffcont1, speccont1)
          } else {
            spec = sphere.specularsurf(surf);
            cosalpha = sphere.vecdot(refl, ldir);
            tmp11 = sphere.vecscale(diff, cosangle);
            diffcont = sphere.vecmult(tmp11, lcolour1);
            scrut2 = cosalpha < 0.0;
            if (scrut2 === true) {
              tmp12 = [
                0.0,
                0.0,
                0.0
              ];
            } else {
              tmp13 = NofibPrelude.power(cosalpha, spow);
              tmp14 = sphere.vecscale(spec, tmp13);
              tmp12 = sphere.vecmult(tmp14, lcolour1);
            }
            speccont = tmp12;
            return sphere.vecadd(diffcont, speccont)
          }
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static shade(lights, sp2, lookpos, dir3, dist, contrib) {
    let hitpos, ambientlight, surf1, amb, norm1, refl1, diff, transmitted, simple, trintensity, matchIdent_1, scrut, first1, first0, is_tir, trcol, reflsurf, reflectiv, rcol, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, lambda;
    tmp = sphere.vecscale(dir3, dist);
    tmp1 = sphere.vecadd(lookpos, tmp);
    hitpos = tmp1;
    ambientlight = [
      1.0,
      1.0,
      1.0
    ];
    tmp2 = sphere.spheresurf(sp2);
    surf1 = tmp2;
    tmp3 = sphere.ambientsurf(surf1);
    tmp4 = sphere.vecmult(ambientlight, tmp3);
    amb = tmp4;
    tmp5 = sphere.spherenormal(hitpos, sp2);
    norm1 = tmp5;
    tmp6 = - 2.0;
    tmp7 = sphere.vecdot(dir3, norm1);
    tmp8 = tmp6 * tmp7;
    tmp9 = sphere.vecscale(norm1, tmp8);
    tmp10 = sphere.vecadd(dir3, tmp9);
    refl1 = tmp10;
    lambda = (undefined, function (l2) {
      return sphere.lightray(l2, hitpos, norm1, refl1, surf1)
    });
    tmp11 = NofibPrelude.map(lambda, lights);
    tmp12 = sphere.vecsum(tmp11);
    diff = tmp12;
    tmp13 = sphere.transmitsurf(surf1);
    transmitted = tmp13;
    tmp14 = sphere.vecadd(amb, diff);
    simple = tmp14;
    tmp15 = sphere.bodysurf(surf1);
    tmp16 = sphere.vecscale(tmp15, transmitted);
    trintensity = tmp16;
    scrut = transmitted < sphere.#epsilon;
    if (scrut === true) {
      tmp17 = [
        false,
        simple
      ];
    } else {
      tmp18 = sphere.refractsurf(surf1);
      tmp17 = sphere.transmitray(lights, simple, hitpos, dir3, tmp18, trintensity, contrib, norm1);
    }
    matchIdent_1 = tmp17;
    if (globalThis.Array.isArray(matchIdent_1) && matchIdent_1.length === 2) {
      first0 = matchIdent_1[0];
      first1 = matchIdent_1[1];
      is_tir = first0;
      trcol = first1;
      tmp19 = sphere.specularsurf(surf1);
      tmp20 = sphere.reflectsurf(surf1);
      tmp21 = sphere.vecscale(tmp19, tmp20);
      reflsurf = tmp21;
      if (is_tir === true) {
        tmp22 = sphere.vecadd(trintensity, reflsurf);
      } else {
        tmp22 = reflsurf;
      }
      reflectiv = tmp22;
      scrut1 = sphere.is_zerovector(reflectiv);
      if (scrut1 === true) {
        tmp23 = trcol;
      } else {
        tmp23 = sphere.reflectray(hitpos, refl1, lights, reflectiv, contrib, trcol);
      }
      rcol = tmp23;
      return rcol
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static transmitray(lights1, colour, pos5, dir4, index, intens, contrib1, norm1) {
    let newcontrib, scrut, first1, first0, is_tir, newdir, nearpos, scrut1, first2, first11, first01, is_hit, dist1, sp3, newcol, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = sphere.vecmult(intens, contrib1);
    newcontrib = tmp;
    scrut = sphere.refractray(index, dir4, norm1);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      is_tir = first0;
      newdir = first1;
      tmp1 = sphere.vecscale(newdir, sphere.#epsilon);
      tmp2 = sphere.vecadd(pos5, tmp1);
      nearpos = tmp2;
      scrut1 = sphere.trace(sphere.#testspheres, nearpos, newdir);
      if (globalThis.Array.isArray(scrut1) && scrut1.length === 3) {
        first01 = scrut1[0];
        first11 = scrut1[1];
        first2 = scrut1[2];
        is_hit = first01;
        dist1 = first11;
        sp3 = first2;
        if (is_hit === true) {
          tmp3 = sphere.shade(lights1, sp3, nearpos, newdir, dist1, newcontrib);
        } else {
          tmp3 = sphere.#background;
        }
        newcol = tmp3;
        scrut2 = sphere.is_zerovector(newcontrib);
        if (scrut2 === true) {
          return [
            false,
            colour
          ]
        } else {
          tmp4 = sphere.vecmult(newcol, intens);
          tmp5 = sphere.vecadd(tmp4, colour);
          return [
            false,
            tmp5
          ]
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static reflectray(pos6, newdir, lights2, intens1, contrib2, colour1) {
    let newcontrib, nearpos, scrut, first2, first1, first0, is_hit, dist1, sp3, newcol, scrut1, tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = sphere.vecmult(intens1, contrib2);
    newcontrib = tmp;
    tmp1 = sphere.vecscale(newdir, sphere.#epsilon);
    tmp2 = sphere.vecadd(pos6, tmp1);
    nearpos = tmp2;
    scrut = sphere.trace(sphere.#testspheres, nearpos, newdir);
    if (globalThis.Array.isArray(scrut) && scrut.length === 3) {
      first0 = scrut[0];
      first1 = scrut[1];
      first2 = scrut[2];
      is_hit = first0;
      dist1 = first1;
      sp3 = first2;
      if (is_hit === true) {
        tmp3 = sphere.shade(lights2, sp3, nearpos, newdir, dist1, newcontrib);
      } else {
        tmp3 = sphere.#background;
      }
      newcol = tmp3;
      scrut1 = sphere.is_zerovector(newcontrib);
      if (scrut1 === true) {
        return colour1
      } else {
        tmp4 = sphere.vecmult(newcol, intens1);
        return sphere.vecadd(colour1, tmp4)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static tracepixel(spheres1, lights3, x5, y, firstray, scrnx, scrny) {
    let pos7, scrut, first1, first0, dir5, tracepixel_Tup2_1, scrut1, first2, first11, first01, hit, dist1, sp3, tmp, tmp1, tmp2, tmp3;
    pos7 = sphere.#lookfrom;
    tmp = sphere.vecscale(scrnx, x5);
    tmp1 = sphere.vecadd(firstray, tmp);
    tmp2 = sphere.vecscale(scrny, y);
    tmp3 = sphere.vecadd(tmp1, tmp2);
    scrut = sphere.vecnorm(tmp3);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      dir5 = first0;
      tracepixel_Tup2_1 = first1;
      scrut1 = sphere.trace(spheres1, pos7, dir5);
      if (globalThis.Array.isArray(scrut1) && scrut1.length === 3) {
        first01 = scrut1[0];
        first11 = scrut1[1];
        first2 = scrut1[2];
        hit = first01;
        dist1 = first11;
        sp3 = first2;
        if (hit === true) {
          return sphere.shade(lights3, sp3, pos7, dir5, dist1, [
            1.0,
            1.0,
            1.0
          ])
        } else {
          return sphere.#background
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static z_of_int(x6) {
    return runtime.safeCall(globalThis.BigInt(x6))
  } 
  static hash(param1) {
    let u8, tmp, tmp1, lambda;
    u8 = function u8(x7) {
      let tmp2, tmp3;
      tmp2 = 255 * x7;
      tmp3 = NofibPrelude.round(tmp2);
      return sphere.z_of_int(tmp3)
    };
    lambda = (undefined, function (rgb, acc) {
      let first2, first1, first0, r, g, b, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12;
      if (globalThis.Array.isArray(rgb) && rgb.length === 3) {
        first0 = rgb[0];
        first1 = rgb[1];
        first2 = rgb[2];
        r = first0;
        g = first1;
        b = first2;
        tmp2 = u8(r);
        tmp3 = u8(g);
        tmp4 = sphere.z_of_int(7);
        tmp5 = tmp3 * tmp4;
        tmp6 = tmp2 + tmp5;
        tmp7 = u8(b);
        tmp8 = sphere.z_of_int(23);
        tmp9 = tmp7 * tmp8;
        tmp10 = tmp6 + tmp9;
        tmp11 = sphere.z_of_int(61);
        tmp12 = acc * tmp11;
        return tmp10 + tmp12
      } else {
        throw new globalThis.Error("match error");
      }
    });
    tmp = lambda;
    tmp1 = sphere.z_of_int(0);
    return NofibPrelude.foldr(tmp, tmp1, param1)
  } 
  static ray(winsize1) {
    let f, lscomp1, lights4, scrut, first2, first1, first0, firstray1, scrnx1, scrny1, tmp, tmp1;
    lights4 = sphere.#testlights;
    scrut = sphere.camparams(sphere.#lookfrom, sphere.#lookat, sphere.#vup, sphere.#fov, winsize1);
    if (globalThis.Array.isArray(scrut) && scrut.length === 3) {
      first0 = scrut[0];
      first1 = scrut[1];
      first2 = scrut[2];
      firstray1 = first0;
      scrnx1 = first1;
      scrny1 = first2;
      f = function f(i, j) {
        return sphere.tracepixel(sphere.#testspheres, lights4, i, j, firstray1, scrnx1, scrny1)
      };
      lscomp1 = function lscomp1(ls1) {
        let lscomp2, param0, param11, i, t1, tmp2, tmp3;
        if (ls1 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (ls1 instanceof NofibPrelude.Cons.class) {
          param0 = ls1.head;
          param11 = ls1.tail;
          i = param0;
          t1 = param11;
          lscomp2 = function lscomp2(ls2) {
            let param01, param12, j, t2, tmp4, tmp5;
            if (ls2 instanceof NofibPrelude.Nil.class) {
              return lscomp1(t1)
            } else if (ls2 instanceof NofibPrelude.Cons.class) {
              param01 = ls2.head;
              param12 = ls2.tail;
              j = param01;
              t2 = param12;
              tmp4 = f(i, j);
              tmp5 = lscomp2(t2);
              return NofibPrelude.Cons([
                [
                  i,
                  j
                ],
                tmp4
              ], tmp5)
            } else {
              throw new globalThis.Error("match error");
            }
          };
          tmp2 = winsize1 - 1;
          tmp3 = NofibPrelude.enumFromTo(0, tmp2);
          return lscomp2(tmp3)
        } else {
          throw new globalThis.Error("match error");
        }
      };
      tmp = winsize1 - 1;
      tmp1 = NofibPrelude.enumFromTo(0, tmp);
      return lscomp1(tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static run(winsize2) {
    let tmp, tmp1;
    tmp = sphere.ray(winsize2);
    tmp1 = NofibPrelude.map(NofibPrelude.snd, tmp);
    return sphere.hash(tmp1)
  } 
  static testSphere_nofib(n) {
    return sphere.run(n)
  }
  static toString() { return "sphere"; }
};
let sphere = sphere1; export default sphere;
