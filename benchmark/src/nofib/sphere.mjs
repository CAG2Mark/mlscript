import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let reflectray, Specpow1, reflectsurf, sphereintersect, lightcolour, spheresurf, hash, bodysurf, ambientsurf, tracepixel, refractsurf, trace, specpowsurf, vecsub, spherenormal, vecscale, run, Point1, Diffuse1, Ambient1, shade, vecdot, lightpos, vecsum, veccross, vecnorm, lightdir, Reflect1, transmitray, testSphere_nofib, camparams, lightdirection, Sphere1, ray, specularsurf, Body1, transmitsurf, vecadd, Specular1, Surfspec1, z_of_int, vecmult, shadowed, dtor, Light1, lightray, refractray, Transmit1, Refract1, Directional1, is_zerovector, diffusesurf, pi, epsilon, infinity, lookat, vup, fov, s2, testspheres, testlights, lookfrom, background, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, lambda, lambda1;
vecadd = function vecadd(a1, a2) {
  let first2, first1, first0, x1, y1, z1, first21, first11, first01, x2, y2, z2, tmp47, tmp48, tmp49;
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
      tmp47 = x1 + x2;
      tmp48 = y1 + y2;
      tmp49 = z1 + z2;
      return [
        tmp47,
        tmp48,
        tmp49
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
vecsub = function vecsub(a1, a2) {
  let first2, first1, first0, x1, y1, z1, first21, first11, first01, x2, y2, z2, tmp47, tmp48, tmp49;
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
      tmp47 = x1 - x2;
      tmp48 = y1 - y2;
      tmp49 = z1 - z2;
      return [
        tmp47,
        tmp48,
        tmp49
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
vecmult = function vecmult(a1, a2) {
  let first2, first1, first0, x1, y1, z1, first21, first11, first01, x2, y2, z2, tmp47, tmp48, tmp49;
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
      tmp47 = x1 * x2;
      tmp48 = y1 * y2;
      tmp49 = z1 * z2;
      return [
        tmp47,
        tmp48,
        tmp49
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
vecsum = function vecsum(param) {
  return NofibPrelude.foldr(vecadd, [
    0.0,
    0.0,
    0.0
  ], param)
};
vecnorm = function vecnorm(xyz) {
  let first2, first1, first0, x, y, z, len, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55;
  if (globalThis.Array.isArray(xyz) && xyz.length === 3) {
    first0 = xyz[0];
    first1 = xyz[1];
    first2 = xyz[2];
    x = first0;
    y = first1;
    z = first2;
    tmp47 = x * x;
    tmp48 = y * y;
    tmp49 = tmp47 + tmp48;
    tmp50 = z * z;
    tmp51 = tmp49 + tmp50;
    tmp52 = NofibPrelude.sqrt(tmp51);
    len = tmp52;
    tmp53 = x / len;
    tmp54 = y / len;
    tmp55 = z / len;
    return [
      [
        tmp53,
        tmp54,
        tmp55
      ],
      len
    ]
  } else {
    throw new globalThis.Error("match error");
  }
};
vecscale = function vecscale(xyz, a) {
  let first2, first1, first0, x, y, z, tmp47, tmp48, tmp49;
  if (globalThis.Array.isArray(xyz) && xyz.length === 3) {
    first0 = xyz[0];
    first1 = xyz[1];
    first2 = xyz[2];
    x = first0;
    y = first1;
    z = first2;
    tmp47 = a * x;
    tmp48 = a * y;
    tmp49 = a * z;
    return [
      tmp47,
      tmp48,
      tmp49
    ]
  } else {
    throw new globalThis.Error("match error");
  }
};
vecdot = function vecdot(x1, x2) {
  let first2, first1, first0, x11, y1, z1, first21, first11, first01, x21, y2, z2, tmp47, tmp48, tmp49, tmp50;
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
      tmp47 = x11 * x21;
      tmp48 = y1 * y2;
      tmp49 = tmp47 + tmp48;
      tmp50 = z1 * z2;
      return tmp49 + tmp50
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
veccross = function veccross(x1, x2) {
  let first2, first1, first0, x11, y1, z1, first21, first11, first01, x21, y2, z2, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55;
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
      tmp47 = y1 * z2;
      tmp48 = y2 * z1;
      tmp49 = tmp47 - tmp48;
      tmp50 = z1 * x21;
      tmp51 = z2 * x11;
      tmp52 = tmp50 - tmp51;
      tmp53 = x11 * y2;
      tmp54 = x21 * y1;
      tmp55 = tmp53 - tmp54;
      return [
        tmp49,
        tmp52,
        tmp55
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
is_zerovector = function is_zerovector(x) {
  let first2, first1, first0, x1, y, z, tmp47, tmp48, tmp49, tmp50;
  if (globalThis.Array.isArray(x) && x.length === 3) {
    first0 = x[0];
    first1 = x[1];
    first2 = x[2];
    x1 = first0;
    y = first1;
    z = first2;
    tmp47 = x1 < epsilon;
    tmp48 = y < epsilon;
    tmp49 = tmp47 && tmp48;
    tmp50 = z < epsilon;
    return tmp49 && tmp50
  } else {
    throw new globalThis.Error("match error");
  }
};
lightpos = function lightpos(p) {
  let param0, param1, pos, col;
  if (p instanceof Point1.class) {
    param0 = p.x;
    param1 = p.y;
    pos = param0;
    col = param1;
    return pos
  } else {
    throw new globalThis.Error("match error");
  }
};
lightdir = function lightdir(d) {
  let param0, param1, dir, col, tmp47;
  if (d instanceof Directional1.class) {
    param0 = d.x;
    param1 = d.y;
    dir = param0;
    col = param1;
    tmp47 = vecnorm(dir);
    return NofibPrelude.fst(tmp47)
  } else {
    throw new globalThis.Error("match error");
  }
};
lightcolour = function lightcolour(x) {
  let param0, param1, pos, col, param01, param11, dir, col1;
  if (x instanceof Directional1.class) {
    param01 = x.x;
    param11 = x.y;
    dir = param01;
    col1 = param11;
    return col1
  } else if (x instanceof Point1.class) {
    param0 = x.x;
    param1 = x.y;
    pos = param0;
    col = param1;
    return col
  } else {
    throw new globalThis.Error("match error");
  }
};
ambientsurf = function ambientsurf(ss) {
  let lscomp, tmp47, tmp48, tmp49;
  lscomp = function lscomp(ls) {
    let param0, param1, x, t, param01, s, tmp50;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x = param0;
      t = param1;
      if (x instanceof Ambient1.class) {
        param01 = x.v;
        s = param01;
        tmp50 = lscomp(t);
        return NofibPrelude.Cons(s, tmp50)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp47 = lscomp(ss);
  tmp48 = NofibPrelude.Cons([
    0.0,
    0.0,
    0.0
  ], NofibPrelude.Nil);
  tmp49 = NofibPrelude.append(tmp47, tmp48);
  return NofibPrelude.head(tmp49)
};
diffusesurf = function diffusesurf(ss) {
  let lscomp, tmp47, tmp48, tmp49;
  lscomp = function lscomp(ls) {
    let param0, param1, x, t, param01, s, tmp50;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x = param0;
      t = param1;
      if (x instanceof Diffuse1.class) {
        param01 = x.v;
        s = param01;
        tmp50 = lscomp(t);
        return NofibPrelude.Cons(s, tmp50)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp47 = lscomp(ss);
  tmp48 = NofibPrelude.Cons([
    0.0,
    0.0,
    0.0
  ], NofibPrelude.Nil);
  tmp49 = NofibPrelude.append(tmp47, tmp48);
  return NofibPrelude.head(tmp49)
};
specularsurf = function specularsurf(ss) {
  let lscomp, tmp47, tmp48, tmp49;
  lscomp = function lscomp(ls) {
    let param0, param1, x, t, param01, s, tmp50;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x = param0;
      t = param1;
      if (x instanceof Specular1.class) {
        param01 = x.v;
        s = param01;
        tmp50 = lscomp(t);
        return NofibPrelude.Cons(s, tmp50)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp47 = lscomp(ss);
  tmp48 = NofibPrelude.Cons([
    0.0,
    0.0,
    0.0
  ], NofibPrelude.Nil);
  tmp49 = NofibPrelude.append(tmp47, tmp48);
  return NofibPrelude.head(tmp49)
};
specpowsurf = function specpowsurf(ss) {
  let lscomp, tmp47, tmp48, tmp49;
  lscomp = function lscomp(ls) {
    let param0, param1, x, t, param01, s, tmp50;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x = param0;
      t = param1;
      if (x instanceof Specpow1.class) {
        param01 = x.v;
        s = param01;
        tmp50 = lscomp(t);
        return NofibPrelude.Cons(s, tmp50)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp47 = lscomp(ss);
  tmp48 = NofibPrelude.Cons(8.0, NofibPrelude.Nil);
  tmp49 = NofibPrelude.append(tmp47, tmp48);
  return NofibPrelude.head(tmp49)
};
reflectsurf = function reflectsurf(ss) {
  let lscomp, tmp47, tmp48, tmp49;
  lscomp = function lscomp(ls) {
    let param0, param1, x, t, param01, s, tmp50;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x = param0;
      t = param1;
      if (x instanceof Reflect1.class) {
        param01 = x.v;
        s = param01;
        tmp50 = lscomp(t);
        return NofibPrelude.Cons(s, tmp50)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp47 = lscomp(ss);
  tmp48 = NofibPrelude.Cons(0.0, NofibPrelude.Nil);
  tmp49 = NofibPrelude.append(tmp47, tmp48);
  return NofibPrelude.head(tmp49)
};
transmitsurf = function transmitsurf(ss) {
  let lscomp, tmp47, tmp48, tmp49;
  lscomp = function lscomp(ls) {
    let param0, param1, x, t, param01, s, tmp50;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x = param0;
      t = param1;
      if (x instanceof Transmit1.class) {
        param01 = x.v;
        s = param01;
        tmp50 = lscomp(t);
        return NofibPrelude.Cons(s, tmp50)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp47 = lscomp(ss);
  tmp48 = NofibPrelude.Cons(0.0, NofibPrelude.Nil);
  tmp49 = NofibPrelude.append(tmp47, tmp48);
  return NofibPrelude.head(tmp49)
};
refractsurf = function refractsurf(ss) {
  let lscomp, tmp47, tmp48, tmp49;
  lscomp = function lscomp(ls) {
    let param0, param1, x, t, param01, s, tmp50;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x = param0;
      t = param1;
      if (x instanceof Refract1.class) {
        param01 = x.v;
        s = param01;
        tmp50 = lscomp(t);
        return NofibPrelude.Cons(s, tmp50)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp47 = lscomp(ss);
  tmp48 = NofibPrelude.Cons(1.0, NofibPrelude.Nil);
  tmp49 = NofibPrelude.append(tmp47, tmp48);
  return NofibPrelude.head(tmp49)
};
bodysurf = function bodysurf(ss) {
  let lscomp, tmp47, tmp48, tmp49;
  lscomp = function lscomp(ls) {
    let param0, param1, x, t, param01, s, tmp50;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x = param0;
      t = param1;
      if (x instanceof Body1.class) {
        param01 = x.v;
        s = param01;
        tmp50 = lscomp(t);
        return NofibPrelude.Cons(s, tmp50)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp47 = lscomp(ss);
  tmp48 = NofibPrelude.Cons([
    1.0,
    1.0,
    1.0
  ], NofibPrelude.Nil);
  tmp49 = NofibPrelude.append(tmp47, tmp48);
  return NofibPrelude.head(tmp49)
};
spheresurf = function spheresurf(s) {
  let param0, param1, param2, pos, rad, surf;
  if (s instanceof Sphere1.class) {
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
};
spherenormal = function spherenormal(pos, sp) {
  let param0, param1, param2, spos, rad, tmp47, tmp48;
  if (sp instanceof Sphere1.class) {
    param0 = sp.pos;
    param1 = sp.radius;
    param2 = sp.surface;
    spos = param0;
    rad = param1;
    tmp47 = vecsub(pos, spos);
    tmp48 = 1 / rad;
    return vecscale(tmp47, tmp48)
  } else {
    throw new globalThis.Error("match error");
  }
};
dtor = function dtor(x) {
  let tmp47;
  tmp47 = x * pi;
  return tmp47 / 180.0
};
camparams = function camparams(lookfrom1, lookat1, vup1, fov1, winsize) {
  let initfirstray, scrut, first1, first0, lookdir, dist, scrut1, first11, first01, scrni, scrut2, first12, first02, scrnj, xfov, yfov, xwinsize, ywinsize, magx, magy, scrnx, scrny, firstray, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69;
  tmp47 = vecsub(lookat1, lookfrom1);
  initfirstray = tmp47;
  scrut = vecnorm(initfirstray);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    lookdir = first0;
    dist = first1;
    tmp48 = veccross(lookdir, vup1);
    scrut1 = vecnorm(tmp48);
    if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
      first01 = scrut1[0];
      first11 = scrut1[1];
      scrni = first01;
      tmp49 = veccross(scrni, lookdir);
      scrut2 = vecnorm(tmp49);
      if (globalThis.Array.isArray(scrut2) && scrut2.length === 2) {
        first02 = scrut2[0];
        first12 = scrut2[1];
        scrnj = first02;
        xfov = fov1;
        yfov = fov1;
        xwinsize = winsize;
        ywinsize = winsize;
        tmp50 = 2.0 * dist;
        tmp51 = xfov / 2;
        tmp52 = dtor(tmp51);
        tmp53 = NofibPrelude.tan(tmp52);
        tmp54 = tmp50 * tmp53;
        tmp55 = tmp54 / xwinsize;
        magx = tmp55;
        tmp56 = 2.0 * dist;
        tmp57 = yfov / 2;
        tmp58 = dtor(tmp57);
        tmp59 = NofibPrelude.tan(tmp58);
        tmp60 = tmp56 * tmp59;
        tmp61 = tmp60 / ywinsize;
        magy = tmp61;
        tmp62 = vecscale(scrni, magx);
        scrnx = tmp62;
        tmp63 = vecscale(scrnj, magy);
        scrny = tmp63;
        tmp64 = 0.5 * xwinsize;
        tmp65 = vecscale(scrnx, tmp64);
        tmp66 = 0.5 * ywinsize;
        tmp67 = vecscale(scrny, tmp66);
        tmp68 = vecadd(tmp65, tmp67);
        tmp69 = vecsub(initfirstray, tmp68);
        firstray = tmp69;
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
};
sphereintersect = function sphereintersect(pos, dir, sp) {
  let param0, param1, param2, spos, rad, m, bm, m2, disc, slo, shi, scrut, scrut1, scrut2, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59;
  if (sp instanceof Sphere1.class) {
    param0 = sp.pos;
    param1 = sp.radius;
    param2 = sp.surface;
    spos = param0;
    rad = param1;
    tmp47 = vecsub(pos, spos);
    m = tmp47;
    tmp48 = vecdot(m, dir);
    bm = tmp48;
    tmp49 = vecdot(m, m);
    m2 = tmp49;
    tmp50 = bm * bm;
    tmp51 = tmp50 - m2;
    tmp52 = rad * rad;
    tmp53 = tmp51 + tmp52;
    disc = tmp53;
    tmp54 = - bm;
    tmp55 = NofibPrelude.sqrt(disc);
    tmp56 = tmp54 - tmp55;
    slo = tmp56;
    tmp57 = - bm;
    tmp58 = NofibPrelude.sqrt(disc);
    tmp59 = tmp57 + tmp58;
    shi = tmp59;
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
};
trace = function trace(spheres, pos, dir) {
  let f, sphmap, dists, scrut, first1, first0, mindist, sp, scrut1, tmp47, tmp48, tmp49, tmp50;
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
    let param0, param1, x, xs, scrut2, first11, first01, is_hit, where_hit, tmp51;
    if (xss instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xss instanceof NofibPrelude.Cons.class) {
      param0 = xss.head;
      param1 = xss.tail;
      x = param0;
      xs = param1;
      scrut2 = sphereintersect(pos, dir, x);
      if (globalThis.Array.isArray(scrut2) && scrut2.length === 2) {
        first01 = scrut2[0];
        first11 = scrut2[1];
        is_hit = first01;
        where_hit = first11;
        if (is_hit === true) {
          tmp51 = sphmap(xs);
          return NofibPrelude.Cons([
            where_hit,
            x
          ], tmp51)
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
  tmp47 = sphmap(spheres);
  dists = tmp47;
  scrut1 = NofibPrelude.null_(dists);
  if (scrut1 === true) {
    tmp48 = NofibPrelude.head(spheres);
    return [
      false,
      infinity,
      tmp48
    ]
  } else {
    tmp49 = NofibPrelude.head(dists);
    tmp50 = NofibPrelude.tail(dists);
    scrut = NofibPrelude.foldr(f, tmp49, tmp50);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      mindist = first0;
      sp = first1;
      return [
        true,
        mindist,
        sp
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  }
};
refractray = function refractray(newindex, olddir, innorm) {
  let dotp, matchIdent_17, scrut, first2, first1, first0, norm, k, nr, disc, t, scrut1, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64;
  tmp47 = vecdot(olddir, innorm);
  tmp48 = - tmp47;
  dotp = tmp48;
  scrut = dotp < 0.0;
  if (scrut === true) {
    tmp49 = - 1.0;
    tmp50 = vecscale(innorm, tmp49);
    tmp51 = - dotp;
    tmp52 = 1.0 / newindex;
    tmp53 = [
      tmp50,
      tmp51,
      tmp52
    ];
  } else {
    tmp53 = [
      innorm,
      dotp,
      newindex
    ];
  }
  matchIdent_17 = tmp53;
  if (globalThis.Array.isArray(matchIdent_17) && matchIdent_17.length === 3) {
    first0 = matchIdent_17[0];
    first1 = matchIdent_17[1];
    first2 = matchIdent_17[2];
    norm = first0;
    k = first1;
    nr = first2;
    tmp54 = nr * nr;
    tmp55 = k * k;
    tmp56 = 1.0 - tmp55;
    tmp57 = tmp54 * tmp56;
    tmp58 = 1.0 - tmp57;
    disc = tmp58;
    tmp59 = nr * k;
    tmp60 = NofibPrelude.sqrt(disc);
    tmp61 = tmp59 - tmp60;
    t = tmp61;
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
      tmp62 = vecscale(norm, t);
      tmp63 = vecscale(olddir, nr);
      tmp64 = vecadd(tmp62, tmp63);
      return [
        false,
        tmp64
      ]
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lightdirection = function lightdirection(l, pt) {
  let param0, param1, pos, col, param01, param11, dir, col1, tmp47, tmp48, tmp49;
  if (l instanceof Directional1.class) {
    param01 = l.x;
    param11 = l.y;
    dir = param01;
    col1 = param11;
    tmp47 = vecnorm(dir);
    tmp48 = NofibPrelude.fst(tmp47);
    return [
      tmp48,
      infinity
    ]
  } else if (l instanceof Point1.class) {
    param0 = l.x;
    param1 = l.y;
    pos = param0;
    col = param1;
    tmp49 = vecsub(pos, pt);
    return vecnorm(tmp49)
  } else {
    throw new globalThis.Error("match error");
  }
};
shadowed = function shadowed(pos, dir, lcolour) {
  let scrut, first2, first1, first0, is_hit, dist, sp, scrut1, tmp47, tmp48;
  tmp47 = vecscale(dir, epsilon);
  tmp48 = vecadd(pos, tmp47);
  scrut = trace(testspheres, tmp48, dir);
  if (globalThis.Array.isArray(scrut) && scrut.length === 3) {
    first0 = scrut[0];
    first1 = scrut[1];
    first2 = scrut[2];
    is_hit = first0;
    dist = first1;
    sp = first2;
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
};
lightray = function lightray(l, pos, norm, refl, surf) {
  let scrut, first1, first0, ldir, dist, cosangle, scrut1, first11, first01, is_inshadow, lcolour, diff, spow, spec, cosalpha, diffcont, speccont, scrut2, scrut3, bodycol, cosalpha1, diffcont1, speccont1, scrut4, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61;
  scrut = lightdirection(l, pos);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    ldir = first0;
    dist = first1;
    tmp47 = vecdot(ldir, norm);
    cosangle = tmp47;
    tmp48 = lightcolour(l);
    scrut1 = shadowed(pos, ldir, tmp48);
    if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
      first01 = scrut1[0];
      first11 = scrut1[1];
      is_inshadow = first01;
      lcolour = first11;
      if (is_inshadow === true) {
        return [
          0.0,
          0.0,
          0.0
        ]
      } else {
        diff = diffusesurf(surf);
        spow = specpowsurf(surf);
        scrut3 = cosangle <= 0.0;
        if (scrut3 === true) {
          tmp49 = bodysurf(surf);
          bodycol = tmp49;
          tmp50 = vecdot(refl, ldir);
          tmp51 = - tmp50;
          cosalpha1 = tmp51;
          tmp52 = - cosangle;
          tmp53 = vecscale(diff, tmp52);
          tmp54 = vecmult(tmp53, lcolour);
          diffcont1 = tmp54;
          scrut4 = cosalpha1 <= 0.0;
          if (scrut4 === true) {
            tmp55 = [
              0.0,
              0.0,
              0.0
            ];
          } else {
            tmp56 = NofibPrelude.power(cosalpha1, spow);
            tmp57 = vecscale(bodycol, tmp56);
            tmp55 = vecmult(tmp57, lcolour);
          }
          speccont1 = tmp55;
          return vecadd(diffcont1, speccont1)
        } else {
          spec = specularsurf(surf);
          cosalpha = vecdot(refl, ldir);
          tmp58 = vecscale(diff, cosangle);
          diffcont = vecmult(tmp58, lcolour);
          scrut2 = cosalpha < 0.0;
          if (scrut2 === true) {
            tmp59 = [
              0.0,
              0.0,
              0.0
            ];
          } else {
            tmp60 = NofibPrelude.power(cosalpha, spow);
            tmp61 = vecscale(spec, tmp60);
            tmp59 = vecmult(tmp61, lcolour);
          }
          speccont = tmp59;
          return vecadd(diffcont, speccont)
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
shade = function shade(lights, sp, lookpos, dir, dist, contrib) {
  let hitpos, ambientlight, surf, amb, norm, refl, diff, transmitted, simple, trintensity, matchIdent_1, scrut, first1, first0, is_tir, trcol, reflsurf, reflectiv, rcol, scrut1, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, lambda2;
  tmp47 = vecscale(dir, dist);
  tmp48 = vecadd(lookpos, tmp47);
  hitpos = tmp48;
  ambientlight = [
    1.0,
    1.0,
    1.0
  ];
  tmp49 = spheresurf(sp);
  surf = tmp49;
  tmp50 = ambientsurf(surf);
  tmp51 = vecmult(ambientlight, tmp50);
  amb = tmp51;
  tmp52 = spherenormal(hitpos, sp);
  norm = tmp52;
  tmp53 = - 2.0;
  tmp54 = vecdot(dir, norm);
  tmp55 = tmp53 * tmp54;
  tmp56 = vecscale(norm, tmp55);
  tmp57 = vecadd(dir, tmp56);
  refl = tmp57;
  lambda2 = (undefined, function (l) {
    return lightray(l, hitpos, norm, refl, surf)
  });
  tmp58 = NofibPrelude.map(lambda2, lights);
  tmp59 = vecsum(tmp58);
  diff = tmp59;
  tmp60 = transmitsurf(surf);
  transmitted = tmp60;
  tmp61 = vecadd(amb, diff);
  simple = tmp61;
  tmp62 = bodysurf(surf);
  tmp63 = vecscale(tmp62, transmitted);
  trintensity = tmp63;
  scrut = transmitted < epsilon;
  if (scrut === true) {
    tmp64 = [
      false,
      simple
    ];
  } else {
    tmp65 = refractsurf(surf);
    tmp64 = transmitray(lights, simple, hitpos, dir, tmp65, trintensity, contrib, norm);
  }
  matchIdent_1 = tmp64;
  if (globalThis.Array.isArray(matchIdent_1) && matchIdent_1.length === 2) {
    first0 = matchIdent_1[0];
    first1 = matchIdent_1[1];
    is_tir = first0;
    trcol = first1;
    tmp66 = specularsurf(surf);
    tmp67 = reflectsurf(surf);
    tmp68 = vecscale(tmp66, tmp67);
    reflsurf = tmp68;
    if (is_tir === true) {
      tmp69 = vecadd(trintensity, reflsurf);
    } else {
      tmp69 = reflsurf;
    }
    reflectiv = tmp69;
    scrut1 = is_zerovector(reflectiv);
    if (scrut1 === true) {
      tmp70 = trcol;
    } else {
      tmp70 = reflectray(hitpos, refl, lights, reflectiv, contrib, trcol);
    }
    rcol = tmp70;
    return rcol
  } else {
    throw new globalThis.Error("match error");
  }
};
transmitray = function transmitray(lights, colour, pos, dir, index, intens, contrib, norm) {
  let newcontrib, scrut, first1, first0, is_tir, newdir, nearpos, scrut1, first2, first11, first01, is_hit, dist, sp, newcol, scrut2, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52;
  tmp47 = vecmult(intens, contrib);
  newcontrib = tmp47;
  scrut = refractray(index, dir, norm);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    is_tir = first0;
    newdir = first1;
    tmp48 = vecscale(newdir, epsilon);
    tmp49 = vecadd(pos, tmp48);
    nearpos = tmp49;
    scrut1 = trace(testspheres, nearpos, newdir);
    if (globalThis.Array.isArray(scrut1) && scrut1.length === 3) {
      first01 = scrut1[0];
      first11 = scrut1[1];
      first2 = scrut1[2];
      is_hit = first01;
      dist = first11;
      sp = first2;
      if (is_hit === true) {
        tmp50 = shade(lights, sp, nearpos, newdir, dist, newcontrib);
      } else {
        tmp50 = background;
      }
      newcol = tmp50;
      scrut2 = is_zerovector(newcontrib);
      if (scrut2 === true) {
        return [
          false,
          colour
        ]
      } else {
        tmp51 = vecmult(newcol, intens);
        tmp52 = vecadd(tmp51, colour);
        return [
          false,
          tmp52
        ]
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
reflectray = function reflectray(pos, newdir, lights, intens, contrib, colour) {
  let newcontrib, nearpos, scrut, first2, first1, first0, is_hit, dist, sp, newcol, scrut1, tmp47, tmp48, tmp49, tmp50, tmp51;
  tmp47 = vecmult(intens, contrib);
  newcontrib = tmp47;
  tmp48 = vecscale(newdir, epsilon);
  tmp49 = vecadd(pos, tmp48);
  nearpos = tmp49;
  scrut = trace(testspheres, nearpos, newdir);
  if (globalThis.Array.isArray(scrut) && scrut.length === 3) {
    first0 = scrut[0];
    first1 = scrut[1];
    first2 = scrut[2];
    is_hit = first0;
    dist = first1;
    sp = first2;
    if (is_hit === true) {
      tmp50 = shade(lights, sp, nearpos, newdir, dist, newcontrib);
    } else {
      tmp50 = background;
    }
    newcol = tmp50;
    scrut1 = is_zerovector(newcontrib);
    if (scrut1 === true) {
      return colour
    } else {
      tmp51 = vecmult(newcol, intens);
      return vecadd(colour, tmp51)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
tracepixel = function tracepixel(spheres, lights, x, y, firstray, scrnx, scrny) {
  let pos, scrut, first1, first0, dir, tracepixel_Tup2_1, scrut1, first2, first11, first01, hit, dist, sp, tmp47, tmp48, tmp49, tmp50;
  pos = lookfrom;
  tmp47 = vecscale(scrnx, x);
  tmp48 = vecadd(firstray, tmp47);
  tmp49 = vecscale(scrny, y);
  tmp50 = vecadd(tmp48, tmp49);
  scrut = vecnorm(tmp50);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    dir = first0;
    tracepixel_Tup2_1 = first1;
    scrut1 = trace(spheres, pos, dir);
    if (globalThis.Array.isArray(scrut1) && scrut1.length === 3) {
      first01 = scrut1[0];
      first11 = scrut1[1];
      first2 = scrut1[2];
      hit = first01;
      dist = first11;
      sp = first2;
      if (hit === true) {
        return shade(lights, sp, pos, dir, dist, [
          1.0,
          1.0,
          1.0
        ])
      } else {
        return background
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
z_of_int = function z_of_int(x) {
  return runtime.safeCall(globalThis.BigInt(x))
};
hash = function hash(param) {
  let u8, tmp47, tmp48, lambda2;
  u8 = function u8(x) {
    let tmp49, tmp50;
    tmp49 = 255 * x;
    tmp50 = NofibPrelude.round(tmp49);
    return z_of_int(tmp50)
  };
  lambda2 = (undefined, function (rgb, acc) {
    let first2, first1, first0, r, g, b, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59;
    if (globalThis.Array.isArray(rgb) && rgb.length === 3) {
      first0 = rgb[0];
      first1 = rgb[1];
      first2 = rgb[2];
      r = first0;
      g = first1;
      b = first2;
      tmp49 = u8(r);
      tmp50 = u8(g);
      tmp51 = z_of_int(7);
      tmp52 = tmp50 * tmp51;
      tmp53 = tmp49 + tmp52;
      tmp54 = u8(b);
      tmp55 = z_of_int(23);
      tmp56 = tmp54 * tmp55;
      tmp57 = tmp53 + tmp56;
      tmp58 = z_of_int(61);
      tmp59 = acc * tmp58;
      return tmp57 + tmp59
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp47 = lambda2;
  tmp48 = z_of_int(0);
  return NofibPrelude.foldr(tmp47, tmp48, param)
};
ray = function ray(winsize) {
  let f, lscomp1, lights, scrut, first2, first1, first0, firstray, scrnx, scrny, tmp47, tmp48;
  lights = testlights;
  scrut = camparams(lookfrom, lookat, vup, fov, winsize);
  if (globalThis.Array.isArray(scrut) && scrut.length === 3) {
    first0 = scrut[0];
    first1 = scrut[1];
    first2 = scrut[2];
    firstray = first0;
    scrnx = first1;
    scrny = first2;
    f = function f(i, j) {
      return tracepixel(testspheres, lights, i, j, firstray, scrnx, scrny)
    };
    lscomp1 = function lscomp1(ls1) {
      let lscomp2, param0, param1, i, t1, tmp49, tmp50;
      if (ls1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls1 instanceof NofibPrelude.Cons.class) {
        param0 = ls1.head;
        param1 = ls1.tail;
        i = param0;
        t1 = param1;
        lscomp2 = function lscomp2(ls2) {
          let param01, param11, j, t2, tmp51, tmp52;
          if (ls2 instanceof NofibPrelude.Nil.class) {
            return lscomp1(t1)
          } else if (ls2 instanceof NofibPrelude.Cons.class) {
            param01 = ls2.head;
            param11 = ls2.tail;
            j = param01;
            t2 = param11;
            tmp51 = f(i, j);
            tmp52 = lscomp2(t2);
            return NofibPrelude.Cons([
              [
                i,
                j
              ],
              tmp51
            ], tmp52)
          } else {
            throw new globalThis.Error("match error");
          }
        };
        tmp49 = winsize - 1;
        tmp50 = NofibPrelude.enumFromTo(0, tmp49);
        return lscomp2(tmp50)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp47 = winsize - 1;
    tmp48 = NofibPrelude.enumFromTo(0, tmp47);
    return lscomp1(tmp48)
  } else {
    throw new globalThis.Error("match error");
  }
};
run = function run(winsize) {
  let tmp47, tmp48;
  tmp47 = ray(winsize);
  tmp48 = NofibPrelude.map(NofibPrelude.snd, tmp47);
  return hash(tmp48)
};
testSphere_nofib = function testSphere_nofib(n) {
  return run(n)
};
lambda = (undefined, function () {
  return globalThis.Math.PI
});
tmp = lambda();
pi = tmp;
epsilon = 0.000001;
infinity = 100000000.0;
Light1 = class Light {
  constructor() {}
  toString() { return "Light"; }
};
Directional1 = function Directional(x1, y1) {
  return new Directional.class(x1, y1);
};
Directional1.class = class Directional extends Light1 {
  constructor(x, y) {
    super();
    this.x = x;
    this.y = y;
  }
  toString() { return "Directional(" + globalThis.Predef.render(this.x) + ", " + globalThis.Predef.render(this.y) + ")"; }
};
Point1 = function Point(x1, y1) {
  return new Point.class(x1, y1);
};
Point1.class = class Point extends Light1 {
  constructor(x, y) {
    super();
    this.x = x;
    this.y = y;
  }
  toString() { return "Point(" + globalThis.Predef.render(this.x) + ", " + globalThis.Predef.render(this.y) + ")"; }
};
Surfspec1 = class Surfspec {
  constructor() {}
  toString() { return "Surfspec"; }
};
Ambient1 = function Ambient(v1) {
  return new Ambient.class(v1);
};
Ambient1.class = class Ambient extends Surfspec1 {
  constructor(v) {
    super();
    this.v = v;
  }
  toString() { return "Ambient(" + globalThis.Predef.render(this.v) + ")"; }
};
Diffuse1 = function Diffuse(v1) {
  return new Diffuse.class(v1);
};
Diffuse1.class = class Diffuse extends Surfspec1 {
  constructor(v) {
    super();
    this.v = v;
  }
  toString() { return "Diffuse(" + globalThis.Predef.render(this.v) + ")"; }
};
Specular1 = function Specular(v1) {
  return new Specular.class(v1);
};
Specular1.class = class Specular extends Surfspec1 {
  constructor(v) {
    super();
    this.v = v;
  }
  toString() { return "Specular(" + globalThis.Predef.render(this.v) + ")"; }
};
Specpow1 = function Specpow(v1) {
  return new Specpow.class(v1);
};
Specpow1.class = class Specpow extends Surfspec1 {
  constructor(v) {
    super();
    this.v = v;
  }
  toString() { return "Specpow(" + globalThis.Predef.render(this.v) + ")"; }
};
Reflect1 = function Reflect(v1) {
  return new Reflect.class(v1);
};
Reflect1.class = class Reflect extends Surfspec1 {
  constructor(v) {
    super();
    this.v = v;
  }
  toString() { return "Reflect(" + globalThis.Predef.render(this.v) + ")"; }
};
Transmit1 = function Transmit(v1) {
  return new Transmit.class(v1);
};
Transmit1.class = class Transmit extends Surfspec1 {
  constructor(v) {
    super();
    this.v = v;
  }
  toString() { return "Transmit(" + globalThis.Predef.render(this.v) + ")"; }
};
Refract1 = function Refract(v1) {
  return new Refract.class(v1);
};
Refract1.class = class Refract extends Surfspec1 {
  constructor(v) {
    super();
    this.v = v;
  }
  toString() { return "Refract(" + globalThis.Predef.render(this.v) + ")"; }
};
Body1 = function Body(v1) {
  return new Body.class(v1);
};
Body1.class = class Body extends Surfspec1 {
  constructor(v) {
    super();
    this.v = v;
  }
  toString() { return "Body(" + globalThis.Predef.render(this.v) + ")"; }
};
Sphere1 = function Sphere(pos1, radius1, surface1) {
  return new Sphere.class(pos1, radius1, surface1);
};
Sphere1.class = class Sphere {
  constructor(pos, radius, surface) {
    this.pos = pos;
    this.radius = radius;
    this.surface = surface;
  }
  toString() { return "Sphere(" + globalThis.Predef.render(this.pos) + ", " + globalThis.Predef.render(this.radius) + ", " + globalThis.Predef.render(this.surface) + ")"; }
};
lookat = [
  0.0,
  0.0,
  0.0
];
vup = [
  0.0,
  0.0,
  1.0
];
fov = 45.0;
tmp1 = Ambient1([
  0.035,
  0.0325,
  0.025
]);
tmp2 = Diffuse1([
  0.5,
  0.45,
  0.35
]);
tmp3 = Specular1([
  0.8,
  0.8,
  0.8
]);
tmp4 = Specpow1(3.0);
tmp5 = Reflect1(0.5);
tmp6 = NofibPrelude.Cons(tmp5, NofibPrelude.Nil);
tmp7 = NofibPrelude.Cons(tmp4, tmp6);
tmp8 = NofibPrelude.Cons(tmp3, tmp7);
tmp9 = NofibPrelude.Cons(tmp2, tmp8);
tmp10 = NofibPrelude.Cons(tmp1, tmp9);
s2 = tmp10;
tmp11 = Sphere1([
  0.0,
  0.0,
  0.0
], 0.5, s2);
tmp12 = Sphere1([
  0.272166,
  0.272166,
  0.544331
], 0.166667, s2);
tmp13 = Sphere1([
  0.643951,
  0.172546,
  0.0
], 0.166667, s2);
tmp14 = Sphere1([
  0.172546,
  0.643951,
  0.0
], 0.166667, s2);
tmp15 = - 0.371785;
tmp16 = Sphere1([
  tmp15,
  0.0996195,
  0.544331
], 0.166667, s2);
tmp17 = - 0.471405;
tmp18 = Sphere1([
  tmp17,
  0.471405,
  0.0
], 0.166667, s2);
tmp19 = - 0.643951;
tmp20 = - 0.172546;
tmp21 = Sphere1([
  tmp19,
  tmp20,
  0.0
], 0.166667, s2);
tmp22 = - 0.371785;
tmp23 = Sphere1([
  0.0996195,
  tmp22,
  0.544331
], 0.166667, s2);
tmp24 = - 0.172546;
tmp25 = - 0.643951;
tmp26 = Sphere1([
  tmp24,
  tmp25,
  0.0
], 0.166667, s2);
tmp27 = - 0.471405;
tmp28 = Sphere1([
  0.471405,
  tmp27,
  0.0
], 0.166667, s2);
tmp29 = NofibPrelude.Cons(tmp28, NofibPrelude.Nil);
tmp30 = NofibPrelude.Cons(tmp26, tmp29);
tmp31 = NofibPrelude.Cons(tmp23, tmp30);
tmp32 = NofibPrelude.Cons(tmp21, tmp31);
tmp33 = NofibPrelude.Cons(tmp18, tmp32);
tmp34 = NofibPrelude.Cons(tmp16, tmp33);
tmp35 = NofibPrelude.Cons(tmp14, tmp34);
tmp36 = NofibPrelude.Cons(tmp13, tmp35);
tmp37 = NofibPrelude.Cons(tmp12, tmp36);
tmp38 = NofibPrelude.Cons(tmp11, tmp37);
testspheres = tmp38;
tmp39 = Point1([
  4.0,
  3.0,
  2.0
], [
  0.288675,
  0.288675,
  0.288675
]);
tmp40 = - 4.0;
tmp41 = Point1([
  1.0,
  tmp40,
  4.0
], [
  0.288675,
  0.288675,
  0.288675
]);
tmp42 = - 3.0;
tmp43 = Point1([
  tmp42,
  1.0,
  5.0
], [
  0.288675,
  0.288675,
  0.288675
]);
tmp44 = NofibPrelude.Cons(tmp43, NofibPrelude.Nil);
tmp45 = NofibPrelude.Cons(tmp41, tmp44);
tmp46 = NofibPrelude.Cons(tmp39, tmp45);
testlights = tmp46;
lookfrom = [
  2.1,
  1.3,
  1.7
];
background = [
  0.078,
  0.361,
  0.753
];
lambda1 = (undefined, function () {
  return testSphere_nofib(30)
});
BenchmarkPrelude.benchmark(lambda1)