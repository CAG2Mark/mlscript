import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let testMandel2_nofib, new_x, NS1, point_colour, check_perim, radius, np, build_tree, EW1, new_y, MandTree1, Leaf1, equalp, check_radius, nq, finite, size, pmn, pmx, qmn, qmx, m, num_cols, delta_p, delta_q, up, down, left, right, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, lambda;
equalp = function equalp(p1, p2) {
  let first1, first0, x1, x2, first11, first01, y1, y2, scrut, scrut1;
  if (globalThis.Array.isArray(p1) && p1.length === 2) {
    first0 = p1[0];
    first1 = p1[1];
    x1 = first0;
    x2 = first1;
    if (globalThis.Array.isArray(p2) && p2.length === 2) {
      first01 = p2[0];
      first11 = p2[1];
      y1 = first01;
      y2 = first11;
      scrut = x1 == y1;
      if (scrut === true) {
        scrut1 = x2 == y2;
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
};
np = function np(x) {
  let tmp10;
  tmp10 = x * delta_p;
  return pmn + tmp10
};
nq = function nq(y) {
  let tmp10;
  tmp10 = y * delta_q;
  return qmn + tmp10
};
radius = function radius(x, y) {
  let tmp10, tmp11;
  tmp10 = x * x;
  tmp11 = y * y;
  return tmp10 + tmp11
};
new_x = function new_x(x, y, p) {
  let tmp10, tmp11, tmp12;
  tmp10 = x * x;
  tmp11 = y * y;
  tmp12 = tmp10 - tmp11;
  return tmp12 + p
};
new_y = function new_y(x, y, q) {
  let tmp10, tmp11;
  tmp10 = 2.0 * x;
  tmp11 = tmp10 * y;
  return tmp11 + q
};
finite = function finite(t) {
  let param0, param1, t1, t2, scrut, scrut1, param01, param11, t11, t21, scrut2, scrut3, param02, c;
  if (t instanceof Leaf1.class) {
    param02 = t.colour;
    c = param02;
    return c == c
  } else if (t instanceof NS1.class) {
    param01 = t.l;
    param11 = t.r;
    t11 = param01;
    t21 = param11;
    scrut2 = finite(t11);
    if (scrut2 === true) {
      scrut3 = finite(t21);
      if (scrut3 === true) {
        return true
      } else {
        return false
      }
    } else {
      return false
    }
  } else if (t instanceof EW1.class) {
    param0 = t.l;
    param1 = t.r;
    t1 = param0;
    t2 = param1;
    scrut = finite(t1);
    if (scrut === true) {
      scrut1 = finite(t2);
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
};
check_radius = function check_radius(p, q, k, x, y) {
  let xn, yn, r, kp, scrut, scrut1, tmp10, tmp11, tmp12, tmp13;
  tmp10 = new_x(x, y, p);
  xn = tmp10;
  tmp11 = new_y(x, y, q);
  yn = tmp11;
  tmp12 = radius(xn, yn);
  r = tmp12;
  tmp13 = k + 1;
  kp = tmp13;
  scrut1 = kp == num_cols;
  if (scrut1 === true) {
    return 0
  } else {
    scrut = r > m;
    if (scrut === true) {
      return kp
    } else {
      return check_radius(p, q, kp, xn, yn)
    }
  }
};
point_colour = function point_colour(xy) {
  let first1, first0, x, y, tmp10, tmp11;
  if (globalThis.Array.isArray(xy) && xy.length === 2) {
    first0 = xy[0];
    first1 = xy[1];
    x = first0;
    y = first1;
    tmp10 = np(x);
    tmp11 = nq(y);
    return check_radius(tmp10, tmp11, 0, 0.0, 0.0)
  } else {
    throw new globalThis.Error("match error");
  }
};
check_perim = function check_perim(x1y1, x2y2) {
  let check_line, col1, first1, first0, x1, y1, first11, first01, x2, y2, col2, col3, col4, corners_diff, scrut, scrut1, scrut2, scrut3, scrut4, scrut5, scrut6, scrut7, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15;
  tmp10 = point_colour(x1y1);
  col1 = tmp10;
  if (globalThis.Array.isArray(x1y1) && x1y1.length === 2) {
    first0 = x1y1[0];
    first1 = x1y1[1];
    x1 = first0;
    y1 = first1;
    if (globalThis.Array.isArray(x2y2) && x2y2.length === 2) {
      first01 = x2y2[0];
      first11 = x2y2[1];
      x2 = first01;
      y2 = first11;
      check_line = function check_line(xcyc, xdyd) {
        let first12, first02, xc, yc, first13, first03, xd, yd, finished, scrut8, scrut9, scrut10, scrut11, tmp16, tmp17, tmp18, tmp19, tmp20;
        if (globalThis.Array.isArray(xcyc) && xcyc.length === 2) {
          first02 = xcyc[0];
          first12 = xcyc[1];
          xc = first02;
          yc = first12;
          if (globalThis.Array.isArray(xdyd) && xdyd.length === 2) {
            first03 = xdyd[0];
            first13 = xdyd[1];
            xd = first03;
            yd = first13;
            scrut10 = equalp(xdyd, right);
            if (scrut10 === true) {
              tmp16 = xc >= x2;
            } else {
              scrut9 = equalp(xdyd, down);
              if (scrut9 === true) {
                tmp16 = yc <= y2;
              } else {
                scrut8 = equalp(xdyd, left);
                if (scrut8 === true) {
                  tmp16 = xc <= x1;
                } else {
                  tmp16 = yc >= y1;
                }
              }
            }
            finished = tmp16;
            if (finished === true) {
              return true
            } else {
              tmp17 = point_colour(xcyc);
              tmp18 = tmp17 == col1;
              scrut11 = BenchmarkPrelude.not(tmp18);
              if (scrut11 === true) {
                return false
              } else {
                tmp19 = xc + xd;
                tmp20 = yc + yd;
                return check_line([
                  tmp19,
                  tmp20
                ], [
                  xd,
                  yd
                ])
              }
            }
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      };
      scrut7 = equalp(x1y1, x2y2);
      if (scrut7 === true) {
        return col1
      } else {
        col2 = point_colour([
          x2,
          y1
        ]);
        col3 = point_colour(x2y2);
        col4 = point_colour([
          x1,
          y2
        ]);
        scrut = col1 == col2;
        if (scrut === true) {
          scrut1 = col1 == col3;
          if (scrut1 === true) {
            scrut2 = col1 == col4;
            if (scrut2 === true) {
              tmp11 = false;
            } else {
              tmp11 = true;
            }
          } else {
            tmp11 = true;
          }
        } else {
          tmp11 = true;
        }
        corners_diff = tmp11;
        if (corners_diff === true) {
          return - 1
        } else {
          tmp12 = x1 + 1;
          scrut3 = check_line([
            tmp12,
            y1
          ], right);
          if (scrut3 === true) {
            tmp13 = y1 + 1;
            scrut4 = check_line([
              x2,
              tmp13
            ], down);
            if (scrut4 === true) {
              tmp14 = x2 - 1;
              scrut5 = check_line([
                tmp14,
                y2
              ], left);
              if (scrut5 === true) {
                tmp15 = y2 - 1;
                scrut6 = check_line([
                  x1,
                  tmp15
                ], up);
                if (scrut6 === true) {
                  return col1
                } else {
                  return - 1
                }
              } else {
                return - 1
              }
            } else {
              return - 1
            }
          } else {
            return - 1
          }
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
build_tree = function build_tree(x1y1, x2y2) {
  let first1, first0, x1, y1, first11, first01, x2, y2, rec_col, split, scrut, split_x, split_y, nsp1, nsp2, nsp3, nsp4, ewp1, ewp2, ewp3, ewp4, scrut1, scrut2, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23;
  if (globalThis.Array.isArray(x1y1) && x1y1.length === 2) {
    first0 = x1y1[0];
    first1 = x1y1[1];
    x1 = first0;
    y1 = first1;
    if (globalThis.Array.isArray(x2y2) && x2y2.length === 2) {
      first01 = x2y2[0];
      first11 = x2y2[1];
      x2 = first01;
      y2 = first11;
      tmp10 = check_perim(x1y1, x2y2);
      rec_col = tmp10;
      tmp11 = - 1;
      tmp12 = rec_col == tmp11;
      scrut2 = BenchmarkPrelude.not(tmp12);
      if (scrut2 === true) {
        return Leaf1(rec_col)
      } else {
        tmp13 = x2 - x1;
        tmp14 = y2 - y1;
        scrut = tmp13 >= tmp14;
        if (scrut === true) {
          tmp15 = "NS";
        } else {
          tmp15 = "EW";
        }
        split = tmp15;
        tmp16 = x2 + x1;
        split_x = NofibPrelude.intDiv(tmp16, 2);
        tmp17 = y2 + y1;
        split_y = NofibPrelude.intDiv(tmp17, 2);
        nsp1 = x1y1;
        nsp2 = [
          split_x,
          y2
        ];
        tmp18 = split_x + 1;
        nsp3 = [
          tmp18,
          y1
        ];
        nsp4 = x2y2;
        ewp1 = x1y1;
        ewp2 = [
          x2,
          split_y
        ];
        tmp19 = split_y + 1;
        ewp3 = [
          x1,
          tmp19
        ];
        ewp4 = x2y2;
        scrut1 = split == "NS";
        if (scrut1 === true) {
          tmp20 = build_tree(nsp1, nsp2);
          tmp21 = build_tree(nsp3, nsp4);
          return NS1(tmp20, tmp21)
        } else {
          tmp22 = build_tree(ewp1, ewp2);
          tmp23 = build_tree(ewp3, ewp4);
          return EW1(tmp22, tmp23)
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
testMandel2_nofib = function testMandel2_nofib(n) {
  let tmp10, tmp11;
  tmp10 = NofibPrelude.intDiv(size, 2);
  tmp11 = build_tree([
    0,
    0
  ], [
    size,
    tmp10
  ]);
  return finite(tmp11)
};
MandTree1 = class MandTree {
  constructor() {}
  toString() { return "MandTree"; }
};
NS1 = function NS(l1, r1) {
  return new NS.class(l1, r1);
};
NS1.class = class NS extends MandTree1 {
  constructor(l, r) {
    super();
    this.l = l;
    this.r = r;
  }
  toString() { return "NS(" + globalThis.Predef.render(this.l) + ", " + globalThis.Predef.render(this.r) + ")"; }
};
EW1 = function EW(l1, r1) {
  return new EW.class(l1, r1);
};
EW1.class = class EW extends MandTree1 {
  constructor(l, r) {
    super();
    this.l = l;
    this.r = r;
  }
  toString() { return "EW(" + globalThis.Predef.render(this.l) + ", " + globalThis.Predef.render(this.r) + ")"; }
};
Leaf1 = function Leaf(colour1) {
  return new Leaf.class(colour1);
};
Leaf1.class = class Leaf extends MandTree1 {
  constructor(colour) {
    super();
    this.colour = colour;
  }
  toString() { return "Leaf(" + globalThis.Predef.render(this.colour) + ")"; }
};
size = 200;
tmp = - 2.25;
pmn = tmp;
pmx = 0.75;
tmp1 = - 1.5;
qmn = tmp1;
qmx = 1.5;
m = 20;
num_cols = 26;
tmp2 = pmx - pmn;
tmp3 = size - 1;
tmp4 = tmp2 / tmp3;
delta_p = tmp4;
tmp5 = qmx - qmn;
tmp6 = size - 1;
tmp7 = tmp5 / tmp6;
delta_q = tmp7;
tmp8 = - 1;
up = [
  0,
  tmp8
];
down = [
  0,
  1
];
tmp9 = - 1;
left = [
  tmp9,
  0
];
right = [
  1,
  0
];
lambda = (undefined, function () {
  return testMandel2_nofib(0)
});
BenchmarkPrelude.benchmark(lambda)