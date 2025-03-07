import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let testTreejoin_nofib, isDigit, readTree, Empty1, isSpace, readInt, join, lookupT, Tree1, Node1, Leaf1, insertT, lambda;
isSpace = function isSpace(c) {
  let tmp, tmp1;
  tmp = c === " ";
  tmp1 = c === "\n";
  return tmp || tmp1
};
isDigit = function isDigit(c) {
  let n, tmp, tmp1, tmp2;
  tmp = runtime.safeCall(c.codePointAt(0));
  n = tmp;
  tmp1 = n >= 48;
  tmp2 = n <= 57;
  return tmp1 && tmp2
};
insertT = function insertT(k, e, t) {
  let param0, param1, k_, k__, l_, scrut, scrut1, param01, param11, param2, k_1, l, r, scrut2, tmp, tmp1, tmp2, tmp3, tmp4;
  if (t instanceof Node1.class) {
    param01 = t.k;
    param11 = t.l;
    param2 = t.r;
    k_1 = param01;
    l = param11;
    r = param2;
    scrut2 = k <= k_1;
    if (scrut2 === true) {
      tmp = insertT(k, e, l);
      return Node1(k_1, tmp, r)
    } else {
      tmp1 = insertT(k, e, r);
      return Node1(k_1, l, tmp1)
    }
  } else if (t instanceof Leaf1.class) {
    param0 = t.k;
    param1 = t.e;
    k_ = param0;
    k__ = param1;
    tmp2 = Leaf1(k, e);
    l_ = tmp2;
    scrut1 = k < k_;
    if (scrut1 === true) {
      tmp3 = Leaf1(k_, k__);
      return Node1(k, l_, tmp3)
    } else {
      scrut = k > k_;
      if (scrut === true) {
        tmp4 = Leaf1(k_, k__);
        return Node1(k_, tmp4, l_)
      } else {
        throw globalThis.Error("already exist");
      }
    }
  } else if (t instanceof Empty1.class) {
    return Leaf1(k, e)
  } else {
    throw new globalThis.Error("match error");
  }
};
lookupT = function lookupT(k, t) {
  let param0, param1, k_, e, scrut, param01, param11, param2, k_1, l, r, scrut1;
  if (t instanceof Node1.class) {
    param01 = t.k;
    param11 = t.l;
    param2 = t.r;
    k_1 = param01;
    l = param11;
    r = param2;
    scrut1 = k <= k_1;
    if (scrut1 === true) {
      return lookupT(k, l)
    } else {
      return lookupT(k, r)
    }
  } else if (t instanceof Leaf1.class) {
    param0 = t.k;
    param1 = t.e;
    k_ = param0;
    e = param1;
    scrut = k === k_;
    if (scrut === true) {
      return NofibPrelude.Some(e)
    } else {
      return NofibPrelude.None
    }
  } else if (t instanceof Empty1.class) {
    return NofibPrelude.None
  } else {
    throw new globalThis.Error("match error");
  }
};
readInt = function readInt(s) {
  let readInt_;
  readInt_ = function readInt_(n, cs) {
    let s_, param0, param1, c, cs_, s_1, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    if (cs instanceof NofibPrelude.Cons.class) {
      param0 = cs.head;
      param1 = cs.tail;
      c = param0;
      cs_ = param1;
      scrut = isDigit(c);
      if (scrut === true) {
        tmp = n * 10;
        tmp1 = runtime.safeCall(c.codePointAt(0));
        tmp2 = tmp + tmp1;
        tmp3 = tmp2 - 48;
        return readInt_(tmp3, cs_)
      } else {
        tmp4 = NofibPrelude.Cons(c, cs);
        tmp5 = NofibPrelude.dropWhile(isSpace, tmp4);
        s_1 = tmp5;
        return [
          n,
          s_1
        ]
      }
    } else {
      tmp6 = NofibPrelude.dropWhile(isSpace, cs);
      s_ = tmp6;
      return [
        n,
        s_
      ]
    }
  };
  return readInt_(0, s)
};
join = function join(t1, t2, j) {
  let param0, param1, param2, k, l, r, param01, param11, k1, first2, first1, first0, a, b, c, scrut, param02, first21, first11, first01, d, e, f, tmp;
  if (t1 instanceof Empty1.class) {
    return j
  } else {
    if (t2 instanceof Empty1.class) {
      return j
    } else {
      if (t1 instanceof Leaf1.class) {
        param01 = t1.k;
        param11 = t1.e;
        k1 = param01;
        if (globalThis.Array.isArray(param11) && param11.length === 3) {
          first0 = param11[0];
          first1 = param11[1];
          first2 = param11[2];
          a = first0;
          b = first1;
          c = first2;
          scrut = lookupT(c, t2);
          if (scrut instanceof NofibPrelude.None.class) {
            return j
          } else if (scrut instanceof NofibPrelude.Some.class) {
            param02 = scrut.x;
            if (globalThis.Array.isArray(param02) && param02.length === 3) {
              first01 = param02[0];
              first11 = param02[1];
              first21 = param02[2];
              d = first01;
              e = first11;
              f = first21;
              return insertT(c, [
                a,
                b,
                c,
                d,
                e
              ], j)
            } else {
              throw new globalThis.Error("match error");
            }
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else if (t1 instanceof Node1.class) {
        param0 = t1.k;
        param1 = t1.l;
        param2 = t1.r;
        k = param0;
        l = param1;
        r = param2;
        tmp = join(r, t2, j);
        return join(l, t2, tmp)
      } else {
        throw new globalThis.Error("match error");
      }
    }
  }
};
readTree = function readTree(fk, s, t) {
  let scrut, first1, first0, f, s_, scrut1, first11, first01, g, s__, scrut2, first12, first02, h, s___, e, k, tmp, tmp1;
  if (s instanceof NofibPrelude.Nil.class) {
    return t
  } else {
    scrut = readInt(s);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      f = first0;
      s_ = first1;
      scrut1 = readInt(s_);
      if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
        first01 = scrut1[0];
        first11 = scrut1[1];
        g = first01;
        s__ = first11;
        scrut2 = readInt(s__);
        if (globalThis.Array.isArray(scrut2) && scrut2.length === 2) {
          first02 = scrut2[0];
          first12 = scrut2[1];
          h = first02;
          s___ = first12;
          e = [
            f,
            g,
            h
          ];
          tmp = runtime.safeCall(fk(e));
          k = tmp;
          tmp1 = insertT(k, e, t);
          return readTree(fk, s___, tmp1)
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
};
testTreejoin_nofib = function testTreejoin_nofib(n) {
  let c1, c2, a, b, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, lambda1, lambda2;
  tmp = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/1500.1"));
  tmp1 = runtime.safeCall(tmp.toString());
  tmp2 = NofibPrelude.nofibStringToList(tmp1);
  c1 = tmp2;
  tmp3 = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/1500.2"));
  tmp4 = runtime.safeCall(tmp3.toString());
  tmp5 = NofibPrelude.nofibStringToList(tmp4);
  c2 = tmp5;
  lambda1 = (undefined, function (caseScrut) {
    let first2, first1, first0, xx;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      first2 = caseScrut[2];
      xx = first0;
      return xx
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp6 = lambda1;
  tmp7 = readTree(tmp6, c1, Empty1);
  a = tmp7;
  lambda2 = (undefined, function (caseScrut) {
    let first2, first1, first0, xx;
    if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 3) {
      first0 = caseScrut[0];
      first1 = caseScrut[1];
      first2 = caseScrut[2];
      xx = first0;
      return xx
    } else {
      throw new globalThis.Error("match error");
    }
  });
  tmp8 = lambda2;
  tmp9 = readTree(tmp8, c2, Empty1);
  b = tmp9;
  return join(a, b, Empty1)
};
Tree1 = class Tree {
  constructor() {}
  toString() { return "Tree"; }
};
Node1 = function Node(k1, l1, r1) {
  return new Node.class(k1, l1, r1);
};
Node1.class = class Node extends Tree1 {
  constructor(k, l, r) {
    super();
    this.k = k;
    this.l = l;
    this.r = r;
  }
  toString() { return "Node(" + globalThis.Predef.render(this.k) + ", " + globalThis.Predef.render(this.l) + ", " + globalThis.Predef.render(this.r) + ")"; }
};
Leaf1 = function Leaf(k1, e1) {
  return new Leaf.class(k1, e1);
};
Leaf1.class = class Leaf extends Tree1 {
  constructor(k, e) {
    super();
    this.k = k;
    this.e = e;
  }
  toString() { return "Leaf(" + globalThis.Predef.render(this.k) + ", " + globalThis.Predef.render(this.e) + ")"; }
};
const Empty$class = class Empty extends Tree1 {
  constructor() {
    super();
  }
  toString() { return "Empty"; }
}; Empty1 = new Empty$class;
Empty1.class = Empty$class;
lambda = (undefined, function () {
  let tmp;
  tmp = testTreejoin_nofib(0);
  return runtime.safeCall(tmp.toString())
});
BenchmarkPrelude.benchmark(lambda)