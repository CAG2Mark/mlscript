import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let readInt_, treejoin1, lambda, lambda1;
lambda = (undefined, function (caseScrut) {
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
readInt_ = function readInt_(n, cs) {
  let s_, param0, param1, c, cs_, s_1, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
  if (cs instanceof NofibPrelude.Cons.class) {
    param0 = cs.head;
    param1 = cs.tail;
    c = param0;
    cs_ = param1;
    scrut = treejoin1.isDigit(c);
    if (scrut === true) {
      tmp = n * 10;
      tmp1 = runtime.safeCall(c.codePointAt(0));
      tmp2 = tmp + tmp1;
      tmp3 = tmp2 - 48;
      return readInt_(tmp3, cs_)
    } else {
      tmp4 = NofibPrelude.Cons(c, cs);
      tmp5 = NofibPrelude.dropWhile(treejoin1.isSpace, tmp4);
      s_1 = tmp5;
      return [
        n,
        s_1
      ]
    }
  } else {
    tmp6 = NofibPrelude.dropWhile(treejoin1.isSpace, cs);
    s_ = tmp6;
    return [
      n,
      s_
    ]
  }
};
treejoin1 = class treejoin {
  static {
    treejoin1 = treejoin;
    let lambda2;
    this.Tree = class Tree {
      constructor() {}
      toString() { return "Tree"; }
    };
    this.Node = function Node(k1, l1, r1) {
      return new Node.class(k1, l1, r1);
    };
    this.Node.class = class Node extends treejoin.Tree {
      constructor(k, l, r) {
        super();
        this.k = k;
        this.l = l;
        this.r = r;
      }
      toString() { return "Node(" + globalThis.Predef.render(this.k) + ", " + globalThis.Predef.render(this.l) + ", " + globalThis.Predef.render(this.r) + ")"; }
    };
    this.Leaf = function Leaf(k1, e1) {
      return new Leaf.class(k1, e1);
    };
    this.Leaf.class = class Leaf extends treejoin.Tree {
      constructor(k, e) {
        super();
        this.k = k;
        this.e = e;
      }
      toString() { return "Leaf(" + globalThis.Predef.render(this.k) + ", " + globalThis.Predef.render(this.e) + ")"; }
    };
    const Empty$class = class Empty extends treejoin.Tree {
      constructor() {
        super();
      }
      toString() { return "Empty"; }
    };
    this.Empty = new Empty$class;
    this.Empty.class = Empty$class;
    lambda2 = (undefined, function () {
      let tmp;
      tmp = treejoin.testTreejoin_nofib(0);
      return runtime.safeCall(tmp.toString())
    });
    BenchmarkPrelude.benchmark(lambda2)
  }
  static isSpace(c) {
    let tmp, tmp1;
    tmp = c === " ";
    tmp1 = c === "\n";
    return tmp || tmp1
  } 
  static isDigit(c1) {
    let n, tmp, tmp1, tmp2;
    tmp = runtime.safeCall(c1.codePointAt(0));
    n = tmp;
    tmp1 = n >= 48;
    tmp2 = n <= 57;
    return tmp1 && tmp2
  } 
  static insertT(k, e, t) {
    let param0, param1, k_, k__, l_, scrut, scrut1, param01, param11, param2, k_1, l, r, scrut2, tmp, tmp1, tmp2, tmp3, tmp4;
    if (t instanceof treejoin.Node.class) {
      param01 = t.k;
      param11 = t.l;
      param2 = t.r;
      k_1 = param01;
      l = param11;
      r = param2;
      scrut2 = k <= k_1;
      if (scrut2 === true) {
        tmp = treejoin.insertT(k, e, l);
        return treejoin.Node(k_1, tmp, r)
      } else {
        tmp1 = treejoin.insertT(k, e, r);
        return treejoin.Node(k_1, l, tmp1)
      }
    } else if (t instanceof treejoin.Leaf.class) {
      param0 = t.k;
      param1 = t.e;
      k_ = param0;
      k__ = param1;
      tmp2 = treejoin.Leaf(k, e);
      l_ = tmp2;
      scrut1 = k < k_;
      if (scrut1 === true) {
        tmp3 = treejoin.Leaf(k_, k__);
        return treejoin.Node(k, l_, tmp3)
      } else {
        scrut = k > k_;
        if (scrut === true) {
          tmp4 = treejoin.Leaf(k_, k__);
          return treejoin.Node(k_, tmp4, l_)
        } else {
          throw globalThis.Error("already exist");
        }
      }
    } else if (t instanceof treejoin.Empty.class) {
      return treejoin.Leaf(k, e)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static lookupT(k1, t1) {
    let param0, param1, k_, e1, scrut, param01, param11, param2, k_1, l, r, scrut1;
    if (t1 instanceof treejoin.Node.class) {
      param01 = t1.k;
      param11 = t1.l;
      param2 = t1.r;
      k_1 = param01;
      l = param11;
      r = param2;
      scrut1 = k1 <= k_1;
      if (scrut1 === true) {
        return treejoin.lookupT(k1, l)
      } else {
        return treejoin.lookupT(k1, r)
      }
    } else if (t1 instanceof treejoin.Leaf.class) {
      param0 = t1.k;
      param1 = t1.e;
      k_ = param0;
      e1 = param1;
      scrut = k1 === k_;
      if (scrut === true) {
        return NofibPrelude.Some(e1)
      } else {
        return NofibPrelude.None
      }
    } else if (t1 instanceof treejoin.Empty.class) {
      return NofibPrelude.None
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static readInt(s) {
    return readInt_(0, s)
  } 
  static join(t11, t2, j) {
    let param0, param1, param2, k2, l, r, param01, param11, k3, first2, first1, first0, a, b, c2, scrut, param02, first21, first11, first01, d, e1, f, tmp;
    if (t11 instanceof treejoin.Empty.class) {
      return j
    } else {
      if (t2 instanceof treejoin.Empty.class) {
        return j
      } else {
        if (t11 instanceof treejoin.Leaf.class) {
          param01 = t11.k;
          param11 = t11.e;
          k3 = param01;
          if (globalThis.Array.isArray(param11) && param11.length === 3) {
            first0 = param11[0];
            first1 = param11[1];
            first2 = param11[2];
            a = first0;
            b = first1;
            c2 = first2;
            scrut = treejoin.lookupT(c2, t2);
            if (scrut instanceof NofibPrelude.None.class) {
              return j
            } else if (scrut instanceof NofibPrelude.Some.class) {
              param02 = scrut.x;
              if (globalThis.Array.isArray(param02) && param02.length === 3) {
                first01 = param02[0];
                first11 = param02[1];
                first21 = param02[2];
                d = first01;
                e1 = first11;
                f = first21;
                return treejoin.insertT(c2, [
                  a,
                  b,
                  c2,
                  d,
                  e1
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
        } else if (t11 instanceof treejoin.Node.class) {
          param0 = t11.k;
          param1 = t11.l;
          param2 = t11.r;
          k2 = param0;
          l = param1;
          r = param2;
          tmp = treejoin.join(r, t2, j);
          return treejoin.join(l, t2, tmp)
        } else {
          throw new globalThis.Error("match error");
        }
      }
    }
  } 
  static readTree(fk, s1, t3) {
    let scrut, first1, first0, f, s_, scrut1, first11, first01, g, s__, scrut2, first12, first02, h, s___, e1, k2, tmp, tmp1;
    if (s1 instanceof NofibPrelude.Nil.class) {
      return t3
    } else {
      scrut = treejoin.readInt(s1);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        f = first0;
        s_ = first1;
        scrut1 = treejoin.readInt(s_);
        if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
          first01 = scrut1[0];
          first11 = scrut1[1];
          g = first01;
          s__ = first11;
          scrut2 = treejoin.readInt(s__);
          if (globalThis.Array.isArray(scrut2) && scrut2.length === 2) {
            first02 = scrut2[0];
            first12 = scrut2[1];
            h = first02;
            s___ = first12;
            e1 = [
              f,
              g,
              h
            ];
            tmp = runtime.safeCall(fk(e1));
            k2 = tmp;
            tmp1 = treejoin.insertT(k2, e1, t3);
            return treejoin.readTree(fk, s___, tmp1)
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
  } 
  static testTreejoin_nofib(n) {
    let c11, c2, a, b, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    tmp = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/1500.1"));
    tmp1 = runtime.safeCall(tmp.toString());
    tmp2 = NofibPrelude.nofibStringToList(tmp1);
    c11 = tmp2;
    tmp3 = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/1500.2"));
    tmp4 = runtime.safeCall(tmp3.toString());
    tmp5 = NofibPrelude.nofibStringToList(tmp4);
    c2 = tmp5;
    tmp6 = lambda;
    tmp7 = treejoin.readTree(tmp6, c11, treejoin.Empty);
    a = tmp7;
    tmp8 = lambda1;
    tmp9 = treejoin.readTree(tmp8, c2, treejoin.Empty);
    b = tmp9;
    return treejoin.join(a, b, treejoin.Empty)
  }
  static toString() { return "treejoin"; }
};
let treejoin = treejoin1; export default treejoin;
