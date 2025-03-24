import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let sorting1;
sorting1 = class sorting {
  static {
    sorting1 = sorting;
    let lambda;
    const EQ$class = class EQ {
      constructor() {}
      toString() { return "EQ"; }
    };
    this.EQ = new EQ$class;
    this.EQ.class = EQ$class;
    const GT$class = class GT {
      constructor() {}
      toString() { return "GT"; }
    };
    this.GT = new GT$class;
    this.GT.class = GT$class;
    const LT$class = class LT {
      constructor() {}
      toString() { return "LT"; }
    };
    this.LT = new LT$class;
    this.LT.class = LT$class;
    this.Tree = class Tree {
      constructor() {}
      toString() { return "Tree"; }
    };
    const Tip$class = class Tip extends sorting.Tree {
      constructor() {
        super();
      }
      toString() { return "Tip"; }
    };
    this.Tip = new Tip$class;
    this.Tip.class = Tip$class;
    this.Branch = function Branch(a1, l1, r1) {
      return new Branch.class(a1, l1, r1);
    };
    this.Branch.class = class Branch extends sorting.Tree {
      constructor(a, l, r) {
        super();
        this.a = a;
        this.l = l;
        this.r = r;
      }
      toString() { return "Branch(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.l) + ", " + globalThis.Predef.render(this.r) + ")"; }
    };
    this.Tree2 = class Tree2 {
      constructor() {}
      toString() { return "Tree2"; }
    };
    const Tip2$class = class Tip2 extends sorting.Tree2 {
      constructor() {
        super();
      }
      toString() { return "Tip2"; }
    };
    this.Tip2 = new Tip2$class;
    this.Tip2.class = Tip2$class;
    this.Twig2 = function Twig2(a1) {
      return new Twig2.class(a1);
    };
    this.Twig2.class = class Twig2 extends sorting.Tree2 {
      constructor(a) {
        super();
        this.a = a;
      }
      toString() { return "Twig2(" + globalThis.Predef.render(this.a) + ")"; }
    };
    this.Branch2 = function Branch2(a1, l1, r1) {
      return new Branch2.class(a1, l1, r1);
    };
    this.Branch2.class = class Branch2 extends sorting.Tree2 {
      constructor(a, l, r) {
        super();
        this.a = a;
        this.l = l;
        this.r = r;
      }
      toString() { return "Branch2(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.l) + ", " + globalThis.Predef.render(this.r) + ")"; }
    };
    lambda = (undefined, function () {
      return sorting.testSorting_nofib(0)
    });
    BenchmarkPrelude.benchmark(lambda)
  }
  static int_of_char(c) {
    return runtime.safeCall(c.codePointAt(0))
  } 
  static compareList(xs, ys) {
    let param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3;
    if (xs instanceof NofibPrelude.Nil.class) {
      if (ys instanceof NofibPrelude.Nil.class) {
        return sorting.EQ
      } else if (ys instanceof NofibPrelude.Cons.class) {
        param01 = ys.head;
        param11 = ys.tail;
        return sorting.LT
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param0 = xs.head;
      param1 = xs.tail;
      x = param0;
      xs_ = param1;
      if (ys instanceof NofibPrelude.Nil.class) {
        return sorting.GT
      } else if (ys instanceof NofibPrelude.Cons.class) {
        param01 = ys.head;
        param11 = ys.tail;
        y = param01;
        ys_ = param11;
        tmp = sorting.int_of_char(x);
        tmp1 = sorting.int_of_char(y);
        scrut1 = tmp === tmp1;
        if (scrut1 === true) {
          return sorting.compareList(xs_, ys_)
        } else {
          tmp2 = sorting.int_of_char(x);
          tmp3 = sorting.int_of_char(y);
          scrut = tmp2 < tmp3;
          if (scrut === true) {
            return sorting.LT
          } else {
            return sorting.GT
          }
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static gtList(a, b) {
    let scrut;
    scrut = sorting.compareList(a, b);
    if (scrut instanceof sorting.GT.class) {
      return true
    } else {
      return false
    }
  } 
  static leList(a1, b1) {
    let tmp;
    tmp = sorting.gtList(a1, b1);
    return BenchmarkPrelude.not(tmp)
  } 
  static ltList(a2, b2) {
    let scrut;
    scrut = sorting.compareList(a2, b2);
    if (scrut instanceof sorting.LT.class) {
      return true
    } else {
      return false
    }
  } 
  static geList(a3, b3) {
    let tmp;
    tmp = sorting.ltList(a3, b3);
    return BenchmarkPrelude.not(tmp)
  } 
  static eqList(a4, b4) {
    let scrut;
    scrut = sorting.compareList(a4, b4);
    if (scrut instanceof sorting.EQ.class) {
      return true
    } else {
      return false
    }
  } 
  static prependToAll(sep, xs1) {
    let param0, param1, x, xs_, tmp, tmp1;
    if (xs1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xs1 instanceof NofibPrelude.Cons.class) {
      param0 = xs1.head;
      param1 = xs1.tail;
      x = param0;
      xs_ = param1;
      tmp = sorting.prependToAll(sep, xs_);
      tmp1 = NofibPrelude.Cons(x, tmp);
      return NofibPrelude.Cons(sep, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static intersperse(sep1, xs2) {
    let param0, param1, x, xs_, tmp;
    if (xs2 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xs2 instanceof NofibPrelude.Cons.class) {
      param0 = xs2.head;
      param1 = xs2.tail;
      x = param0;
      xs_ = param1;
      tmp = sorting.prependToAll(sep1, xs_);
      return NofibPrelude.Cons(x, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static lines(s) {
    let scrut, first1, first0, l, s_, tt, param0, param1, s__, tmp, lambda;
    if (s instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      lambda = (undefined, function (x) {
        return x === "\n"
      });
      scrut = NofibPrelude.break_(lambda, s);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        l = first0;
        s_ = first1;
        if (s_ instanceof NofibPrelude.Nil.class) {
          tmp = NofibPrelude.Nil;
        } else if (s_ instanceof NofibPrelude.Cons.class) {
          param0 = s_.head;
          param1 = s_.tail;
          s__ = param1;
          tmp = sorting.lines(s__);
        } else {
          throw new globalThis.Error("match error");
        }
        tt = tmp;
        return NofibPrelude.Cons(l, tt)
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  static unlines(ls) {
    let tmp, lambda;
    lambda = (undefined, function (l) {
      let tmp1;
      tmp1 = NofibPrelude.Cons("\n", NofibPrelude.Nil);
      return NofibPrelude.append(l, tmp1)
    });
    tmp = NofibPrelude.map(lambda, ls);
    return NofibPrelude.concat(tmp)
  } 
  static odd(x) {
    let tmp;
    tmp = NofibPrelude.intMod(x, 2);
    return tmp === 0
  } 
  static z_of_int(x1) {
    return runtime.safeCall(globalThis.BigInt(x1))
  } 
  static hash(str) {
    let tmp, tmp1, lambda;
    lambda = (undefined, function (acc, c1) {
      let tmp2, tmp3, tmp4, tmp5;
      tmp2 = sorting.int_of_char(c1);
      tmp3 = sorting.z_of_int(tmp2);
      tmp4 = sorting.z_of_int(31);
      tmp5 = acc * tmp4;
      return tmp3 + tmp5
    });
    tmp = lambda;
    tmp1 = sorting.z_of_int(0);
    return NofibPrelude.foldl(tmp, tmp1, str)
  } 
  static quickSort(xs3) {
    let lscomp2, lscomp1, param0, param1, x2, xs_, tmp, tmp1, tmp2, tmp3, tmp4;
    if (xs3 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xs3 instanceof NofibPrelude.Cons.class) {
      param0 = xs3.head;
      param1 = xs3.tail;
      x2 = param0;
      xs_ = param1;
      lscomp1 = function lscomp1(ls1) {
        let param01, param11, h, t, scrut, tmp5;
        if (ls1 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (ls1 instanceof NofibPrelude.Cons.class) {
          param01 = ls1.head;
          param11 = ls1.tail;
          h = param01;
          t = param11;
          scrut = sorting.leList(h, x2);
          if (scrut === true) {
            tmp5 = lscomp1(t);
            return NofibPrelude.Cons(h, tmp5)
          } else {
            return lscomp1(t)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      };
      lscomp2 = function lscomp2(ls1) {
        let param01, param11, h, t, scrut, tmp5;
        if (ls1 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (ls1 instanceof NofibPrelude.Cons.class) {
          param01 = ls1.head;
          param11 = ls1.tail;
          h = param01;
          t = param11;
          scrut = sorting.gtList(h, x2);
          if (scrut === true) {
            tmp5 = lscomp2(t);
            return NofibPrelude.Cons(h, tmp5)
          } else {
            return lscomp2(t)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      };
      tmp = lscomp1(xs_);
      tmp1 = sorting.quickSort(tmp);
      tmp2 = lscomp2(xs_);
      tmp3 = sorting.quickSort(tmp2);
      tmp4 = NofibPrelude.Cons(x2, tmp3);
      return NofibPrelude.append(tmp1, tmp4)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static select(p, x2, ts_fs) {
    let first1, first0, ts, fs1, scrut, tmp, tmp1;
    if (globalThis.Array.isArray(ts_fs) && ts_fs.length === 2) {
      first0 = ts_fs[0];
      first1 = ts_fs[1];
      ts = first0;
      fs1 = first1;
      scrut = runtime.safeCall(p(x2));
      if (scrut === true) {
        tmp = NofibPrelude.Cons(x2, ts);
        return [
          tmp,
          fs1
        ]
      } else {
        tmp1 = NofibPrelude.Cons(x2, fs1);
        return [
          ts,
          tmp1
        ]
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static partition(p1, xs4) {
    let lambda;
    lambda = (undefined, function (x3, y) {
      return sorting.select(p1, x3, y)
    });
    return NofibPrelude.foldr(lambda, [
      NofibPrelude.Nil,
      NofibPrelude.Nil
    ], xs4)
  } 
  static quickSort2(xs5) {
    let param0, param1, x3, xs_, scrut, first1, first0, lo, hi, tmp, tmp1, tmp2, lambda;
    if (xs5 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xs5 instanceof NofibPrelude.Cons.class) {
      param0 = xs5.head;
      param1 = xs5.tail;
      x3 = param0;
      xs_ = param1;
      lambda = (undefined, function (y) {
        return sorting.geList(x3, y)
      });
      scrut = sorting.partition(lambda, xs_);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        lo = first0;
        hi = first1;
        tmp = sorting.quickSort2(lo);
        tmp1 = sorting.quickSort2(hi);
        tmp2 = NofibPrelude.Cons(x3, tmp1);
        return NofibPrelude.append(tmp, tmp2)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static quickerSort(xss) {
    let split, param0, param1, x3, xs6, x4;
    if (xss instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xss instanceof NofibPrelude.Cons.class) {
      param0 = xss.head;
      param1 = xss.tail;
      x4 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Cons(x4, NofibPrelude.Nil)
      } else {
        x3 = param0;
        xs6 = param1;
        split = function split(x5, lo, hi, ys1) {
          let param01, param11, y, ys_, scrut, tmp, tmp1, tmp2, tmp3, tmp4;
          if (ys1 instanceof NofibPrelude.Nil.class) {
            tmp = sorting.quickerSort(lo);
            tmp1 = sorting.quickerSort(hi);
            tmp2 = NofibPrelude.Cons(x5, tmp1);
            return NofibPrelude.append(tmp, tmp2)
          } else if (ys1 instanceof NofibPrelude.Cons.class) {
            param01 = ys1.head;
            param11 = ys1.tail;
            y = param01;
            ys_ = param11;
            scrut = sorting.leList(y, x5);
            if (scrut === true) {
              tmp3 = NofibPrelude.Cons(y, lo);
              return split(x5, tmp3, hi, ys_)
            } else {
              tmp4 = NofibPrelude.Cons(y, hi);
              return split(x5, lo, tmp4, ys_)
            }
          } else {
            throw new globalThis.Error("match error");
          }
        };
        return split(x3, NofibPrelude.Nil, NofibPrelude.Nil, xs6)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static insertSort(xss1) {
    let trins, param0, param1, x3, xs6, tmp;
    if (xss1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xss1 instanceof NofibPrelude.Cons.class) {
      param0 = xss1.head;
      param1 = xss1.tail;
      x3 = param0;
      xs6 = param1;
      trins = function trins(rev, xs7, ys1) {
        let param01, param11, x4, xs_, param02, param12, y, ys_, scrut, xs8, y1, ys_1, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
        if (xs7 instanceof NofibPrelude.Nil.class) {
          xs8 = xs7;
          if (ys1 instanceof NofibPrelude.Cons.class) {
            param02 = ys1.head;
            param12 = ys1.tail;
            y1 = param02;
            ys_1 = param12;
            tmp1 = NofibPrelude.reverse(rev);
            tmp2 = NofibPrelude.Cons(y1, NofibPrelude.Nil);
            tmp3 = NofibPrelude.append(tmp1, tmp2);
            return trins(NofibPrelude.Nil, tmp3, ys_1)
          } else if (ys1 instanceof NofibPrelude.Nil.class) {
            tmp4 = NofibPrelude.reverse(rev);
            return NofibPrelude.append(tmp4, xs8)
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          xs8 = xs7;
          if (ys1 instanceof NofibPrelude.Nil.class) {
            tmp5 = NofibPrelude.reverse(rev);
            return NofibPrelude.append(tmp5, xs8)
          } else {
            if (xs7 instanceof NofibPrelude.Cons.class) {
              param01 = xs7.head;
              param11 = xs7.tail;
              x4 = param01;
              xs_ = param11;
              if (ys1 instanceof NofibPrelude.Cons.class) {
                param02 = ys1.head;
                param12 = ys1.tail;
                y = param02;
                ys_ = param12;
                scrut = sorting.ltList(x4, y);
                if (scrut === true) {
                  tmp6 = NofibPrelude.Cons(x4, rev);
                  tmp7 = NofibPrelude.Cons(y, ys_);
                  return trins(tmp6, xs_, tmp7)
                } else {
                  tmp8 = NofibPrelude.reverse(rev);
                  tmp9 = NofibPrelude.Cons(x4, xs_);
                  tmp10 = NofibPrelude.Cons(y, tmp9);
                  tmp11 = NofibPrelude.append(tmp8, tmp10);
                  return trins(NofibPrelude.Nil, tmp11, ys_)
                }
              } else {
                throw new globalThis.Error("match error");
              }
            } else {
              throw new globalThis.Error("match error");
            }
          }
        }
      };
      tmp = NofibPrelude.Cons(x3, NofibPrelude.Nil);
      return trins(NofibPrelude.Nil, tmp, xs6)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static treeSort(param) {
    let mkTree, readTree, tmp;
    mkTree = function mkTree(innerparam) {
      let to_tree;
      to_tree = function to_tree(x3, t) {
        let param0, param1, param2, y, l, r, scrut, tmp1, tmp2;
        if (t instanceof sorting.Tip.class) {
          return sorting.Branch(x3, sorting.Tip, sorting.Tip)
        } else if (t instanceof sorting.Branch.class) {
          param0 = t.a;
          param1 = t.l;
          param2 = t.r;
          y = param0;
          l = param1;
          r = param2;
          scrut = sorting.leList(x3, y);
          if (scrut === true) {
            tmp1 = to_tree(x3, l);
            return sorting.Branch(y, tmp1, r)
          } else {
            tmp2 = to_tree(x3, r);
            return sorting.Branch(y, l, tmp2)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      };
      return NofibPrelude.foldr(to_tree, sorting.Tip, innerparam)
    };
    readTree = function readTree(t) {
      let param0, param1, param2, x3, l, r, tmp1, tmp2, tmp3;
      if (t instanceof sorting.Tip.class) {
        return NofibPrelude.Nil
      } else if (t instanceof sorting.Branch.class) {
        param0 = t.a;
        param1 = t.l;
        param2 = t.r;
        x3 = param0;
        l = param1;
        r = param2;
        tmp1 = readTree(l);
        tmp2 = readTree(r);
        tmp3 = NofibPrelude.Cons(x3, tmp2);
        return NofibPrelude.append(tmp1, tmp3)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = mkTree(param);
    return readTree(tmp)
  } 
  static treeSort2(param1) {
    let mkTree, readTree, tmp;
    mkTree = function mkTree(innerparam) {
      let to_tree;
      to_tree = function to_tree(x3, t) {
        let param0, param11, param2, y, l, r, scrut, param01, y1, scrut1, tmp1, tmp2, tmp3, tmp4;
        if (t instanceof sorting.Tip2.class) {
          return sorting.Twig2(x3)
        } else if (t instanceof sorting.Twig2.class) {
          param01 = t.a;
          y1 = param01;
          scrut1 = sorting.leList(x3, y1);
          if (scrut1 === true) {
            tmp1 = sorting.Twig2(x3);
            return sorting.Branch2(y1, tmp1, sorting.Tip2)
          } else {
            tmp2 = sorting.Twig2(x3);
            return sorting.Branch2(y1, sorting.Tip2, tmp2)
          }
        } else if (t instanceof sorting.Branch2.class) {
          param0 = t.a;
          param11 = t.l;
          param2 = t.r;
          y = param0;
          l = param11;
          r = param2;
          scrut = sorting.leList(x3, y);
          if (scrut === true) {
            tmp3 = to_tree(x3, l);
            return sorting.Branch2(y, tmp3, r)
          } else {
            tmp4 = to_tree(x3, r);
            return sorting.Branch2(y, l, tmp4)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      };
      return NofibPrelude.foldr(to_tree, sorting.Tip2, innerparam)
    };
    readTree = function readTree(t) {
      let param0, param11, param2, x3, l, r, param01, x4, tmp1, tmp2, tmp3;
      if (t instanceof sorting.Tip2.class) {
        return NofibPrelude.Nil
      } else if (t instanceof sorting.Twig2.class) {
        param01 = t.a;
        x4 = param01;
        return NofibPrelude.Cons(x4, NofibPrelude.Nil)
      } else if (t instanceof sorting.Branch2.class) {
        param0 = t.a;
        param11 = t.l;
        param2 = t.r;
        x3 = param0;
        l = param11;
        r = param2;
        tmp1 = readTree(l);
        tmp2 = readTree(r);
        tmp3 = NofibPrelude.Cons(x3, tmp2);
        return NofibPrelude.append(tmp1, tmp3)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = mkTree(param1);
    return readTree(tmp)
  } 
  static heapSort(xs6) {
    let to_heap, clear, heap, mix, tmp;
    heap = function heap(k, xs7) {
      let param0, param11, x3, xs_, tmp1, tmp2;
      if (xs7 instanceof NofibPrelude.Nil.class) {
        return sorting.Tip
      } else if (xs7 instanceof NofibPrelude.Cons.class) {
        param0 = xs7.head;
        param11 = xs7.tail;
        x3 = param0;
        xs_ = param11;
        tmp1 = k + 1;
        tmp2 = heap(tmp1, xs_);
        return to_heap(k, x3, tmp2)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    to_heap = function to_heap(k, x3, t) {
      let param0, param11, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
      if (t instanceof sorting.Tip.class) {
        return sorting.Branch(x3, sorting.Tip, sorting.Tip)
      } else if (t instanceof sorting.Branch.class) {
        param0 = t.a;
        param11 = t.l;
        param2 = t.r;
        y = param0;
        l = param11;
        r = param2;
        scrut2 = sorting.leList(x3, y);
        if (scrut2 === true) {
          scrut3 = sorting.odd(k);
          if (scrut3 === true) {
            tmp1 = NofibPrelude.intDiv(k, 2);
            tmp2 = to_heap(tmp1, y, l);
            return sorting.Branch(x3, tmp2, r)
          } else {
            scrut1 = sorting.leList(x3, y);
            if (scrut1 === true) {
              tmp3 = NofibPrelude.intDiv(k, 2);
              tmp4 = to_heap(tmp3, y, r);
              return sorting.Branch(x3, l, tmp4)
            } else {
              scrut = sorting.odd(k);
              if (scrut === true) {
                tmp5 = NofibPrelude.intDiv(k, 2);
                tmp6 = to_heap(tmp5, x3, l);
                return sorting.Branch(y, tmp6, r)
              } else {
                tmp7 = NofibPrelude.intDiv(k, 2);
                tmp8 = to_heap(tmp7, x3, r);
                return sorting.Branch(y, l, tmp8)
              }
            }
          }
        } else {
          scrut1 = sorting.leList(x3, y);
          if (scrut1 === true) {
            tmp9 = NofibPrelude.intDiv(k, 2);
            tmp10 = to_heap(tmp9, y, r);
            return sorting.Branch(x3, l, tmp10)
          } else {
            scrut = sorting.odd(k);
            if (scrut === true) {
              tmp11 = NofibPrelude.intDiv(k, 2);
              tmp12 = to_heap(tmp11, x3, l);
              return sorting.Branch(y, tmp12, r)
            } else {
              tmp13 = NofibPrelude.intDiv(k, 2);
              tmp14 = to_heap(tmp13, x3, r);
              return sorting.Branch(y, l, tmp14)
            }
          }
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    clear = function clear(t) {
      let param0, param11, param2, x3, l, r, tmp1, tmp2;
      if (t instanceof sorting.Tip.class) {
        return NofibPrelude.Nil
      } else if (t instanceof sorting.Branch.class) {
        param0 = t.a;
        param11 = t.l;
        param2 = t.r;
        x3 = param0;
        l = param11;
        r = param2;
        tmp1 = mix(l, r);
        tmp2 = clear(tmp1);
        return NofibPrelude.Cons(x3, tmp2)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    mix = function mix(l, r) {
      let param0, param11, param2, x3, l1, r1, param01, param12, param21, y, l2, r2, scrut, tmp1, tmp2, tmp3, tmp4;
      if (l instanceof sorting.Tip.class) {
        return r
      } else {
        if (r instanceof sorting.Tip.class) {
          return l
        } else {
          if (l instanceof sorting.Branch.class) {
            param0 = l.a;
            param11 = l.l;
            param2 = l.r;
            x3 = param0;
            l1 = param11;
            r1 = param2;
            if (r instanceof sorting.Branch.class) {
              param01 = r.a;
              param12 = r.l;
              param21 = r.r;
              y = param01;
              l2 = param12;
              r2 = param21;
              scrut = sorting.leList(x3, y);
              if (scrut === true) {
                tmp1 = mix(l1, r1);
                tmp2 = sorting.Branch(y, l2, r2);
                return sorting.Branch(x3, tmp1, tmp2)
              } else {
                tmp3 = sorting.Branch(x3, l1, r1);
                tmp4 = mix(l2, r2);
                return sorting.Branch(y, tmp3, tmp4)
              }
            } else {
              throw new globalThis.Error("match error");
            }
          } else {
            throw new globalThis.Error("match error");
          }
        }
      }
    };
    tmp = heap(0, xs6);
    return clear(tmp)
  } 
  static mergeSort(param2) {
    let runsplit, merge, merge_lists, tmp;
    runsplit = function runsplit(run, xs7) {
      let param0, param11, r, rs, param01, param12, x3, xs_, rs1, scrut, scrut1, scrut2, x4, xs_1, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13;
      if (run instanceof NofibPrelude.Nil.class) {
        if (xs7 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (xs7 instanceof NofibPrelude.Cons.class) {
          param01 = xs7.head;
          param12 = xs7.tail;
          x4 = param01;
          xs_1 = param12;
          tmp1 = NofibPrelude.Cons(x4, NofibPrelude.Nil);
          return runsplit(tmp1, xs_1)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        if (xs7 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Cons(run, NofibPrelude.Nil)
        } else {
          if (run instanceof NofibPrelude.Cons.class) {
            param0 = run.head;
            param11 = run.tail;
            r = param0;
            rs = param11;
            if (xs7 instanceof NofibPrelude.Cons.class) {
              param01 = xs7.head;
              param12 = xs7.tail;
              x3 = param01;
              xs_ = param12;
              if (rs instanceof NofibPrelude.Nil.class) {
                scrut2 = sorting.gtList(x3, r);
                if (scrut2 === true) {
                  tmp2 = NofibPrelude.Cons(x3, NofibPrelude.Nil);
                  tmp3 = NofibPrelude.Cons(r, tmp2);
                  return runsplit(tmp3, xs_)
                } else {
                  scrut1 = sorting.leList(x3, r);
                  if (scrut1 === true) {
                    tmp4 = NofibPrelude.Cons(r, rs);
                    tmp5 = NofibPrelude.Cons(x3, tmp4);
                    return runsplit(tmp5, xs_)
                  } else {
                    tmp6 = NofibPrelude.Cons(r, rs);
                    tmp7 = NofibPrelude.Cons(x3, NofibPrelude.Nil);
                    tmp8 = runsplit(tmp7, xs_);
                    return NofibPrelude.Cons(tmp6, tmp8)
                  }
                }
              } else {
                rs1 = rs;
                scrut = sorting.leList(x3, r);
                if (scrut === true) {
                  tmp9 = NofibPrelude.Cons(r, rs1);
                  tmp10 = NofibPrelude.Cons(x3, tmp9);
                  return runsplit(tmp10, xs_)
                } else {
                  tmp11 = NofibPrelude.Cons(r, rs1);
                  tmp12 = NofibPrelude.Cons(x3, NofibPrelude.Nil);
                  tmp13 = runsplit(tmp12, xs_);
                  return NofibPrelude.Cons(tmp11, tmp13)
                }
              }
            } else {
              throw new globalThis.Error("match error");
            }
          } else {
            throw new globalThis.Error("match error");
          }
        }
      }
    };
    merge_lists = function merge_lists(xs7) {
      let param0, param11, x3, xs_, tmp1;
      if (xs7 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (xs7 instanceof NofibPrelude.Cons.class) {
        param0 = xs7.head;
        param11 = xs7.tail;
        x3 = param0;
        xs_ = param11;
        tmp1 = merge_lists(xs_);
        return merge(x3, tmp1)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    merge = function merge(xs7, ys1) {
      let param0, param11, x3, xs_, param01, param12, y, ys_, scrut, scrut1, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
      if (xs7 instanceof NofibPrelude.Nil.class) {
        return ys1
      } else {
        if (ys1 instanceof NofibPrelude.Nil.class) {
          return xs7
        } else {
          if (xs7 instanceof NofibPrelude.Cons.class) {
            param0 = xs7.head;
            param11 = xs7.tail;
            x3 = param0;
            xs_ = param11;
            if (ys1 instanceof NofibPrelude.Cons.class) {
              param01 = ys1.head;
              param12 = ys1.tail;
              y = param01;
              ys_ = param12;
              scrut1 = sorting.eqList(x3, y);
              if (scrut1 === true) {
                tmp1 = merge(xs_, ys_);
                tmp2 = NofibPrelude.Cons(y, tmp1);
                return NofibPrelude.Cons(x3, tmp2)
              } else {
                scrut = sorting.ltList(x3, y);
                if (scrut === true) {
                  tmp3 = NofibPrelude.Cons(y, ys_);
                  tmp4 = merge(xs_, tmp3);
                  return NofibPrelude.Cons(x3, tmp4)
                } else {
                  tmp5 = NofibPrelude.Cons(x3, xs_);
                  tmp6 = merge(tmp5, ys_);
                  return NofibPrelude.Cons(y, tmp6)
                }
              }
            } else {
              throw new globalThis.Error("match error");
            }
          } else {
            throw new globalThis.Error("match error");
          }
        }
      }
    };
    tmp = runsplit(NofibPrelude.Nil, param2);
    return merge_lists(tmp)
  } 
  static mangle(inpt) {
    let sort, tmp, tmp1;
    sort = function sort(param3) {
      let tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, lambda, lambda1;
      tmp2 = NofibPrelude.Cons(sorting.treeSort2, NofibPrelude.Nil);
      tmp3 = NofibPrelude.Cons(sorting.treeSort, tmp2);
      tmp4 = NofibPrelude.Cons(sorting.quickerSort, tmp3);
      tmp5 = NofibPrelude.Cons(sorting.quickSort2, tmp4);
      tmp6 = NofibPrelude.Cons(sorting.quickSort, tmp5);
      tmp7 = NofibPrelude.Cons(sorting.mergeSort, tmp6);
      tmp8 = NofibPrelude.Cons(sorting.insertSort, tmp7);
      tmp9 = NofibPrelude.Cons(sorting.heapSort, tmp8);
      tmp10 = sorting.intersperse(NofibPrelude.reverse, tmp9);
      lambda = (undefined, function (f, g) {
        let lambda2;
        lambda2 = (undefined, function (x3) {
          let tmp12;
          tmp12 = runtime.safeCall(g(x3));
          return runtime.safeCall(f(tmp12))
        });
        return lambda2
      });
      lambda1 = (undefined, function (x3) {
        return x3
      });
      tmp11 = NofibPrelude.foldr(lambda, lambda1, tmp10);
      return runtime.safeCall(tmp11(param3))
    };
    tmp = sorting.lines(inpt);
    tmp1 = sort(tmp);
    return sorting.unlines(tmp1)
  } 
  static testSorting_nofib(d) {
    let f, tmp, tmp1, tmp2, tmp3;
    tmp = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/Main.hs"));
    tmp1 = runtime.safeCall(tmp.toString());
    tmp2 = NofibPrelude.nofibStringToList(tmp1);
    f = tmp2;
    tmp3 = sorting.mangle(f);
    return sorting.hash(tmp3)
  }
  static toString() { return "sorting"; }
};
let sorting = sorting1; export default sorting;
