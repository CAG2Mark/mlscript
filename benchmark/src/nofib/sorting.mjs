import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let lscomp2, lscomp1, split, trins, to_tree, mkTree, readTree, to_tree1, mkTree1, readTree1, to_heap, clear, heap, mix, runsplit, merge, merge_lists, sort, sorting1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lscomp2$, lscomp1$, lambda$, lambda$1, lambda$2;
lambda$2 = function lambda$(f, g, x) {
  let tmp;
  tmp = runtime.safeCall(g(x));
  return runtime.safeCall(f(tmp))
};
lambda7 = (undefined, function (f, g) {
  return (x) => {
    return lambda$2(f, g, x)
  }
});
lambda5 = (undefined, function (f, g) {
  return runtime.safeCall(lambda7(f, g))
});
lambda6 = (undefined, function (x) {
  return x
});
sort = function sort(param) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
  tmp = NofibPrelude.Cons(sorting1.treeSort2, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(sorting1.treeSort, tmp);
  tmp2 = NofibPrelude.Cons(sorting1.quickerSort, tmp1);
  tmp3 = NofibPrelude.Cons(sorting1.quickSort2, tmp2);
  tmp4 = NofibPrelude.Cons(sorting1.quickSort, tmp3);
  tmp5 = NofibPrelude.Cons(sorting1.mergeSort, tmp4);
  tmp6 = NofibPrelude.Cons(sorting1.insertSort, tmp5);
  tmp7 = NofibPrelude.Cons(sorting1.heapSort, tmp6);
  tmp8 = sorting1.intersperse(NofibPrelude.reverse, tmp7);
  tmp9 = NofibPrelude.foldr(lambda5, lambda6, tmp8);
  return runtime.safeCall(tmp9(param))
};
runsplit = function runsplit(run, xs) {
  let param0, param1, r, rs, param01, param11, x, xs_, rs1, scrut, scrut1, scrut2, x1, xs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12;
  if (run instanceof NofibPrelude.Nil.class) {
    if (xs instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param01 = xs.head;
      param11 = xs.tail;
      x1 = param01;
      xs_1 = param11;
      tmp = NofibPrelude.Cons(x1, NofibPrelude.Nil);
      return runsplit(tmp, xs_1)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    if (xs instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(run, NofibPrelude.Nil)
    } else {
      if (run instanceof NofibPrelude.Cons.class) {
        param0 = run.head;
        param1 = run.tail;
        r = param0;
        rs = param1;
        if (xs instanceof NofibPrelude.Cons.class) {
          param01 = xs.head;
          param11 = xs.tail;
          x = param01;
          xs_ = param11;
          if (rs instanceof NofibPrelude.Nil.class) {
            scrut2 = sorting1.gtList(x, r);
            if (scrut2 === true) {
              tmp1 = NofibPrelude.Cons(x, NofibPrelude.Nil);
              tmp2 = NofibPrelude.Cons(r, tmp1);
              return runsplit(tmp2, xs_)
            } else {
              scrut1 = sorting1.leList(x, r);
              if (scrut1 === true) {
                tmp3 = NofibPrelude.Cons(r, rs);
                tmp4 = NofibPrelude.Cons(x, tmp3);
                return runsplit(tmp4, xs_)
              } else {
                tmp5 = NofibPrelude.Cons(r, rs);
                tmp6 = NofibPrelude.Cons(x, NofibPrelude.Nil);
                tmp7 = runsplit(tmp6, xs_);
                return NofibPrelude.Cons(tmp5, tmp7)
              }
            }
          } else {
            rs1 = rs;
            scrut = sorting1.leList(x, r);
            if (scrut === true) {
              tmp8 = NofibPrelude.Cons(r, rs1);
              tmp9 = NofibPrelude.Cons(x, tmp8);
              return runsplit(tmp9, xs_)
            } else {
              tmp10 = NofibPrelude.Cons(r, rs1);
              tmp11 = NofibPrelude.Cons(x, NofibPrelude.Nil);
              tmp12 = runsplit(tmp11, xs_);
              return NofibPrelude.Cons(tmp10, tmp12)
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
merge_lists = function merge_lists(xs) {
  let param0, param1, x, xs_, tmp;
  if (xs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs_ = param1;
    tmp = merge_lists(xs_);
    return merge(x, tmp)
  } else {
    throw new globalThis.Error("match error");
  }
};
merge = function merge(xs, ys) {
  let param0, param1, x, xs_, param01, param11, y, ys_, scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
  if (xs instanceof NofibPrelude.Nil.class) {
    return ys
  } else {
    if (ys instanceof NofibPrelude.Nil.class) {
      return xs
    } else {
      if (xs instanceof NofibPrelude.Cons.class) {
        param0 = xs.head;
        param1 = xs.tail;
        x = param0;
        xs_ = param1;
        if (ys instanceof NofibPrelude.Cons.class) {
          param01 = ys.head;
          param11 = ys.tail;
          y = param01;
          ys_ = param11;
          scrut1 = sorting1.eqList(x, y);
          if (scrut1 === true) {
            tmp = merge(xs_, ys_);
            tmp1 = NofibPrelude.Cons(y, tmp);
            return NofibPrelude.Cons(x, tmp1)
          } else {
            scrut = sorting1.ltList(x, y);
            if (scrut === true) {
              tmp2 = NofibPrelude.Cons(y, ys_);
              tmp3 = merge(xs_, tmp2);
              return NofibPrelude.Cons(x, tmp3)
            } else {
              tmp4 = NofibPrelude.Cons(x, xs_);
              tmp5 = merge(tmp4, ys_);
              return NofibPrelude.Cons(y, tmp5)
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
heap = function heap(k, xs) {
  let param0, param1, x, xs_, tmp, tmp1;
  if (xs instanceof NofibPrelude.Nil.class) {
    return sorting1.Tip
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs_ = param1;
    tmp = k + 1;
    tmp1 = heap(tmp, xs_);
    return to_heap(k, x, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
to_heap = function to_heap(k, x, t) {
  let param0, param1, param2, y, l, r, scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13;
  if (t instanceof sorting1.Tip.class) {
    return sorting1.Branch(x, sorting1.Tip, sorting1.Tip)
  } else if (t instanceof sorting1.Branch.class) {
    param0 = t.a;
    param1 = t.l;
    param2 = t.r;
    y = param0;
    l = param1;
    r = param2;
    scrut2 = sorting1.leList(x, y);
    if (scrut2 === true) {
      scrut3 = sorting1.odd(k);
      if (scrut3 === true) {
        tmp = NofibPrelude.intDiv(k, 2);
        tmp1 = to_heap(tmp, y, l);
        return sorting1.Branch(x, tmp1, r)
      } else {
        scrut1 = sorting1.leList(x, y);
        if (scrut1 === true) {
          tmp2 = NofibPrelude.intDiv(k, 2);
          tmp3 = to_heap(tmp2, y, r);
          return sorting1.Branch(x, l, tmp3)
        } else {
          scrut = sorting1.odd(k);
          if (scrut === true) {
            tmp4 = NofibPrelude.intDiv(k, 2);
            tmp5 = to_heap(tmp4, x, l);
            return sorting1.Branch(y, tmp5, r)
          } else {
            tmp6 = NofibPrelude.intDiv(k, 2);
            tmp7 = to_heap(tmp6, x, r);
            return sorting1.Branch(y, l, tmp7)
          }
        }
      }
    } else {
      scrut1 = sorting1.leList(x, y);
      if (scrut1 === true) {
        tmp8 = NofibPrelude.intDiv(k, 2);
        tmp9 = to_heap(tmp8, y, r);
        return sorting1.Branch(x, l, tmp9)
      } else {
        scrut = sorting1.odd(k);
        if (scrut === true) {
          tmp10 = NofibPrelude.intDiv(k, 2);
          tmp11 = to_heap(tmp10, x, l);
          return sorting1.Branch(y, tmp11, r)
        } else {
          tmp12 = NofibPrelude.intDiv(k, 2);
          tmp13 = to_heap(tmp12, x, r);
          return sorting1.Branch(y, l, tmp13)
        }
      }
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
clear = function clear(t) {
  let param0, param1, param2, x, l, r, tmp, tmp1;
  if (t instanceof sorting1.Tip.class) {
    return NofibPrelude.Nil
  } else if (t instanceof sorting1.Branch.class) {
    param0 = t.a;
    param1 = t.l;
    param2 = t.r;
    x = param0;
    l = param1;
    r = param2;
    tmp = mix(l, r);
    tmp1 = clear(tmp);
    return NofibPrelude.Cons(x, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
mix = function mix(l, r) {
  let param0, param1, param2, x, l1, r1, param01, param11, param21, y, l2, r2, scrut, tmp, tmp1, tmp2, tmp3;
  if (l instanceof sorting1.Tip.class) {
    return r
  } else {
    if (r instanceof sorting1.Tip.class) {
      return l
    } else {
      if (l instanceof sorting1.Branch.class) {
        param0 = l.a;
        param1 = l.l;
        param2 = l.r;
        x = param0;
        l1 = param1;
        r1 = param2;
        if (r instanceof sorting1.Branch.class) {
          param01 = r.a;
          param11 = r.l;
          param21 = r.r;
          y = param01;
          l2 = param11;
          r2 = param21;
          scrut = sorting1.leList(x, y);
          if (scrut === true) {
            tmp = mix(l1, r1);
            tmp1 = sorting1.Branch(y, l2, r2);
            return sorting1.Branch(x, tmp, tmp1)
          } else {
            tmp2 = sorting1.Branch(x, l1, r1);
            tmp3 = mix(l2, r2);
            return sorting1.Branch(y, tmp2, tmp3)
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
to_tree1 = function to_tree(x, t) {
  let param0, param1, param2, y, l, r, scrut, param01, y1, scrut1, tmp, tmp1, tmp2, tmp3;
  if (t instanceof sorting1.Tip2.class) {
    return sorting1.Twig2(x)
  } else if (t instanceof sorting1.Twig2.class) {
    param01 = t.a;
    y1 = param01;
    scrut1 = sorting1.leList(x, y1);
    if (scrut1 === true) {
      tmp = sorting1.Twig2(x);
      return sorting1.Branch2(y1, tmp, sorting1.Tip2)
    } else {
      tmp1 = sorting1.Twig2(x);
      return sorting1.Branch2(y1, sorting1.Tip2, tmp1)
    }
  } else if (t instanceof sorting1.Branch2.class) {
    param0 = t.a;
    param1 = t.l;
    param2 = t.r;
    y = param0;
    l = param1;
    r = param2;
    scrut = sorting1.leList(x, y);
    if (scrut === true) {
      tmp2 = to_tree1(x, l);
      return sorting1.Branch2(y, tmp2, r)
    } else {
      tmp3 = to_tree1(x, r);
      return sorting1.Branch2(y, l, tmp3)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
mkTree1 = function mkTree(innerparam) {
  return NofibPrelude.foldr(to_tree1, sorting1.Tip2, innerparam)
};
readTree1 = function readTree(t) {
  let param0, param1, param2, x, l, r, param01, x1, tmp, tmp1, tmp2;
  if (t instanceof sorting1.Tip2.class) {
    return NofibPrelude.Nil
  } else if (t instanceof sorting1.Twig2.class) {
    param01 = t.a;
    x1 = param01;
    return NofibPrelude.Cons(x1, NofibPrelude.Nil)
  } else if (t instanceof sorting1.Branch2.class) {
    param0 = t.a;
    param1 = t.l;
    param2 = t.r;
    x = param0;
    l = param1;
    r = param2;
    tmp = readTree1(l);
    tmp1 = readTree1(r);
    tmp2 = NofibPrelude.Cons(x, tmp1);
    return NofibPrelude.append(tmp, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
to_tree = function to_tree(x, t) {
  let param0, param1, param2, y, l, r, scrut, tmp, tmp1;
  if (t instanceof sorting1.Tip.class) {
    return sorting1.Branch(x, sorting1.Tip, sorting1.Tip)
  } else if (t instanceof sorting1.Branch.class) {
    param0 = t.a;
    param1 = t.l;
    param2 = t.r;
    y = param0;
    l = param1;
    r = param2;
    scrut = sorting1.leList(x, y);
    if (scrut === true) {
      tmp = to_tree(x, l);
      return sorting1.Branch(y, tmp, r)
    } else {
      tmp1 = to_tree(x, r);
      return sorting1.Branch(y, l, tmp1)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
mkTree = function mkTree(innerparam) {
  return NofibPrelude.foldr(to_tree, sorting1.Tip, innerparam)
};
readTree = function readTree(t) {
  let param0, param1, param2, x, l, r, tmp, tmp1, tmp2;
  if (t instanceof sorting1.Tip.class) {
    return NofibPrelude.Nil
  } else if (t instanceof sorting1.Branch.class) {
    param0 = t.a;
    param1 = t.l;
    param2 = t.r;
    x = param0;
    l = param1;
    r = param2;
    tmp = readTree(l);
    tmp1 = readTree(r);
    tmp2 = NofibPrelude.Cons(x, tmp1);
    return NofibPrelude.append(tmp, tmp2)
  } else {
    throw new globalThis.Error("match error");
  }
};
trins = function trins(rev, xs, ys) {
  let param0, param1, x, xs_, param01, param11, y, ys_, scrut, xs1, y1, ys_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10;
  if (xs instanceof NofibPrelude.Nil.class) {
    xs1 = xs;
    if (ys instanceof NofibPrelude.Cons.class) {
      param01 = ys.head;
      param11 = ys.tail;
      y1 = param01;
      ys_1 = param11;
      tmp = NofibPrelude.reverse(rev);
      tmp1 = NofibPrelude.Cons(y1, NofibPrelude.Nil);
      tmp2 = NofibPrelude.append(tmp, tmp1);
      return trins(NofibPrelude.Nil, tmp2, ys_1)
    } else if (ys instanceof NofibPrelude.Nil.class) {
      tmp3 = NofibPrelude.reverse(rev);
      return NofibPrelude.append(tmp3, xs1)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    xs1 = xs;
    if (ys instanceof NofibPrelude.Nil.class) {
      tmp4 = NofibPrelude.reverse(rev);
      return NofibPrelude.append(tmp4, xs1)
    } else {
      if (xs instanceof NofibPrelude.Cons.class) {
        param0 = xs.head;
        param1 = xs.tail;
        x = param0;
        xs_ = param1;
        if (ys instanceof NofibPrelude.Cons.class) {
          param01 = ys.head;
          param11 = ys.tail;
          y = param01;
          ys_ = param11;
          scrut = sorting1.ltList(x, y);
          if (scrut === true) {
            tmp5 = NofibPrelude.Cons(x, rev);
            tmp6 = NofibPrelude.Cons(y, ys_);
            return trins(tmp5, xs_, tmp6)
          } else {
            tmp7 = NofibPrelude.reverse(rev);
            tmp8 = NofibPrelude.Cons(x, xs_);
            tmp9 = NofibPrelude.Cons(y, tmp8);
            tmp10 = NofibPrelude.append(tmp7, tmp9);
            return trins(NofibPrelude.Nil, tmp10, ys_)
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
split = function split(x, lo, hi, ys) {
  let param0, param1, y, ys_, scrut, tmp, tmp1, tmp2, tmp3, tmp4;
  if (ys instanceof NofibPrelude.Nil.class) {
    tmp = sorting1.quickerSort(lo);
    tmp1 = sorting1.quickerSort(hi);
    tmp2 = NofibPrelude.Cons(x, tmp1);
    return NofibPrelude.append(tmp, tmp2)
  } else if (ys instanceof NofibPrelude.Cons.class) {
    param0 = ys.head;
    param1 = ys.tail;
    y = param0;
    ys_ = param1;
    scrut = sorting1.leList(y, x);
    if (scrut === true) {
      tmp3 = NofibPrelude.Cons(y, lo);
      return split(x, tmp3, hi, ys_)
    } else {
      tmp4 = NofibPrelude.Cons(y, hi);
      return split(x, lo, tmp4, ys_)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$1 = function lambda$(x, y) {
  return sorting1.geList(x, y)
};
lambda4 = (undefined, function (x) {
  return (y) => {
    return lambda$1(x, y)
  }
});
lambda$ = function lambda$(p, x, y) {
  return sorting1.select(p, x, y)
};
lambda3 = (undefined, function (p) {
  return (x, y) => {
    return lambda$(p, x, y)
  }
});
lscomp1$ = function lscomp1$(x, ls) {
  let param0, param1, h, t, scrut, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    scrut = sorting1.leList(h, x);
    if (scrut === true) {
      tmp = lscomp1$(x, t);
      return NofibPrelude.Cons(h, tmp)
    } else {
      return lscomp1$(x, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp1 = function lscomp1(x) {
  return (ls) => {
    return lscomp1$(x, ls)
  }
};
lscomp2$ = function lscomp2$(x, ls) {
  let param0, param1, h, t, scrut, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    scrut = sorting1.gtList(h, x);
    if (scrut === true) {
      tmp = lscomp2$(x, t);
      return NofibPrelude.Cons(h, tmp)
    } else {
      return lscomp2$(x, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp2 = function lscomp2(x) {
  return (ls) => {
    return lscomp2$(x, ls)
  }
};
lambda2 = (undefined, function (acc, c) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = sorting1.int_of_char(c);
  tmp1 = sorting1.z_of_int(tmp);
  tmp2 = sorting1.z_of_int(31);
  tmp3 = acc * tmp2;
  return tmp1 + tmp3
});
lambda1 = (undefined, function (l) {
  let tmp;
  tmp = NofibPrelude.Cons("\n", NofibPrelude.Nil);
  return NofibPrelude.append(l, tmp)
});
lambda = (undefined, function (x) {
  return x === "\n"
});
sorting1 = class sorting {
  static {
    sorting1 = sorting;
    let lambda8;
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
    lambda8 = (undefined, function () {
      return sorting.testSorting_nofib(0)
    });
    BenchmarkPrelude.benchmark(lambda8)
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
    let scrut, first1, first0, l, s_, tt, param0, param1, s__, tmp;
    if (s instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
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
    let tmp;
    tmp = NofibPrelude.map(lambda1, ls);
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
    let tmp, tmp1;
    tmp = lambda2;
    tmp1 = sorting.z_of_int(0);
    return NofibPrelude.foldl(tmp, tmp1, str)
  } 
  static quickSort(xs3) {
    let param0, param1, x2, xs_, tmp, tmp1, tmp2, tmp3, tmp4;
    if (xs3 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xs3 instanceof NofibPrelude.Cons.class) {
      param0 = xs3.head;
      param1 = xs3.tail;
      x2 = param0;
      xs_ = param1;
      tmp = lscomp1$(x2, xs_);
      tmp1 = sorting.quickSort(tmp);
      tmp2 = lscomp2$(x2, xs_);
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
    let lambda$this;
    lambda$this = runtime.safeCall(lambda3(p1));
    return NofibPrelude.foldr(lambda$this, [
      NofibPrelude.Nil,
      NofibPrelude.Nil
    ], xs4)
  } 
  static quickSort2(xs5) {
    let param0, param1, x3, xs_, scrut, first1, first0, lo, hi, tmp, tmp1, tmp2, lambda$this;
    if (xs5 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xs5 instanceof NofibPrelude.Cons.class) {
      param0 = xs5.head;
      param1 = xs5.tail;
      x3 = param0;
      xs_ = param1;
      lambda$this = runtime.safeCall(lambda4(x3));
      scrut = sorting.partition(lambda$this, xs_);
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
    let param0, param1, x3, xs6, x4;
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
        return split(x3, NofibPrelude.Nil, NofibPrelude.Nil, xs6)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static insertSort(xss1) {
    let param0, param1, x3, xs6, tmp;
    if (xss1 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xss1 instanceof NofibPrelude.Cons.class) {
      param0 = xss1.head;
      param1 = xss1.tail;
      x3 = param0;
      xs6 = param1;
      tmp = NofibPrelude.Cons(x3, NofibPrelude.Nil);
      return trins(NofibPrelude.Nil, tmp, xs6)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static treeSort(param) {
    let tmp;
    tmp = mkTree(param);
    return readTree(tmp)
  } 
  static treeSort2(param1) {
    let tmp;
    tmp = mkTree1(param1);
    return readTree1(tmp)
  } 
  static heapSort(xs6) {
    let tmp;
    tmp = heap(0, xs6);
    return clear(tmp)
  } 
  static mergeSort(param2) {
    let tmp;
    tmp = runsplit(NofibPrelude.Nil, param2);
    return merge_lists(tmp)
  } 
  static mangle(inpt) {
    let tmp, tmp1;
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
