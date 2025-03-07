import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let dfs, testScc_nofib, stronglyConnComp, lambda;
dfs = function dfs(r, vsns, xs) {
  let first1, first0, vs, ns, param0, param1, x, xs1, scrut, first11, first01, vs1, ns1, scrut1, tmp, tmp1, tmp2, tmp3;
  if (globalThis.Array.isArray(vsns) && vsns.length === 2) {
    first0 = vsns[0];
    first1 = vsns[1];
    vs = first0;
    ns = first1;
    if (xs instanceof NofibPrelude.Nil.class) {
      return [
        vs,
        ns
      ]
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param0 = xs.head;
      param1 = xs.tail;
      x = param0;
      xs1 = param1;
      scrut1 = NofibPrelude.inList(x, vs);
      if (scrut1 === true) {
        return dfs(r, [
          vs,
          ns
        ], xs1)
      } else {
        tmp = NofibPrelude.Cons(x, vs);
        tmp1 = runtime.safeCall(r(x));
        scrut = dfs(r, [
          tmp,
          NofibPrelude.Nil
        ], tmp1);
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first01 = scrut[0];
          first11 = scrut[1];
          vs1 = first01;
          ns1 = first11;
          tmp2 = NofibPrelude.Cons(x, ns1);
          tmp3 = NofibPrelude.append(tmp2, ns);
          return dfs(r, [
            vs1,
            tmp3
          ], xs1)
        } else {
          throw new globalThis.Error("match error");
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
stronglyConnComp = function stronglyConnComp(es, vs) {
  let swap, span_tree, new_range, tmp, tmp1, tmp2, lambda1, lambda2;
  swap = function swap(a) {
    let first1, first0, f, s;
    if (globalThis.Array.isArray(a) && a.length === 2) {
      first0 = a[0];
      first1 = a[1];
      f = first0;
      s = first1;
      return [
        s,
        f
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  };
  new_range = function new_range(xys, w) {
    let param0, param1, first1, first0, x, y, xys1, scrut, tmp3;
    if (xys instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (xys instanceof NofibPrelude.Cons.class) {
      param0 = xys.head;
      param1 = xys.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        x = first0;
        y = first1;
        xys1 = param1;
        scrut = x == w;
        if (scrut === true) {
          tmp3 = new_range(xys1, w);
          return NofibPrelude.Cons(y, tmp3)
        } else {
          return new_range(xys1, w)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  span_tree = function span_tree(r, vsns, xs) {
    let first1, first0, vs1, ns, param0, param1, x, xs1, scrut, first11, first01, vs11, ns1, scrut1, tmp3, tmp4, tmp5, tmp6;
    if (globalThis.Array.isArray(vsns) && vsns.length === 2) {
      first0 = vsns[0];
      first1 = vsns[1];
      vs1 = first0;
      ns = first1;
      if (xs instanceof NofibPrelude.Nil.class) {
        return [
          vs1,
          ns
        ]
      } else if (xs instanceof NofibPrelude.Cons.class) {
        param0 = xs.head;
        param1 = xs.tail;
        x = param0;
        xs1 = param1;
        scrut1 = NofibPrelude.inList(x, vs1);
        if (scrut1 === true) {
          return span_tree(r, [
            vs1,
            ns
          ], xs1)
        } else {
          tmp3 = NofibPrelude.Cons(x, vs1);
          tmp4 = runtime.safeCall(r(x));
          scrut = dfs(r, [
            tmp3,
            NofibPrelude.Nil
          ], tmp4);
          if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
            first01 = scrut[0];
            first11 = scrut[1];
            vs11 = first01;
            ns1 = first11;
            tmp5 = NofibPrelude.Cons(x, ns1);
            tmp6 = NofibPrelude.Cons(tmp5, ns);
            return span_tree(r, [
              vs11,
              tmp6
            ], xs1)
          } else {
            throw new globalThis.Error("match error");
          }
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  lambda1 = (undefined, function (x) {
    return new_range(es, x)
  });
  tmp = dfs(lambda1, [
    NofibPrelude.Nil,
    NofibPrelude.Nil
  ], vs);
  tmp1 = NofibPrelude.snd(tmp);
  lambda2 = (undefined, function (x) {
    let tmp3;
    tmp3 = NofibPrelude.map(swap, es);
    return new_range(tmp3, x)
  });
  tmp2 = span_tree(lambda2, [
    NofibPrelude.Nil,
    NofibPrelude.Nil
  ], tmp1);
  return NofibPrelude.snd(tmp2)
};
testScc_nofib = function testScc_nofib(d) {
  let a, b, c, d1, f, g, h, vertices, edges, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16;
  a = 1;
  b = 2;
  c = 3;
  d1 = 4;
  f = 5;
  g = 6;
  h = 7;
  tmp = NofibPrelude.Cons(h, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(g, tmp);
  tmp2 = NofibPrelude.Cons(f, tmp1);
  tmp3 = NofibPrelude.Cons(d1, tmp2);
  tmp4 = NofibPrelude.Cons(c, tmp3);
  tmp5 = NofibPrelude.Cons(b, tmp4);
  tmp6 = NofibPrelude.Cons(a, tmp5);
  vertices = tmp6;
  tmp7 = NofibPrelude.Cons([
    h,
    g
  ], NofibPrelude.Nil);
  tmp8 = NofibPrelude.Cons([
    g,
    f
  ], tmp7);
  tmp9 = NofibPrelude.Cons([
    f,
    h
  ], tmp8);
  tmp10 = NofibPrelude.Cons([
    f,
    g
  ], tmp9);
  tmp11 = NofibPrelude.Cons([
    f,
    a
  ], tmp10);
  tmp12 = NofibPrelude.Cons([
    d1,
    c
  ], tmp11);
  tmp13 = NofibPrelude.Cons([
    c,
    h
  ], tmp12);
  tmp14 = NofibPrelude.Cons([
    c,
    d1
  ], tmp13);
  tmp15 = NofibPrelude.Cons([
    c,
    b
  ], tmp14);
  tmp16 = NofibPrelude.Cons([
    b,
    a
  ], tmp15);
  edges = tmp16;
  return stronglyConnComp(edges, vertices)
};
lambda = (undefined, function () {
  let tmp;
  tmp = testScc_nofib(0);
  return runtime.safeCall(tmp.toString())
});
BenchmarkPrelude.benchmark(lambda)