import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let down1, down2, down3, up, lscomp, lscomp1, thrid, get_output, lscomp2, restore_outport, restore, lscomp3, check_requests, check_lr_requests, pad, lscomp4, update_is, update_os, lscomp5, sim_then_send, ilabel, olabel, circsim1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda14, lambda15, lambda16, lambda17, lambda18, lambda19, lambda20, lambda21, lambda22, down1$, down2$, lambda$, lambda$1, lambda$2, lscomp$, lambda$3, lscomp$1, lscomp$2, lscomp$3, lambda$4, lambda$5, pad$, lscomp$4, lambda$6, update_os$, update_is$, lambda$7, lambda$8, lambda$9, lambda$10, lambda$11, lambda$12, lambda$13;
ilabel = function ilabel(n, pid_) {
  let tmp, tmp1;
  tmp = NofibPrelude.stringOfInt(n);
  tmp1 = NofibPrelude.stringConcat("x", tmp);
  return [
    tmp1,
    pid_
  ]
};
olabel = function olabel(n, pid_) {
  let tmp, tmp1;
  tmp = NofibPrelude.stringOfInt(n);
  tmp1 = NofibPrelude.stringConcat("y", tmp);
  return [
    tmp1,
    pid_
  ]
};
lambda19 = (undefined, function (x) {
  let tmp;
  tmp = 7 * x;
  return tmp + 1
});
lambda20 = (undefined, function (x) {
  let tmp;
  tmp = 7 * x;
  return tmp + 7
});
lambda21 = (undefined, function (x) {
  let tmp;
  tmp = 7 * x;
  return tmp + 1
});
lambda22 = (undefined, function (x) {
  return circsim1.reg(0, x)
});
lambda$13 = function lambda$(size, ins, outs, states, x, y) {
  let tmp;
  tmp = circsim1.critical_path_depth([
    size,
    ins,
    outs,
    states
  ]);
  return circsim1.do_cycle(tmp, x, y)
};
lambda18 = (undefined, function (size, ins, outs, states) {
  return (x, y) => {
    return lambda$13(size, ins, outs, states, x, y)
  }
});
sim_then_send = function sim_then_send(state, d) {
  let tmp;
  tmp = circsim1.simulate_components(d, state);
  return circsim1.do_sends(d, tmp)
};
lambda$12 = function lambda$(inputs, ins, s) {
  let tmp;
  tmp = NofibPrelude.zip(ins, inputs);
  return circsim1.store_inputs(tmp, s)
};
lambda17 = (undefined, function (inputs, ins) {
  return (s) => {
    return lambda$12(inputs, ins, s)
  }
});
lambda$11 = function lambda$(depth, s) {
  return circsim1.simulate_component(depth, s)
};
lambda16 = (undefined, function (depth) {
  return (s) => {
    return lambda$11(depth, s)
  }
});
lscomp5 = function lscomp(ls) {
  let param0, param1, h, t, first2, first1, first0, sig, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    if (globalThis.Array.isArray(h) && h.length === 3) {
      first0 = h[0];
      first1 = h[1];
      first2 = h[2];
      sig = first2;
      tmp = lscomp5(t);
      return NofibPrelude.Cons(sig, tmp)
    } else {
      return lscomp5(t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$10 = function lambda$(d, s) {
  return circsim1.acknowledge(d, s)
};
lambda14 = (undefined, function (d) {
  return (s) => {
    return lambda$10(d, s)
  }
});
lambda$9 = function lambda$(d, x) {
  return circsim1.do_send(d, x)
};
lambda15 = (undefined, function (d) {
  return (x) => {
    return lambda$9(d, x)
  }
});
lambda$8 = function lambda$(d, s) {
  return circsim1.check_depth(d, s)
};
lambda11 = (undefined, function (d) {
  return (s) => {
    return lambda$8(d, s)
  }
});
lambda12 = (undefined, function (x) {
  let tmp;
  tmp = circsim1.send(x);
  return NofibPrelude.snd(tmp)
});
lambda$7 = function lambda$(d, x, y) {
  return circsim1.update_io(d, x, y)
};
lambda13 = (undefined, function (d) {
  return (x, y) => {
    return lambda$7(d, x, y)
  }
});
update_is$ = function update_is$(lrps, state) {
  let tmp, tmp1;
  tmp = circsim1.inports(state);
  tmp1 = NofibPrelude.foldr(circsim1.update_i, tmp, lrps);
  return circsim1.updateInports(state, tmp1)
};
update_is = function update_is(lrps) {
  return (state) => {
    return update_is$(lrps, state)
  }
};
update_os$ = function update_os$(d, lrps, state) {
  let scrut, tmp, tmp1, tmp2;
  tmp = circsim1.pathDepth(state);
  scrut = tmp == d;
  if (scrut === true) {
    tmp1 = circsim1.outports(state);
    tmp2 = NofibPrelude.zipWith(circsim1.update_o, lrps, tmp1);
    return circsim1.updateOutports(state, tmp2)
  } else {
    return state
  }
};
update_os = function update_os(d, lrps) {
  return (state) => {
    return update_os$(d, lrps, state)
  }
};
lambda$6 = function lambda$(i, p, m_, x) {
  return circsim1.compare_and_update([
    i,
    p,
    m_
  ], x)
};
lambda10 = (undefined, function (i, p, m_) {
  return (x) => {
    return lambda$6(i, p, m_, x)
  }
});
lscomp$4 = function lscomp$(state, ls) {
  let param0, param1, h, t, first5, first4, first3, first2, first1, first0, p, m, ql, dl, qr, dr, tmp, tmp1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    if (globalThis.Array.isArray(h) && h.length === 6) {
      first0 = h[0];
      first1 = h[1];
      first2 = h[2];
      first3 = h[3];
      first4 = h[4];
      first5 = h[5];
      p = first0;
      m = first1;
      ql = first2;
      dl = first3;
      qr = first4;
      dr = first5;
      tmp = circsim1.pid(state);
      tmp1 = lscomp$4(state, t);
      return NofibPrelude.Cons([
        tmp,
        p,
        m,
        ql,
        dl,
        qr,
        dr,
        1
      ], tmp1)
    } else {
      return lscomp$4(state, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp4 = function lscomp(state) {
  return (ls) => {
    return lscomp$4(state, ls)
  }
};
lambda8 = (undefined, function (x) {
  return NofibPrelude.listLen(x)
});
pad$ = function pad$(pss, xs) {
  let max_ps, tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.map(lambda8, pss);
  tmp1 = NofibPrelude.maximum(tmp);
  max_ps = tmp1;
  tmp2 = NofibPrelude.replicate_lz(max_ps, circsim1.emptyPacket);
  tmp3 = NofibPrelude.append_nl_lz(xs, tmp2);
  return NofibPrelude.take_lz(max_ps, tmp3)
};
pad = function pad(pss) {
  return (xs) => {
    return pad$(pss, xs)
  }
};
lambda$5 = function lambda$(pss, x) {
  return pad$(pss, x)
};
lambda9 = (undefined, function (pss) {
  return (x) => {
    return lambda$5(pss, x)
  }
});
check_requests = function check_requests(xs) {
  let tmp;
  tmp = NofibPrelude.map(check_lr_requests, xs);
  return NofibPrelude.orList(tmp)
};
check_lr_requests = function check_lr_requests(pql) {
  let first5, first4, first3, first2, first1, first0, p, m, ql, dl, qr, dr;
  if (globalThis.Array.isArray(pql) && pql.length === 6) {
    first0 = pql[0];
    first1 = pql[1];
    first2 = pql[2];
    first3 = pql[3];
    first4 = pql[4];
    first5 = pql[5];
    p = first0;
    m = first1;
    ql = first2;
    dl = first3;
    qr = first4;
    dr = first5;
    return ql || qr
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$4 = function lambda$(d, s) {
  return circsim1.check_depth(d, s)
};
lambda6 = (undefined, function (d) {
  return (s) => {
    return lambda$4(d, s)
  }
});
lambda7 = (undefined, function (s) {
  let tmp;
  tmp = circsim1.outports(s);
  return check_requests(tmp)
});
lscomp$3 = function lscomp$(b, ls) {
  let param0, param1, h, t, first5, first4, first3, first2, first1, first0, p, m, ql, dl, qr, dr, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    if (globalThis.Array.isArray(h) && h.length === 6) {
      first0 = h[0];
      first1 = h[1];
      first2 = h[2];
      first3 = h[3];
      first4 = h[4];
      first5 = h[5];
      p = first0;
      m = first1;
      ql = first2;
      dl = first3;
      qr = first4;
      dr = first5;
      tmp = lscomp$3(b, t);
      return NofibPrelude.Cons([
        p,
        m,
        b,
        dl,
        b,
        dr
      ], tmp)
    } else {
      return lscomp$3(b, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp3 = function lscomp(b) {
  return (ls) => {
    return lscomp$3(b, ls)
  }
};
restore = function restore(os, ns) {
  let tmp, tmp1, tmp2;
  tmp = circsim1.outports(os);
  tmp1 = circsim1.outports(ns);
  tmp2 = NofibPrelude.zipWith(restore_outport, tmp, tmp1);
  return circsim1.updateOutports(ns, tmp2)
};
restore_outport = function restore_outport(pql, mdq) {
  let first5, first4, first3, first2, first1, first0, p, ql, dl, qr, dq, first51, first41, first31, first21, first11, first01, m;
  if (globalThis.Array.isArray(pql) && pql.length === 6) {
    first0 = pql[0];
    first1 = pql[1];
    first2 = pql[2];
    first3 = pql[3];
    first4 = pql[4];
    first5 = pql[5];
    p = first0;
    ql = first2;
    dl = first3;
    qr = first4;
    dq = first5;
    if (globalThis.Array.isArray(mdq) && mdq.length === 6) {
      first01 = mdq[0];
      first11 = mdq[1];
      first21 = mdq[2];
      first31 = mdq[3];
      first41 = mdq[4];
      first51 = mdq[5];
      m = first11;
      return [
        p,
        m,
        ql,
        dl,
        qr,
        dq
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp$2 = function lscomp$(state, pid_, ls) {
  let param0, param1, h, t, first1, first0, first11, first01, label, input_pid, value, scrut, tmp, tmp1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    if (globalThis.Array.isArray(h) && h.length === 2) {
      first0 = h[0];
      first1 = h[1];
      if (globalThis.Array.isArray(first0) && first0.length === 2) {
        first01 = first0[0];
        first11 = first0[1];
        label = first01;
        input_pid = first11;
        value = first1;
        scrut = pid_ == input_pid;
        if (scrut === true) {
          tmp = circsim1.update_outports(state, value);
          tmp1 = lscomp$2(state, pid_, t);
          return NofibPrelude.Cons(tmp, tmp1)
        } else {
          return lscomp$2(state, pid_, t)
        }
      } else {
        return lscomp$2(state, pid_, t)
      }
    } else {
      return lscomp$2(state, pid_, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp2 = function lscomp(state, pid_) {
  return (ls) => {
    return lscomp$2(state, pid_, ls)
  }
};
thrid = function thrid(tp3) {
  let first2, first1, first0, v;
  if (globalThis.Array.isArray(tp3) && tp3.length === 3) {
    first0 = tp3[0];
    first1 = tp3[1];
    first2 = tp3[2];
    v = first2;
    return v
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp$1 = function lscomp$(p, ls) {
  let param0, param1, s, t, scrut, tmp, tmp1, tmp2, tmp3;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    s = param0;
    t = param1;
    tmp = circsim1.pid(s);
    scrut = p == tmp;
    if (scrut === true) {
      tmp1 = circsim1.inports(s);
      tmp2 = NofibPrelude.head(tmp1);
      tmp3 = lscomp$1(p, t);
      return NofibPrelude.Cons(tmp2, tmp3)
    } else {
      return lscomp$1(p, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp1 = function lscomp(p) {
  return (ls) => {
    return lscomp$1(p, ls)
  }
};
get_output = function get_output(states, label_p) {
  let first1, first0, label, p, tmp, tmp1;
  if (globalThis.Array.isArray(label_p) && label_p.length === 2) {
    first0 = label_p[0];
    first1 = label_p[1];
    label = first0;
    p = first1;
    tmp = lscomp$1(p, states);
    tmp1 = NofibPrelude.head(tmp);
    return thrid(tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$3 = function lambda$(states, p) {
  return get_output(states, p)
};
lambda5 = (undefined, function (states) {
  return (p) => {
    return lambda$3(states, p)
  }
});
lscomp$ = function lscomp$(value, ls) {
  let param0, param1, h, t, first5, first4, first3, first2, first1, first0, p, m, ql, dl, qr, dr, tmp;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    if (globalThis.Array.isArray(h) && h.length === 6) {
      first0 = h[0];
      first1 = h[1];
      first2 = h[2];
      first3 = h[3];
      first4 = h[4];
      first5 = h[5];
      p = first0;
      m = first1;
      ql = first2;
      dl = first3;
      qr = first4;
      dr = first5;
      tmp = lscomp$(value, t);
      return NofibPrelude.Cons([
        p,
        value,
        ql,
        dl,
        qr,
        dr
      ], tmp)
    } else {
      return lscomp$(value, t)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp = function lscomp(value) {
  return (ls) => {
    return lscomp$(value, ls)
  }
};
lambda$2 = function lambda$(x, a) {
  return a >= x
};
lambda3 = (undefined, function (x) {
  return (a) => {
    return lambda$2(x, a)
  }
});
lambda4 = (undefined, function (a) {
  return a * 2
});
up = function up(f, g, lxly, rxry) {
  let first1, first0, lx, ly, first11, first01, rx, ry, tmp, tmp1;
  if (globalThis.Array.isArray(lxly) && lxly.length === 2) {
    first0 = lxly[0];
    first1 = lxly[1];
    lx = first0;
    ly = first1;
    if (globalThis.Array.isArray(rxry) && rxry.length === 2) {
      first01 = rxry[0];
      first11 = rxry[1];
      rx = first01;
      ry = first11;
      tmp = runtime.safeCall(f(lx, rx));
      tmp1 = runtime.safeCall(g(ly, ry));
      return [
        tmp,
        tmp1
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
down3 = function down3(f, g, lxly, rxry, ab) {
  let first1, first0, lx, ly, first11, first01, rx, ry, first12, first02, a, b, tmp, tmp1;
  if (globalThis.Array.isArray(lxly) && lxly.length === 2) {
    first0 = lxly[0];
    first1 = lxly[1];
    lx = first0;
    ly = first1;
    if (globalThis.Array.isArray(rxry) && rxry.length === 2) {
      first01 = rxry[0];
      first11 = rxry[1];
      rx = first01;
      ry = first11;
      if (globalThis.Array.isArray(ab) && ab.length === 2) {
        first02 = ab[0];
        first12 = ab[1];
        a = first02;
        b = first12;
        tmp = runtime.safeCall(g(ry, b));
        tmp1 = runtime.safeCall(f(a, lx));
        return [
          [
            a,
            tmp
          ],
          [
            tmp1,
            b
          ]
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
lambda = (undefined, function (x) {
  return [
    x,
    x
  ]
});
lambda$1 = function lambda$(f, g, a, b) {
  return up(f, g, a, b)
};
lambda1 = (undefined, function (f, g) {
  return (a, b) => {
    return lambda$1(f, g, a, b)
  }
});
lambda$ = function lambda$(f, g, a, b, c) {
  return down3(f, g, a, b, c)
};
lambda2 = (undefined, function (f, g) {
  return (a, b, c) => {
    return lambda$(f, g, a, b, c)
  }
});
down2$ = function down2$(f, l, r, x) {
  let tmp;
  tmp = runtime.safeCall(f(r, x));
  return [
    tmp,
    x
  ]
};
down2 = function down2(f) {
  return (l, r, x) => {
    return down2$(f, l, r, x)
  }
};
down1$ = function down1$(f, l, r, x) {
  let tmp;
  tmp = runtime.safeCall(f(x, l));
  return [
    x,
    tmp
  ]
};
down1 = function down1(f) {
  return (l, r, x) => {
    return down1$(f, l, r, x)
  }
};
circsim1 = class circsim {
  static {
    circsim1 = circsim;
    let tmp, tmp1, tmp2, tmp3, tmp4, lambda23;
    this.BinTree = class BinTree {
      constructor() {}
      toString() { return "BinTree"; }
    };
    this.Cell = function Cell(value1) {
      return new Cell.class(value1);
    };
    this.Cell.class = class Cell extends circsim.BinTree {
      constructor(value) {
        super();
        this.value = value;
      }
      toString() { return "Cell(" + globalThis.Predef.render(this.value) + ")"; }
    };
    this.Node = function Node(value1, left1, right1) {
      return new Node.class(value1, left1, right1);
    };
    this.Node.class = class Node extends circsim.BinTree {
      constructor(value, left, right) {
        super();
        this.value = value;
        this.left = left;
        this.right = right;
      }
      toString() { return "Node(" + globalThis.Predef.render(this.value) + ", " + globalThis.Predef.render(this.left) + ", " + globalThis.Predef.render(this.right) + ")"; }
    };
    this.Componenet = class Componenet {
      constructor() {}
      toString() { return "Componenet"; }
    };
    const None_$class = class None_ extends circsim.Componenet {
      constructor() {
        super();
      }
      toString() { return "None_"; }
    };
    this.None_ = new None_$class;
    this.None_.class = None_$class;
    const Inp$class = class Inp extends circsim.Componenet {
      constructor() {
        super();
      }
      toString() { return "Inp"; }
    };
    this.Inp = new Inp$class;
    this.Inp.class = Inp$class;
    const Outp$class = class Outp extends circsim.Componenet {
      constructor() {
        super();
      }
      toString() { return "Outp"; }
    };
    this.Outp = new Outp$class;
    this.Outp.class = Outp$class;
    const Dff$class = class Dff extends circsim.Componenet {
      constructor() {
        super();
      }
      toString() { return "Dff"; }
    };
    this.Dff = new Dff$class;
    this.Dff.class = Dff$class;
    const Inv$class = class Inv extends circsim.Componenet {
      constructor() {
        super();
      }
      toString() { return "Inv"; }
    };
    this.Inv = new Inv$class;
    this.Inv.class = Inv$class;
    const And2$class = class And2 extends circsim.Componenet {
      constructor() {
        super();
      }
      toString() { return "And2"; }
    };
    this.And2 = new And2$class;
    this.And2.class = And2$class;
    const Or2$class = class Or2 extends circsim.Componenet {
      constructor() {
        super();
      }
      toString() { return "Or2"; }
    };
    this.Or2 = new Or2$class;
    this.Or2.class = Or2$class;
    const Xor$class = class Xor extends circsim.Componenet {
      constructor() {
        super();
      }
      toString() { return "Xor"; }
    };
    this.Xor = new Xor$class;
    this.Xor.class = Xor$class;
    const Unit$class = class Unit {
      constructor() {}
      toString() { return "Unit"; }
    };
    this.Unit = new Unit$class;
    this.Unit.class = Unit$class;
    this.PS = function PS(pid1, compType1, pathDepth1, inports1, outports1) {
      return new PS.class(pid1, compType1, pathDepth1, inports1, outports1);
    };
    this.PS.class = class PS {
      constructor(pid, compType, pathDepth, inports, outports) {
        this.pid = pid;
        this.compType = compType;
        this.pathDepth = pathDepth;
        this.inports = inports;
        this.outports = outports;
      }
      toString() { return "PS(" + globalThis.Predef.render(this.pid) + ", " + globalThis.Predef.render(this.compType) + ", " + globalThis.Predef.render(this.pathDepth) + ", " + globalThis.Predef.render(this.inports) + ", " + globalThis.Predef.render(this.outports) + ")"; }
    };
    this.Boolean = class Boolean {
      constructor() {}
      toString() { return "Boolean"; }
    };
    const F$class = class F extends circsim.Boolean {
      constructor() {
        super();
      }
      toString() { return "F"; }
    };
    this.F = new F$class;
    this.F.class = F$class;
    const T$class = class T extends circsim.Boolean {
      constructor() {
        super();
      }
      toString() { return "T"; }
    };
    this.T = new T$class;
    this.T.class = T$class;
    tmp = - 1;
    tmp1 = - 1;
    tmp2 = circsim.PS(tmp, circsim.None_, tmp1, NofibPrelude.Nil, NofibPrelude.Nil);
    this.emptyState = tmp2;
    tmp3 = - 1;
    tmp4 = - 1;
    this.emptyPacket = [
      tmp3,
      tmp4,
      circsim.F,
      false,
      0,
      false,
      0,
      1
    ];
    lambda23 = (undefined, function () {
      let tmp5;
      tmp5 = circsim.testCircsim_nofib(40);
      return runtime.safeCall(tmp5.toString())
    });
    BenchmarkPrelude.benchmark(lambda23)
  }
  static pid(p) {
    return p.pid
  } 
  static compType(p1) {
    return p1.compType
  } 
  static pathDepth(p2) {
    return p2.pathDepth
  } 
  static inports(p3) {
    return p3.inports
  } 
  static outports(p4) {
    return p4.outports
  } 
  static updateOutports(p5, noutports) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = circsim.pid(p5);
    tmp1 = circsim.compType(p5);
    tmp2 = circsim.pathDepth(p5);
    tmp3 = circsim.inports(p5);
    return circsim.PS(tmp, tmp1, tmp2, tmp3, noutports)
  } 
  static updateInports(p6, ninports) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = circsim.pid(p6);
    tmp1 = circsim.compType(p6);
    tmp2 = circsim.pathDepth(p6);
    tmp3 = circsim.outports(p6);
    return circsim.PS(tmp, tmp1, tmp2, ninports, tmp3)
  } 
  static put(xs) {
    let scrut, first1, first0, fstHalf, sndHalf, param0, param1, x, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    if (xs instanceof NofibPrelude.Cons.class) {
      param0 = xs.head;
      param1 = xs.tail;
      x = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return circsim.Cell(x)
      } else {
        tmp = NofibPrelude.listLen(xs);
        tmp1 = NofibPrelude.intDiv(tmp, 2);
        scrut = NofibPrelude.splitAt(tmp1, xs);
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first0 = scrut[0];
          first1 = scrut[1];
          fstHalf = first0;
          sndHalf = first1;
          tmp2 = circsim.put(fstHalf);
          tmp3 = circsim.put(sndHalf);
          return circsim.Node(circsim.Unit, tmp2, tmp3)
        } else {
          throw new globalThis.Error("match error");
        }
      }
    } else {
      tmp4 = NofibPrelude.listLen(xs);
      tmp5 = NofibPrelude.intDiv(tmp4, 2);
      scrut = NofibPrelude.splitAt(tmp5, xs);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        fstHalf = first0;
        sndHalf = first1;
        tmp6 = circsim.put(fstHalf);
        tmp7 = circsim.put(sndHalf);
        return circsim.Node(circsim.Unit, tmp6, tmp7)
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  static get(t) {
    let param0, param1, param2, l, r, param01, x, tmp, tmp1;
    if (t instanceof circsim.Cell.class) {
      param01 = t.value;
      x = param01;
      return NofibPrelude.Cons(x, NofibPrelude.Nil)
    } else if (t instanceof circsim.Node.class) {
      param0 = t.value;
      param1 = t.left;
      param2 = t.right;
      l = param1;
      r = param2;
      tmp = circsim.get(l);
      tmp1 = circsim.get(r);
      return NofibPrelude.append(tmp, tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static upsweep(f, t1) {
    let param0, param1, param2, x, l, r, scrut, first1, first0, lv, l_, scrut1, first11, first01, rv, r_, param01, a, tmp, tmp1, tmp2;
    if (t1 instanceof circsim.Cell.class) {
      param01 = t1.value;
      a = param01;
      tmp = circsim.Cell(a);
      return [
        a,
        tmp
      ]
    } else if (t1 instanceof circsim.Node.class) {
      param0 = t1.value;
      param1 = t1.left;
      param2 = t1.right;
      x = param0;
      l = param1;
      r = param2;
      scrut = circsim.upsweep(f, l);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        lv = first0;
        l_ = first1;
        scrut1 = circsim.upsweep(f, r);
        if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
          first01 = scrut1[0];
          first11 = scrut1[1];
          rv = first01;
          r_ = first11;
          tmp1 = runtime.safeCall(f(lv, rv));
          tmp2 = circsim.Node([
            lv,
            rv
          ], l_, r_);
          return [
            tmp1,
            tmp2
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
  static downsweep(g, d, t2) {
    let param0, param1, param2, first1, first0, lv, rv, l, r, scrut, first11, first01, dl, dr, param01, x, tmp, tmp1;
    if (t2 instanceof circsim.Cell.class) {
      param01 = t2.value;
      x = param01;
      return circsim.Cell(d)
    } else if (t2 instanceof circsim.Node.class) {
      param0 = t2.value;
      param1 = t2.left;
      param2 = t2.right;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        lv = first0;
        rv = first1;
        l = param1;
        r = param2;
        scrut = runtime.safeCall(g(lv, rv, d));
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first01 = scrut[0];
          first11 = scrut[1];
          dl = first01;
          dr = first11;
          tmp = circsim.downsweep(g, dl, l);
          tmp1 = circsim.downsweep(g, dr, r);
          return circsim.Node(circsim.Unit, tmp, tmp1)
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
  static sweep_ud(up1, down, u, t3) {
    let scrut, first1, first0, ans, t_, tmp;
    scrut = circsim.upsweep(up1, t3);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      ans = first0;
      t_ = first1;
      tmp = circsim.downsweep(down, u, t_);
      return [
        ans,
        tmp
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static scanL(f1, u1, xs1) {
    let scrut, first1, first0, up_ans, t_, tmp, tmp1, down1$this;
    tmp = circsim.put(xs1);
    down1$this = runtime.safeCall(down1(f1));
    scrut = circsim.sweep_ud(f1, down1$this, u1, tmp);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      up_ans = first0;
      t_ = first1;
      tmp1 = circsim.get(t_);
      return [
        up_ans,
        tmp1
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static scanR(f2, u2, xs2) {
    let scrut, first1, first0, up_ans, t_, tmp, tmp1, down2$this;
    tmp = circsim.put(xs2);
    down2$this = runtime.safeCall(down2(f2));
    scrut = circsim.sweep_ud(f2, down2$this, u2, tmp);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      up_ans = first0;
      t_ = first1;
      tmp1 = circsim.get(t_);
      return [
        up_ans,
        tmp1
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static scanlr(f3, g1, lu, ru, xs3) {
    let xs_, scrut, first1, first0, first11, first01, l_ans, r_ans, t_, ans, tmp, tmp1, tmp2, tmp3, tmp4, lambda$this, lambda$this1;
    tmp = NofibPrelude.map(lambda, xs3);
    xs_ = tmp;
    tmp1 = circsim.put(xs_);
    lambda$this = runtime.safeCall(lambda1(f3, g1));
    lambda$this1 = runtime.safeCall(lambda2(f3, g1));
    scrut = circsim.sweep_ud(lambda$this, lambda$this1, [
      lu,
      ru
    ], tmp1);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      if (globalThis.Array.isArray(first0) && first0.length === 2) {
        first01 = first0[0];
        first11 = first0[1];
        l_ans = first01;
        r_ans = first11;
        t_ = first1;
        tmp2 = runtime.safeCall(g1(r_ans, ru));
        tmp3 = runtime.safeCall(f3(lu, l_ans));
        ans = [
          tmp2,
          tmp3
        ];
        tmp4 = circsim.get(t_);
        return [
          ans,
          tmp4
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static nearest_power_of_two(x) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda3(x));
    return NofibPrelude.until(lambda$this, lambda4, 1)
  } 
  static pad_circuit(size_ins_outs_states) {
    let first3, first2, first1, first0, size, ins, outs, states, p21, states_, tmp, tmp1, tmp2, tmp3;
    if (globalThis.Array.isArray(size_ins_outs_states) && size_ins_outs_states.length === 4) {
      first0 = size_ins_outs_states[0];
      first1 = size_ins_outs_states[1];
      first2 = size_ins_outs_states[2];
      first3 = size_ins_outs_states[3];
      size = first0;
      ins = first1;
      outs = first2;
      states = first3;
      tmp = circsim.nearest_power_of_two(size);
      p21 = tmp;
      tmp1 = NofibPrelude.replicate_lz(p21, circsim.emptyState);
      tmp2 = NofibPrelude.append_nl_lz(states, tmp1);
      states_ = tmp2;
      tmp3 = NofibPrelude.take_lz(p21, states_);
      return [
        p21,
        ins,
        outs,
        tmp3
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static inv(x1) {
    let scrut;
    scrut = x1 === circsim.T;
    if (scrut === true) {
      return circsim.F
    } else {
      return circsim.T
    }
  } 
  static and2(x2, y) {
    let scrut, tmp, tmp1;
    tmp = x2 === circsim.T;
    tmp1 = y === circsim.T;
    scrut = tmp && tmp1;
    if (scrut === true) {
      return circsim.T
    } else {
      return circsim.F
    }
  } 
  static or2(x3, y1) {
    let scrut, tmp, tmp1;
    tmp = x3 === circsim.T;
    tmp1 = y1 === circsim.T;
    scrut = tmp || tmp1;
    if (scrut === true) {
      return circsim.T
    } else {
      return circsim.F
    }
  } 
  static xor(x4, y2) {
    let scrut;
    scrut = x4 === y2;
    if (scrut === true) {
      return circsim.T
    } else {
      return circsim.F
    }
  } 
  static send_right(a, b) {
    let first7, first6, first5, first4, first3, first2, first1, first0, ia, sa, ma, qla, dla, qra, dra, ea, first71, first61, first51, first41, first31, first21, first11, first01, ib, sb, mb, qlb, dlb, qrb, drb, eb, scrut, tmp, tmp1, tmp2, tmp3;
    if (globalThis.Array.isArray(a) && a.length === 8) {
      first0 = a[0];
      first1 = a[1];
      first2 = a[2];
      first3 = a[3];
      first4 = a[4];
      first5 = a[5];
      first6 = a[6];
      first7 = a[7];
      ia = first0;
      sa = first1;
      ma = first2;
      qla = first3;
      dla = first4;
      qra = first5;
      dra = first6;
      ea = first7;
      if (globalThis.Array.isArray(b) && b.length === 8) {
        first01 = b[0];
        first11 = b[1];
        first21 = b[2];
        first31 = b[3];
        first41 = b[4];
        first51 = b[5];
        first61 = b[6];
        first71 = b[7];
        ib = first01;
        sb = first11;
        mb = first21;
        qlb = first31;
        dlb = first41;
        qrb = first51;
        drb = first61;
        eb = first71;
        if (qra === true) {
          scrut = dra > eb;
          if (scrut === true) {
            tmp = dra - eb;
            tmp1 = ea + eb;
            return [
              ia,
              sa,
              ma,
              qla,
              dla,
              qra,
              tmp,
              tmp1
            ]
          } else {
            tmp2 = ea + eb;
            return [
              ib,
              sb,
              mb,
              qlb,
              dlb,
              qrb,
              drb,
              tmp2
            ]
          }
        } else {
          tmp3 = ea + eb;
          return [
            ib,
            sb,
            mb,
            qlb,
            dlb,
            qrb,
            drb,
            tmp3
          ]
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static send_left(a1, b1) {
    let first7, first6, first5, first4, first3, first2, first1, first0, ia, sa, ma, qla, dla, qra, dra, ea, first71, first61, first51, first41, first31, first21, first11, first01, ib, sb, mb, qlb, dlb, qrb, drb, eb, scrut, tmp, tmp1, tmp2, tmp3;
    if (globalThis.Array.isArray(a1) && a1.length === 8) {
      first0 = a1[0];
      first1 = a1[1];
      first2 = a1[2];
      first3 = a1[3];
      first4 = a1[4];
      first5 = a1[5];
      first6 = a1[6];
      first7 = a1[7];
      ia = first0;
      sa = first1;
      ma = first2;
      qla = first3;
      dla = first4;
      qra = first5;
      dra = first6;
      ea = first7;
      if (globalThis.Array.isArray(b1) && b1.length === 8) {
        first01 = b1[0];
        first11 = b1[1];
        first21 = b1[2];
        first31 = b1[3];
        first41 = b1[4];
        first51 = b1[5];
        first61 = b1[6];
        first71 = b1[7];
        ib = first01;
        sb = first11;
        mb = first21;
        qlb = first31;
        dlb = first41;
        qrb = first51;
        drb = first61;
        eb = first71;
        tmp = dlb > ea;
        scrut = qlb && tmp;
        if (scrut === true) {
          tmp1 = dlb - ea;
          tmp2 = ea + eb;
          return [
            ib,
            sb,
            mb,
            qlb,
            tmp1,
            qrb,
            drb,
            tmp2
          ]
        } else {
          tmp3 = ea + eb;
          return [
            ia,
            sa,
            ma,
            qla,
            dla,
            qra,
            dra,
            tmp3
          ]
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static send(xs4) {
    return circsim.scanlr(circsim.send_right, circsim.send_left, circsim.emptyPacket, circsim.emptyPacket, xs4)
  } 
  static update_outports(state, value) {
    let tmp, tmp1;
    tmp = circsim.outports(state);
    tmp1 = lscomp$(value, tmp);
    return circsim.updateOutports(state, tmp1)
  } 
  static critical_path_depth(siot) {
    let first3, first2, first1, first0, size, ins, outs, states, tmp;
    if (globalThis.Array.isArray(siot) && siot.length === 4) {
      first0 = siot[0];
      first1 = siot[1];
      first2 = siot[2];
      first3 = siot[3];
      size = first0;
      ins = first1;
      outs = first2;
      states = first3;
      tmp = NofibPrelude.map(circsim.pathDepth, states);
      return NofibPrelude.maximum(tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static collect_outputs(tp4) {
    let first3, first2, first1, first0, size, ins, outs, states, lambda$this;
    if (globalThis.Array.isArray(tp4) && tp4.length === 4) {
      first0 = tp4[0];
      first1 = tp4[1];
      first2 = tp4[2];
      first3 = tp4[3];
      size = first0;
      ins = first1;
      outs = first2;
      states = first3;
      lambda$this = runtime.safeCall(lambda5(states));
      return NofibPrelude.map(lambda$this, outs)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static store_inputs(label_inputs, state1) {
    let param0, param1, param2, param3, param4, pid_, tmp;
    if (state1 instanceof circsim.PS.class) {
      param0 = state1.pid;
      param1 = state1.compType;
      param2 = state1.pathDepth;
      param3 = state1.inports;
      param4 = state1.outports;
      pid_ = param0;
      if (param1 instanceof circsim.Inp.class) {
        tmp = lscomp$2(state1, pid_, label_inputs);
        return NofibPrelude.head(tmp)
      } else {
        return state1
      }
    } else {
      return state1
    }
  } 
  static apply_component(comp, signals) {
    let param0, param1, x5, param01, param11, y3, x6, y4, x7, y5, x8, x9, x10, tmp, tmp1, tmp2, tmp3;
    if (comp instanceof circsim.Inp.class) {
      return NofibPrelude.None
    } else if (comp instanceof circsim.Outp.class) {
      if (signals instanceof NofibPrelude.Cons.class) {
        param0 = signals.head;
        param1 = signals.tail;
        x10 = param0;
        if (param1 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Some(x10)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (comp instanceof circsim.Dff.class) {
      if (signals instanceof NofibPrelude.Cons.class) {
        param0 = signals.head;
        param1 = signals.tail;
        x9 = param0;
        if (param1 instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Some(x9)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (comp instanceof circsim.Inv.class) {
      if (signals instanceof NofibPrelude.Cons.class) {
        param0 = signals.head;
        param1 = signals.tail;
        x8 = param0;
        if (param1 instanceof NofibPrelude.Nil.class) {
          tmp = circsim.inv(x8);
          return NofibPrelude.Some(tmp)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (comp instanceof circsim.And2.class) {
      if (signals instanceof NofibPrelude.Cons.class) {
        param0 = signals.head;
        param1 = signals.tail;
        x7 = param0;
        if (param1 instanceof NofibPrelude.Cons.class) {
          param01 = param1.head;
          param11 = param1.tail;
          y5 = param01;
          if (param11 instanceof NofibPrelude.Nil.class) {
            tmp1 = circsim.and2(x7, y5);
            return NofibPrelude.Some(tmp1)
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (comp instanceof circsim.Or2.class) {
      if (signals instanceof NofibPrelude.Cons.class) {
        param0 = signals.head;
        param1 = signals.tail;
        x6 = param0;
        if (param1 instanceof NofibPrelude.Cons.class) {
          param01 = param1.head;
          param11 = param1.tail;
          y4 = param01;
          if (param11 instanceof NofibPrelude.Nil.class) {
            tmp2 = circsim.or2(x6, y4);
            return NofibPrelude.Some(tmp2)
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (comp instanceof circsim.Xor.class) {
      if (signals instanceof NofibPrelude.Cons.class) {
        param0 = signals.head;
        param1 = signals.tail;
        x5 = param0;
        if (param1 instanceof NofibPrelude.Cons.class) {
          param01 = param1.head;
          param11 = param1.tail;
          y3 = param01;
          if (param11 instanceof NofibPrelude.Nil.class) {
            tmp3 = circsim.xor(x5, y3);
            return NofibPrelude.Some(tmp3)
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (comp instanceof circsim.None_.class) {
      return NofibPrelude.None
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static init_dffs(state2) {
    let scrut, tmp;
    tmp = circsim.compType(state2);
    scrut = tmp === circsim.Dff;
    if (scrut === true) {
      return circsim.update_outports(state2, circsim.F)
    } else {
      return state2
    }
  } 
  static restore_requests(old_states, new_states) {
    return NofibPrelude.zipWith(restore, old_states, new_states)
  } 
  static update_requests(b2, state3) {
    let tmp, tmp1;
    tmp = circsim.outports(state3);
    tmp1 = lscomp$3(b2, tmp);
    return circsim.updateOutports(state3, tmp1)
  } 
  static check_depth(d1, state4) {
    let scrut, tmp;
    tmp = circsim.pathDepth(state4);
    scrut = tmp == d1;
    if (scrut === true) {
      return state4
    } else {
      return circsim.update_requests(false, state4)
    }
  } 
  static acknowledge(d2, states) {
    let states1, tmp, tmp1, tmp2, lambda$this;
    lambda$this = runtime.safeCall(lambda6(d2));
    tmp = NofibPrelude.map(lambda$this, states);
    states1 = tmp;
    tmp1 = NofibPrelude.map(lambda7, states1);
    tmp2 = NofibPrelude.orList(tmp1);
    return BenchmarkPrelude.not(tmp2)
  } 
  static pad_packets(pss) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda9(pss));
    return NofibPrelude.map(lambda$this, pss)
  } 
  static make_packet(state5) {
    let tmp;
    tmp = circsim.outports(state5);
    return lscomp$4(state5, tmp)
  } 
  static compare_and_update(ipm_, pid_port_m) {
    let first2, first1, first0, i, p7, m_, first21, first11, first01, pid_, port, m, scrut;
    if (globalThis.Array.isArray(ipm_) && ipm_.length === 3) {
      first0 = ipm_[0];
      first1 = ipm_[1];
      first2 = ipm_[2];
      i = first0;
      p7 = first1;
      m_ = first2;
      if (globalThis.Array.isArray(pid_port_m) && pid_port_m.length === 3) {
        first01 = pid_port_m[0];
        first11 = pid_port_m[1];
        first21 = pid_port_m[2];
        pid_ = first01;
        port = first11;
        m = first21;
        scrut = NofibPrelude.eqTup2([
          i,
          p7
        ], [
          pid_,
          port
        ]);
        if (scrut === true) {
          return [
            pid_,
            port,
            m_
          ]
        } else {
          return [
            pid_,
            port,
            m
          ]
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static up_i(ipm_1, ins) {
    let first7, first6, first5, first4, first3, first2, first1, first0, i, p7, m_, lambda$this;
    if (globalThis.Array.isArray(ipm_1) && ipm_1.length === 8) {
      first0 = ipm_1[0];
      first1 = ipm_1[1];
      first2 = ipm_1[2];
      first3 = ipm_1[3];
      first4 = ipm_1[4];
      first5 = ipm_1[5];
      first6 = ipm_1[6];
      first7 = ipm_1[7];
      i = first0;
      p7 = first1;
      m_ = first2;
      lambda$this = runtime.safeCall(lambda10(i, p7, m_));
      return NofibPrelude.map(lambda$this, ins)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static update_i(l_r, ins1) {
    let first1, first0, l, r, tmp;
    if (globalThis.Array.isArray(l_r) && l_r.length === 2) {
      first0 = l_r[0];
      first1 = l_r[1];
      l = first0;
      r = first1;
      tmp = circsim.up_i(r, ins1);
      return circsim.up_i(l, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static check_left(a2, b3) {
    let first7, first6, first5, first4, first3, first2, first1, first0, pid_, port, pm, pql, pdl, pqr, pdr, e, first51, first41, first31, first21, first11, first01, p7, m, ql, dl, qr, dr, scrut, tmp;
    if (globalThis.Array.isArray(a2) && a2.length === 8) {
      first0 = a2[0];
      first1 = a2[1];
      first2 = a2[2];
      first3 = a2[3];
      first4 = a2[4];
      first5 = a2[5];
      first6 = a2[6];
      first7 = a2[7];
      pid_ = first0;
      port = first1;
      pm = first2;
      pql = first3;
      pdl = first4;
      pqr = first5;
      pdr = first6;
      e = first7;
      if (globalThis.Array.isArray(b3) && b3.length === 6) {
        first01 = b3[0];
        first11 = b3[1];
        first21 = b3[2];
        first31 = b3[3];
        first41 = b3[4];
        first51 = b3[5];
        p7 = first01;
        m = first11;
        ql = first21;
        dl = first31;
        qr = first41;
        dr = first51;
        tmp = pdr > 0;
        scrut = pqr && tmp;
        if (scrut === true) {
          return [
            p7,
            m,
            ql,
            dl,
            qr,
            dr
          ]
        } else {
          return [
            p7,
            m,
            ql,
            dl,
            false,
            dr
          ]
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static check_right(a3, b4) {
    let first7, first6, first5, first4, first3, first2, first1, first0, pid_, port, pm, pql, pdl, pqr, pdr, e, first51, first41, first31, first21, first11, first01, p7, m, ql, dl, qr, dr, scrut, tmp;
    if (globalThis.Array.isArray(a3) && a3.length === 8) {
      first0 = a3[0];
      first1 = a3[1];
      first2 = a3[2];
      first3 = a3[3];
      first4 = a3[4];
      first5 = a3[5];
      first6 = a3[6];
      first7 = a3[7];
      pid_ = first0;
      port = first1;
      pm = first2;
      pql = first3;
      pdl = first4;
      pqr = first5;
      pdr = first6;
      e = first7;
      if (globalThis.Array.isArray(b4) && b4.length === 6) {
        first01 = b4[0];
        first11 = b4[1];
        first21 = b4[2];
        first31 = b4[3];
        first41 = b4[4];
        first51 = b4[5];
        p7 = first01;
        m = first11;
        ql = first21;
        dl = first31;
        qr = first41;
        dr = first51;
        tmp = pdl > 0;
        scrut = pql && tmp;
        if (scrut === true) {
          return [
            p7,
            m,
            ql,
            dl,
            qr,
            dr
          ]
        } else {
          return [
            p7,
            m,
            false,
            dl,
            qr,
            dr
          ]
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static update_o(lp_rp, out_) {
    let first1, first0, lp, rp, tmp;
    if (globalThis.Array.isArray(lp_rp) && lp_rp.length === 2) {
      first0 = lp_rp[0];
      first1 = lp_rp[1];
      lp = first0;
      rp = first1;
      tmp = circsim.check_right(rp, out_);
      return circsim.check_left(lp, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static update_io(d3, lrps, state6) {
    let tmp;
    tmp = update_is$(lrps, state6);
    return update_os$(d3, lrps, tmp)
  } 
  static do_send(d4, states1) {
    let states11, send_results, pss_, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, lambda$this, lambda$this1;
    lambda$this = runtime.safeCall(lambda11(d4));
    tmp = NofibPrelude.map(lambda$this, states1);
    states11 = tmp;
    tmp1 = NofibPrelude.map(circsim.make_packet, states11);
    tmp2 = circsim.pad_packets(tmp1);
    tmp3 = NofibPrelude.transpose(tmp2);
    tmp4 = NofibPrelude.map(lambda12, tmp3);
    send_results = tmp4;
    tmp5 = NofibPrelude.transpose(send_results);
    pss_ = tmp5;
    lambda$this1 = runtime.safeCall(lambda13(d4));
    return NofibPrelude.zipWith(lambda$this1, pss_, states1)
  } 
  static do_sends(d5, states2) {
    let lambda$this, lambda$this1;
    lambda$this = runtime.safeCall(lambda14(d5));
    lambda$this1 = runtime.safeCall(lambda15(d5));
    return NofibPrelude.until(lambda$this, lambda$this1, states2)
  } 
  static simulate_component(d6, state7) {
    let out_signals, new_value, scrut, scrut1, param0, v, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = circsim.inports(state7);
    tmp1 = lscomp5(tmp);
    out_signals = tmp1;
    tmp2 = circsim.compType(state7);
    tmp3 = circsim.apply_component(tmp2, out_signals);
    new_value = tmp3;
    tmp4 = circsim.pathDepth(state7);
    scrut = d6 == tmp4;
    if (scrut === true) {
      tmp5 = new_value === NofibPrelude.None;
      scrut1 = BenchmarkPrelude.not(tmp5);
      if (scrut1 === true) {
        if (new_value instanceof NofibPrelude.Some.class) {
          param0 = new_value.x;
          v = param0;
          return circsim.update_outports(state7, v)
        } else {
          return state7
        }
      } else {
        return state7
      }
    } else {
      return state7
    }
  } 
  static simulate_components(depth, states3) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda16(depth));
    return NofibPrelude.map(lambda$this, states3)
  } 
  static do_cycle(cpd, tp41, inputs) {
    let first3, first2, first1, first0, size, ins2, outs, states4, states11, states21, states31, states41, tmp, tmp1, tmp2, tmp3, tmp4, lambda$this;
    if (globalThis.Array.isArray(tp41) && tp41.length === 4) {
      first0 = tp41[0];
      first1 = tp41[1];
      first2 = tp41[2];
      first3 = tp41[3];
      size = first0;
      ins2 = first1;
      outs = first2;
      states4 = first3;
      lambda$this = runtime.safeCall(lambda17(inputs, ins2));
      tmp = NofibPrelude.map(lambda$this, states4);
      states11 = tmp;
      tmp1 = circsim.do_sends(0, states11);
      states21 = tmp1;
      tmp2 = NofibPrelude.enumFromTo(1, cpd);
      tmp3 = NofibPrelude.foldl(sim_then_send, states21, tmp2);
      states31 = tmp3;
      tmp4 = circsim.restore_requests(states4, states31);
      states41 = tmp4;
      return [
        size,
        ins2,
        outs,
        states41
      ]
    } else {
      throw globalThis.Error(tp41);
    }
  } 
  static simulate(inputs_list, b5) {
    let first3, first2, first1, first0, size, ins2, outs, states4, tmp, tmp1, lambda$this;
    if (globalThis.Array.isArray(b5) && b5.length === 4) {
      first0 = b5[0];
      first1 = b5[1];
      first2 = b5[2];
      first3 = b5[3];
      size = first0;
      ins2 = first1;
      outs = first2;
      states4 = first3;
      tmp = NofibPrelude.map(circsim.init_dffs, states4);
      lambda$this = runtime.safeCall(lambda18(size, ins2, outs, states4));
      tmp1 = NofibPrelude.scanl(lambda$this, [
        size,
        ins2,
        outs,
        tmp
      ], inputs_list);
      return NofibPrelude.tail(tmp1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static reg(sto, n) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39;
    tmp = NofibPrelude.Cons([
      0,
      circsim.F,
      false,
      0,
      true,
      4
    ], NofibPrelude.Nil);
    tmp1 = circsim.PS(n, circsim.Inp, 0, NofibPrelude.Nil, tmp);
    tmp2 = n + 1;
    tmp3 = n + 5;
    tmp4 = NofibPrelude.Cons([
      tmp3,
      0,
      circsim.F
    ], NofibPrelude.Nil);
    tmp5 = NofibPrelude.Cons([
      0,
      circsim.F,
      false,
      0,
      true,
      5
    ], NofibPrelude.Nil);
    tmp6 = circsim.PS(tmp2, circsim.Dff, 1, tmp4, tmp5);
    tmp7 = n + 2;
    tmp8 = NofibPrelude.Cons([
      sto,
      0,
      circsim.F
    ], NofibPrelude.Nil);
    tmp9 = NofibPrelude.Cons([
      0,
      circsim.F,
      false,
      0,
      true,
      1
    ], NofibPrelude.Nil);
    tmp10 = circsim.PS(tmp7, circsim.Inv, 1, tmp8, tmp9);
    tmp11 = n + 3;
    tmp12 = n + 1;
    tmp13 = n + 2;
    tmp14 = NofibPrelude.Cons([
      tmp13,
      0,
      circsim.F
    ], NofibPrelude.Nil);
    tmp15 = NofibPrelude.Cons([
      tmp12,
      0,
      circsim.F
    ], tmp14);
    tmp16 = NofibPrelude.Cons([
      0,
      circsim.F,
      false,
      0,
      true,
      2
    ], NofibPrelude.Nil);
    tmp17 = circsim.PS(tmp11, circsim.And2, 2, tmp15, tmp16);
    tmp18 = n + 4;
    tmp19 = NofibPrelude.Cons([
      n,
      0,
      circsim.F
    ], NofibPrelude.Nil);
    tmp20 = NofibPrelude.Cons([
      sto,
      0,
      circsim.F
    ], tmp19);
    tmp21 = NofibPrelude.Cons([
      0,
      circsim.F,
      false,
      0,
      true,
      1
    ], NofibPrelude.Nil);
    tmp22 = circsim.PS(tmp18, circsim.And2, 1, tmp20, tmp21);
    tmp23 = n + 5;
    tmp24 = n + 3;
    tmp25 = n + 4;
    tmp26 = NofibPrelude.Cons([
      tmp25,
      0,
      circsim.F
    ], NofibPrelude.Nil);
    tmp27 = NofibPrelude.Cons([
      tmp24,
      0,
      circsim.F
    ], tmp26);
    tmp28 = NofibPrelude.Cons([
      0,
      circsim.F,
      true,
      4,
      false,
      0
    ], NofibPrelude.Nil);
    tmp29 = circsim.PS(tmp23, circsim.Or2, 3, tmp27, tmp28);
    tmp30 = n + 6;
    tmp31 = n + 1;
    tmp32 = NofibPrelude.Cons([
      tmp31,
      0,
      circsim.F
    ], NofibPrelude.Nil);
    tmp33 = circsim.PS(tmp30, circsim.Outp, 4, tmp32, NofibPrelude.Nil);
    tmp34 = NofibPrelude.Cons(tmp33, NofibPrelude.Nil);
    tmp35 = NofibPrelude.Cons(tmp29, tmp34);
    tmp36 = NofibPrelude.Cons(tmp22, tmp35);
    tmp37 = NofibPrelude.Cons(tmp17, tmp36);
    tmp38 = NofibPrelude.Cons(tmp10, tmp37);
    tmp39 = NofibPrelude.Cons(tmp6, tmp38);
    return NofibPrelude.Cons(tmp1, tmp39)
  } 
  static regs(bits) {
    let is_, os, sto1, states4, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23;
    tmp = NofibPrelude.enumFrom(0);
    tmp1 = bits - 1;
    tmp2 = NofibPrelude.enumFromTo(0, tmp1);
    tmp3 = NofibPrelude.map(lambda19, tmp2);
    tmp4 = NofibPrelude.zipWith_lz_nl(ilabel, tmp, tmp3);
    tmp5 = NofibPrelude.Cons([
      "sto",
      0
    ], tmp4);
    is_ = tmp5;
    tmp6 = NofibPrelude.enumFrom(0);
    tmp7 = bits - 1;
    tmp8 = NofibPrelude.enumFromTo(0, tmp7);
    tmp9 = NofibPrelude.map(lambda20, tmp8);
    tmp10 = NofibPrelude.zipWith_lz_nl(olabel, tmp6, tmp9);
    os = tmp10;
    tmp11 = bits - 1;
    tmp12 = 8 * tmp11;
    tmp13 = tmp12 + 5;
    tmp14 = NofibPrelude.Cons([
      0,
      circsim.F,
      false,
      0,
      true,
      tmp13
    ], NofibPrelude.Nil);
    tmp15 = circsim.PS(0, circsim.Inp, 0, NofibPrelude.Nil, tmp14);
    sto1 = tmp15;
    tmp16 = bits - 1;
    tmp17 = NofibPrelude.enumFromTo(0, tmp16);
    tmp18 = NofibPrelude.map(lambda21, tmp17);
    tmp19 = NofibPrelude.map(lambda22, tmp18);
    tmp20 = NofibPrelude.concat(tmp19);
    tmp21 = NofibPrelude.Cons(sto1, tmp20);
    states4 = tmp21;
    tmp22 = 7 * bits;
    tmp23 = 1 + tmp22;
    return [
      tmp23,
      is_,
      os,
      states4
    ]
  } 
  static circuit_simulate(inputs_list1, circuit) {
    let tmp;
    tmp = circsim.simulate(inputs_list1, circuit);
    return NofibPrelude.map(circsim.collect_outputs, tmp)
  } 
  static run(num_bits, num_cycles) {
    let example, inputs1, cycles, tmp, tmp1, tmp2, tmp3, tmp4;
    tmp = circsim.regs(num_bits);
    tmp1 = circsim.pad_circuit(tmp);
    example = tmp1;
    tmp2 = num_bits + 1;
    tmp3 = NofibPrelude.replicate(tmp2, circsim.T);
    inputs1 = tmp3;
    tmp4 = NofibPrelude.replicate(num_cycles, inputs1);
    cycles = tmp4;
    return circsim.circuit_simulate(cycles, example)
  } 
  static testCircsim_nofib(n1) {
    return circsim.run(8, n1)
  }
  static toString() { return "circsim"; }
};
let circsim = circsim1; export default circsim;
