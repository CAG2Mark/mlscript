import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let pad_circuit, update_outports, apply_component, downsweep, send_right, put, updateOutports, regs, simulate, simulate_component, compType, critical_path_depth, upsweep, check_right, reg, acknowledge, update_io, Componenet1, update_o, sweep_ud, testCircsim_nofib, do_sends, inports, T1, outports, scanlr, run, restore_requests, Or21, pathDepth, F1, Boolean1, Xor1, Node1, BinTree1, init_dffs, update_requests, simulate_components, Inv1, nearest_power_of_two, Cell1, Outp1, check_left, make_packet, pid, xor, update_i, circuit_simulate, Inp1, scanR, None_1, pad_packets, send_left, get, compare_and_update, inv, Unit1, scanL, and2, Dff1, updateInports, check_depth, store_inputs, collect_outputs, do_cycle, up_i, or2, PS1, do_send, And21, send, emptyState, emptyPacket, tmp, tmp1, tmp2, tmp3, tmp4, lambda;
pid = function pid(p) {
  return p.pid
};
compType = function compType(p) {
  return p.compType
};
pathDepth = function pathDepth(p) {
  return p.pathDepth
};
inports = function inports(p) {
  return p.inports
};
outports = function outports(p) {
  return p.outports
};
updateOutports = function updateOutports(p, noutports) {
  let tmp5, tmp6, tmp7, tmp8;
  tmp5 = pid(p);
  tmp6 = compType(p);
  tmp7 = pathDepth(p);
  tmp8 = inports(p);
  return PS1(tmp5, tmp6, tmp7, tmp8, noutports)
};
updateInports = function updateInports(p, ninports) {
  let tmp5, tmp6, tmp7, tmp8;
  tmp5 = pid(p);
  tmp6 = compType(p);
  tmp7 = pathDepth(p);
  tmp8 = outports(p);
  return PS1(tmp5, tmp6, tmp7, ninports, tmp8)
};
put = function put(xs) {
  let scrut, first1, first0, fstHalf, sndHalf, param0, param1, x, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12;
  if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return Cell1(x)
    } else {
      tmp5 = NofibPrelude.listLen(xs);
      tmp6 = NofibPrelude.intDiv(tmp5, 2);
      scrut = NofibPrelude.splitAt(tmp6, xs);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        fstHalf = first0;
        sndHalf = first1;
        tmp7 = put(fstHalf);
        tmp8 = put(sndHalf);
        return Node1(Unit1, tmp7, tmp8)
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } else {
    tmp9 = NofibPrelude.listLen(xs);
    tmp10 = NofibPrelude.intDiv(tmp9, 2);
    scrut = NofibPrelude.splitAt(tmp10, xs);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      fstHalf = first0;
      sndHalf = first1;
      tmp11 = put(fstHalf);
      tmp12 = put(sndHalf);
      return Node1(Unit1, tmp11, tmp12)
    } else {
      throw new globalThis.Error("match error");
    }
  }
};
get = function get(t) {
  let param0, param1, param2, l, r, param01, x, tmp5, tmp6;
  if (t instanceof Cell1.class) {
    param01 = t.value;
    x = param01;
    return NofibPrelude.Cons(x, NofibPrelude.Nil)
  } else if (t instanceof Node1.class) {
    param0 = t.value;
    param1 = t.left;
    param2 = t.right;
    l = param1;
    r = param2;
    tmp5 = get(l);
    tmp6 = get(r);
    return NofibPrelude.append(tmp5, tmp6)
  } else {
    throw new globalThis.Error("match error");
  }
};
upsweep = function upsweep(f, t) {
  let param0, param1, param2, x, l, r, scrut, first1, first0, lv, l_, scrut1, first11, first01, rv, r_, param01, a, tmp5, tmp6, tmp7;
  if (t instanceof Cell1.class) {
    param01 = t.value;
    a = param01;
    tmp5 = Cell1(a);
    return [
      a,
      tmp5
    ]
  } else if (t instanceof Node1.class) {
    param0 = t.value;
    param1 = t.left;
    param2 = t.right;
    x = param0;
    l = param1;
    r = param2;
    scrut = upsweep(f, l);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      lv = first0;
      l_ = first1;
      scrut1 = upsweep(f, r);
      if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
        first01 = scrut1[0];
        first11 = scrut1[1];
        rv = first01;
        r_ = first11;
        tmp6 = runtime.safeCall(f(lv, rv));
        tmp7 = Node1([
          lv,
          rv
        ], l_, r_);
        return [
          tmp6,
          tmp7
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
downsweep = function downsweep(g, d, t) {
  let param0, param1, param2, first1, first0, lv, rv, l, r, scrut, first11, first01, dl, dr, param01, x, tmp5, tmp6;
  if (t instanceof Cell1.class) {
    param01 = t.value;
    x = param01;
    return Cell1(d)
  } else if (t instanceof Node1.class) {
    param0 = t.value;
    param1 = t.left;
    param2 = t.right;
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
        tmp5 = downsweep(g, dl, l);
        tmp6 = downsweep(g, dr, r);
        return Node1(Unit1, tmp5, tmp6)
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
sweep_ud = function sweep_ud(up, down, u, t) {
  let scrut, first1, first0, ans, t_, tmp5;
  scrut = upsweep(up, t);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    ans = first0;
    t_ = first1;
    tmp5 = downsweep(down, u, t_);
    return [
      ans,
      tmp5
    ]
  } else {
    throw new globalThis.Error("match error");
  }
};
scanL = function scanL(f, u, xs) {
  let down1, scrut, first1, first0, up_ans, t_, tmp5, tmp6;
  down1 = function down1(l, r, x) {
    let tmp7;
    tmp7 = runtime.safeCall(f(x, l));
    return [
      x,
      tmp7
    ]
  };
  tmp5 = put(xs);
  scrut = sweep_ud(f, down1, u, tmp5);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    up_ans = first0;
    t_ = first1;
    tmp6 = get(t_);
    return [
      up_ans,
      tmp6
    ]
  } else {
    throw new globalThis.Error("match error");
  }
};
scanR = function scanR(f, u, xs) {
  let down2, scrut, first1, first0, up_ans, t_, tmp5, tmp6;
  down2 = function down2(l, r, x) {
    let tmp7;
    tmp7 = runtime.safeCall(f(r, x));
    return [
      tmp7,
      x
    ]
  };
  tmp5 = put(xs);
  scrut = sweep_ud(f, down2, u, tmp5);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    up_ans = first0;
    t_ = first1;
    tmp6 = get(t_);
    return [
      up_ans,
      tmp6
    ]
  } else {
    throw new globalThis.Error("match error");
  }
};
scanlr = function scanlr(f, g, lu, ru, xs) {
  let down3, up, xs_, scrut, first1, first0, first11, first01, l_ans, r_ans, t_, ans, tmp5, tmp6, tmp7, tmp8, tmp9, lambda1, lambda2, lambda3;
  up = function up(f1, g1, lxly, rxry) {
    let first12, first02, lx, ly, first13, first03, rx, ry, tmp10, tmp11;
    if (globalThis.Array.isArray(lxly) && lxly.length === 2) {
      first02 = lxly[0];
      first12 = lxly[1];
      lx = first02;
      ly = first12;
      if (globalThis.Array.isArray(rxry) && rxry.length === 2) {
        first03 = rxry[0];
        first13 = rxry[1];
        rx = first03;
        ry = first13;
        tmp10 = runtime.safeCall(f1(lx, rx));
        tmp11 = runtime.safeCall(g1(ly, ry));
        return [
          tmp10,
          tmp11
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  down3 = function down3(f1, g1, lxly, rxry, ab) {
    let first12, first02, lx, ly, first13, first03, rx, ry, first14, first04, a, b, tmp10, tmp11;
    if (globalThis.Array.isArray(lxly) && lxly.length === 2) {
      first02 = lxly[0];
      first12 = lxly[1];
      lx = first02;
      ly = first12;
      if (globalThis.Array.isArray(rxry) && rxry.length === 2) {
        first03 = rxry[0];
        first13 = rxry[1];
        rx = first03;
        ry = first13;
        if (globalThis.Array.isArray(ab) && ab.length === 2) {
          first04 = ab[0];
          first14 = ab[1];
          a = first04;
          b = first14;
          tmp10 = runtime.safeCall(g1(ry, b));
          tmp11 = runtime.safeCall(f1(a, lx));
          return [
            [
              a,
              tmp10
            ],
            [
              tmp11,
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
  lambda1 = (undefined, function (x) {
    return [
      x,
      x
    ]
  });
  tmp5 = NofibPrelude.map(lambda1, xs);
  xs_ = tmp5;
  tmp6 = put(xs_);
  lambda2 = (undefined, function (a, b) {
    return up(f, g, a, b)
  });
  lambda3 = (undefined, function (a, b, c) {
    return down3(f, g, a, b, c)
  });
  scrut = sweep_ud(lambda2, lambda3, [
    lu,
    ru
  ], tmp6);
  if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
    first0 = scrut[0];
    first1 = scrut[1];
    if (globalThis.Array.isArray(first0) && first0.length === 2) {
      first01 = first0[0];
      first11 = first0[1];
      l_ans = first01;
      r_ans = first11;
      t_ = first1;
      tmp7 = runtime.safeCall(g(r_ans, ru));
      tmp8 = runtime.safeCall(f(lu, l_ans));
      ans = [
        tmp7,
        tmp8
      ];
      tmp9 = get(t_);
      return [
        ans,
        tmp9
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
nearest_power_of_two = function nearest_power_of_two(x) {
  let lambda1, lambda2;
  lambda1 = (undefined, function (a) {
    return a >= x
  });
  lambda2 = (undefined, function (a) {
    return a * 2
  });
  return NofibPrelude.until(lambda1, lambda2, 1)
};
pad_circuit = function pad_circuit(size_ins_outs_states) {
  let first3, first2, first1, first0, size, ins, outs, states, p2, states_, tmp5, tmp6, tmp7, tmp8;
  if (globalThis.Array.isArray(size_ins_outs_states) && size_ins_outs_states.length === 4) {
    first0 = size_ins_outs_states[0];
    first1 = size_ins_outs_states[1];
    first2 = size_ins_outs_states[2];
    first3 = size_ins_outs_states[3];
    size = first0;
    ins = first1;
    outs = first2;
    states = first3;
    tmp5 = nearest_power_of_two(size);
    p2 = tmp5;
    tmp6 = NofibPrelude.replicate_lz(p2, emptyState);
    tmp7 = NofibPrelude.append_nl_lz(states, tmp6);
    states_ = tmp7;
    tmp8 = NofibPrelude.take_lz(p2, states_);
    return [
      p2,
      ins,
      outs,
      tmp8
    ]
  } else {
    throw new globalThis.Error("match error");
  }
};
inv = function inv(x) {
  let scrut;
  scrut = x === T1;
  if (scrut === true) {
    return F1
  } else {
    return T1
  }
};
and2 = function and2(x, y) {
  let scrut, tmp5, tmp6;
  tmp5 = x === T1;
  tmp6 = y === T1;
  scrut = tmp5 && tmp6;
  if (scrut === true) {
    return T1
  } else {
    return F1
  }
};
or2 = function or2(x, y) {
  let scrut, tmp5, tmp6;
  tmp5 = x === T1;
  tmp6 = y === T1;
  scrut = tmp5 || tmp6;
  if (scrut === true) {
    return T1
  } else {
    return F1
  }
};
xor = function xor(x, y) {
  let scrut;
  scrut = x === y;
  if (scrut === true) {
    return T1
  } else {
    return F1
  }
};
send_right = function send_right(a, b) {
  let first7, first6, first5, first4, first3, first2, first1, first0, ia, sa, ma, qla, dla, qra, dra, ea, first71, first61, first51, first41, first31, first21, first11, first01, ib, sb, mb, qlb, dlb, qrb, drb, eb, scrut, tmp5, tmp6, tmp7, tmp8;
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
          tmp5 = dra - eb;
          tmp6 = ea + eb;
          return [
            ia,
            sa,
            ma,
            qla,
            dla,
            qra,
            tmp5,
            tmp6
          ]
        } else {
          tmp7 = ea + eb;
          return [
            ib,
            sb,
            mb,
            qlb,
            dlb,
            qrb,
            drb,
            tmp7
          ]
        }
      } else {
        tmp8 = ea + eb;
        return [
          ib,
          sb,
          mb,
          qlb,
          dlb,
          qrb,
          drb,
          tmp8
        ]
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
send_left = function send_left(a, b) {
  let first7, first6, first5, first4, first3, first2, first1, first0, ia, sa, ma, qla, dla, qra, dra, ea, first71, first61, first51, first41, first31, first21, first11, first01, ib, sb, mb, qlb, dlb, qrb, drb, eb, scrut, tmp5, tmp6, tmp7, tmp8;
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
      tmp5 = dlb > ea;
      scrut = qlb && tmp5;
      if (scrut === true) {
        tmp6 = dlb - ea;
        tmp7 = ea + eb;
        return [
          ib,
          sb,
          mb,
          qlb,
          tmp6,
          qrb,
          drb,
          tmp7
        ]
      } else {
        tmp8 = ea + eb;
        return [
          ia,
          sa,
          ma,
          qla,
          dla,
          qra,
          dra,
          tmp8
        ]
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
send = function send(xs) {
  return scanlr(send_right, send_left, emptyPacket, emptyPacket, xs)
};
update_outports = function update_outports(state, value) {
  let lscomp, tmp5, tmp6;
  lscomp = function lscomp(ls) {
    let param0, param1, h, t, first5, first4, first3, first2, first1, first0, p, m, ql, dl, qr, dr, tmp7;
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
        tmp7 = lscomp(t);
        return NofibPrelude.Cons([
          p,
          value,
          ql,
          dl,
          qr,
          dr
        ], tmp7)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp5 = outports(state);
  tmp6 = lscomp(tmp5);
  return updateOutports(state, tmp6)
};
critical_path_depth = function critical_path_depth(siot) {
  let first3, first2, first1, first0, size, ins, outs, states, tmp5;
  if (globalThis.Array.isArray(siot) && siot.length === 4) {
    first0 = siot[0];
    first1 = siot[1];
    first2 = siot[2];
    first3 = siot[3];
    size = first0;
    ins = first1;
    outs = first2;
    states = first3;
    tmp5 = NofibPrelude.map(pathDepth, states);
    return NofibPrelude.maximum(tmp5)
  } else {
    throw new globalThis.Error("match error");
  }
};
collect_outputs = function collect_outputs(tp4) {
  let thrid, get_output, first3, first2, first1, first0, size, ins, outs, states, lambda1;
  if (globalThis.Array.isArray(tp4) && tp4.length === 4) {
    first0 = tp4[0];
    first1 = tp4[1];
    first2 = tp4[2];
    first3 = tp4[3];
    size = first0;
    ins = first1;
    outs = first2;
    states = first3;
    thrid = function thrid(tp3) {
      let first21, first11, first01, v;
      if (globalThis.Array.isArray(tp3) && tp3.length === 3) {
        first01 = tp3[0];
        first11 = tp3[1];
        first21 = tp3[2];
        v = first21;
        return v
      } else {
        throw new globalThis.Error("match error");
      }
    };
    get_output = function get_output(states1, label_p) {
      let lscomp, first11, first01, label, p, tmp5, tmp6;
      if (globalThis.Array.isArray(label_p) && label_p.length === 2) {
        first01 = label_p[0];
        first11 = label_p[1];
        label = first01;
        p = first11;
        lscomp = function lscomp(ls) {
          let param0, param1, s, t, scrut, tmp7, tmp8, tmp9, tmp10;
          if (ls instanceof NofibPrelude.Nil.class) {
            return NofibPrelude.Nil
          } else if (ls instanceof NofibPrelude.Cons.class) {
            param0 = ls.head;
            param1 = ls.tail;
            s = param0;
            t = param1;
            tmp7 = pid(s);
            scrut = p == tmp7;
            if (scrut === true) {
              tmp8 = inports(s);
              tmp9 = NofibPrelude.head(tmp8);
              tmp10 = lscomp(t);
              return NofibPrelude.Cons(tmp9, tmp10)
            } else {
              return lscomp(t)
            }
          } else {
            throw new globalThis.Error("match error");
          }
        };
        tmp5 = lscomp(states1);
        tmp6 = NofibPrelude.head(tmp5);
        return thrid(tmp6)
      } else {
        throw new globalThis.Error("match error");
      }
    };
    lambda1 = (undefined, function (p) {
      return get_output(states, p)
    });
    return NofibPrelude.map(lambda1, outs)
  } else {
    throw new globalThis.Error("match error");
  }
};
store_inputs = function store_inputs(label_inputs, state) {
  let lscomp, param0, param1, param2, param3, param4, pid_, tmp5;
  if (state instanceof PS1.class) {
    param0 = state.pid;
    param1 = state.compType;
    param2 = state.pathDepth;
    param3 = state.inports;
    param4 = state.outports;
    pid_ = param0;
    if (param1 instanceof Inp1.class) {
      lscomp = function lscomp(ls) {
        let param01, param11, h, t, first1, first0, first11, first01, label, input_pid, value, scrut, tmp6, tmp7;
        if (ls instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (ls instanceof NofibPrelude.Cons.class) {
          param01 = ls.head;
          param11 = ls.tail;
          h = param01;
          t = param11;
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
                tmp6 = update_outports(state, value);
                tmp7 = lscomp(t);
                return NofibPrelude.Cons(tmp6, tmp7)
              } else {
                return lscomp(t)
              }
            } else {
              return lscomp(t)
            }
          } else {
            return lscomp(t)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      };
      tmp5 = lscomp(label_inputs);
      return NofibPrelude.head(tmp5)
    } else {
      return state
    }
  } else {
    return state
  }
};
apply_component = function apply_component(comp, signals) {
  let param0, param1, x, param01, param11, y, x1, y1, x2, y2, x3, x4, x5, tmp5, tmp6, tmp7, tmp8;
  if (comp instanceof Inp1.class) {
    return NofibPrelude.None
  } else if (comp instanceof Outp1.class) {
    if (signals instanceof NofibPrelude.Cons.class) {
      param0 = signals.head;
      param1 = signals.tail;
      x5 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Some(x5)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else if (comp instanceof Dff1.class) {
    if (signals instanceof NofibPrelude.Cons.class) {
      param0 = signals.head;
      param1 = signals.tail;
      x4 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Some(x4)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else if (comp instanceof Inv1.class) {
    if (signals instanceof NofibPrelude.Cons.class) {
      param0 = signals.head;
      param1 = signals.tail;
      x3 = param0;
      if (param1 instanceof NofibPrelude.Nil.class) {
        tmp5 = inv(x3);
        return NofibPrelude.Some(tmp5)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else if (comp instanceof And21.class) {
    if (signals instanceof NofibPrelude.Cons.class) {
      param0 = signals.head;
      param1 = signals.tail;
      x2 = param0;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        y2 = param01;
        if (param11 instanceof NofibPrelude.Nil.class) {
          tmp6 = and2(x2, y2);
          return NofibPrelude.Some(tmp6)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else if (comp instanceof Or21.class) {
    if (signals instanceof NofibPrelude.Cons.class) {
      param0 = signals.head;
      param1 = signals.tail;
      x1 = param0;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        y1 = param01;
        if (param11 instanceof NofibPrelude.Nil.class) {
          tmp7 = or2(x1, y1);
          return NofibPrelude.Some(tmp7)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else if (comp instanceof Xor1.class) {
    if (signals instanceof NofibPrelude.Cons.class) {
      param0 = signals.head;
      param1 = signals.tail;
      x = param0;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        y = param01;
        if (param11 instanceof NofibPrelude.Nil.class) {
          tmp8 = xor(x, y);
          return NofibPrelude.Some(tmp8)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else if (comp instanceof None_1.class) {
    return NofibPrelude.None
  } else {
    throw new globalThis.Error("match error");
  }
};
init_dffs = function init_dffs(state) {
  let scrut, tmp5;
  tmp5 = compType(state);
  scrut = tmp5 === Dff1;
  if (scrut === true) {
    return update_outports(state, F1)
  } else {
    return state
  }
};
restore_requests = function restore_requests(old_states, new_states) {
  let restore_outport, restore;
  restore = function restore(os, ns) {
    let tmp5, tmp6, tmp7;
    tmp5 = outports(os);
    tmp6 = outports(ns);
    tmp7 = NofibPrelude.zipWith(restore_outport, tmp5, tmp6);
    return updateOutports(ns, tmp7)
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
  return NofibPrelude.zipWith(restore, old_states, new_states)
};
update_requests = function update_requests(b, state) {
  let lscomp, tmp5, tmp6;
  lscomp = function lscomp(ls) {
    let param0, param1, h, t, first5, first4, first3, first2, first1, first0, p, m, ql, dl, qr, dr, tmp7;
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
        tmp7 = lscomp(t);
        return NofibPrelude.Cons([
          p,
          m,
          b,
          dl,
          b,
          dr
        ], tmp7)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp5 = outports(state);
  tmp6 = lscomp(tmp5);
  return updateOutports(state, tmp6)
};
check_depth = function check_depth(d, state) {
  let scrut, tmp5;
  tmp5 = pathDepth(state);
  scrut = tmp5 == d;
  if (scrut === true) {
    return state
  } else {
    return update_requests(false, state)
  }
};
acknowledge = function acknowledge(d, states) {
  let check_requests, check_lr_requests, states1, tmp5, tmp6, tmp7, lambda1, lambda2;
  check_requests = function check_requests(xs) {
    let tmp8;
    tmp8 = NofibPrelude.map(check_lr_requests, xs);
    return NofibPrelude.orList(tmp8)
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
  lambda1 = (undefined, function (s) {
    return check_depth(d, s)
  });
  tmp5 = NofibPrelude.map(lambda1, states);
  states1 = tmp5;
  lambda2 = (undefined, function (s) {
    let tmp8;
    tmp8 = outports(s);
    return check_requests(tmp8)
  });
  tmp6 = NofibPrelude.map(lambda2, states1);
  tmp7 = NofibPrelude.orList(tmp6);
  return BenchmarkPrelude.not(tmp7)
};
pad_packets = function pad_packets(pss) {
  let pad, lambda1;
  pad = function pad(xs) {
    let max_ps, tmp5, tmp6, tmp7, tmp8, lambda2;
    lambda2 = (undefined, function (x) {
      return NofibPrelude.listLen(x)
    });
    tmp5 = NofibPrelude.map(lambda2, pss);
    tmp6 = NofibPrelude.maximum(tmp5);
    max_ps = tmp6;
    tmp7 = NofibPrelude.replicate_lz(max_ps, emptyPacket);
    tmp8 = NofibPrelude.append_nl_lz(xs, tmp7);
    return NofibPrelude.take_lz(max_ps, tmp8)
  };
  lambda1 = (undefined, function (x) {
    return pad(x)
  });
  return NofibPrelude.map(lambda1, pss)
};
make_packet = function make_packet(state) {
  let lscomp, tmp5;
  lscomp = function lscomp(ls) {
    let param0, param1, h, t, first5, first4, first3, first2, first1, first0, p, m, ql, dl, qr, dr, tmp6, tmp7;
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
        tmp6 = pid(state);
        tmp7 = lscomp(t);
        return NofibPrelude.Cons([
          tmp6,
          p,
          m,
          ql,
          dl,
          qr,
          dr,
          1
        ], tmp7)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp5 = outports(state);
  return lscomp(tmp5)
};
compare_and_update = function compare_and_update(ipm_, pid_port_m) {
  let first2, first1, first0, i, p, m_, first21, first11, first01, pid_, port, m, scrut;
  if (globalThis.Array.isArray(ipm_) && ipm_.length === 3) {
    first0 = ipm_[0];
    first1 = ipm_[1];
    first2 = ipm_[2];
    i = first0;
    p = first1;
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
        p
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
};
up_i = function up_i(ipm_, ins) {
  let first7, first6, first5, first4, first3, first2, first1, first0, i, p, m_, lambda1;
  if (globalThis.Array.isArray(ipm_) && ipm_.length === 8) {
    first0 = ipm_[0];
    first1 = ipm_[1];
    first2 = ipm_[2];
    first3 = ipm_[3];
    first4 = ipm_[4];
    first5 = ipm_[5];
    first6 = ipm_[6];
    first7 = ipm_[7];
    i = first0;
    p = first1;
    m_ = first2;
    lambda1 = (undefined, function (x) {
      return compare_and_update([
        i,
        p,
        m_
      ], x)
    });
    return NofibPrelude.map(lambda1, ins)
  } else {
    throw new globalThis.Error("match error");
  }
};
update_i = function update_i(l_r, ins) {
  let first1, first0, l, r, tmp5;
  if (globalThis.Array.isArray(l_r) && l_r.length === 2) {
    first0 = l_r[0];
    first1 = l_r[1];
    l = first0;
    r = first1;
    tmp5 = up_i(r, ins);
    return up_i(l, tmp5)
  } else {
    throw new globalThis.Error("match error");
  }
};
check_left = function check_left(a, b) {
  let first7, first6, first5, first4, first3, first2, first1, first0, pid_, port, pm, pql, pdl, pqr, pdr, e, first51, first41, first31, first21, first11, first01, p, m, ql, dl, qr, dr, scrut, tmp5;
  if (globalThis.Array.isArray(a) && a.length === 8) {
    first0 = a[0];
    first1 = a[1];
    first2 = a[2];
    first3 = a[3];
    first4 = a[4];
    first5 = a[5];
    first6 = a[6];
    first7 = a[7];
    pid_ = first0;
    port = first1;
    pm = first2;
    pql = first3;
    pdl = first4;
    pqr = first5;
    pdr = first6;
    e = first7;
    if (globalThis.Array.isArray(b) && b.length === 6) {
      first01 = b[0];
      first11 = b[1];
      first21 = b[2];
      first31 = b[3];
      first41 = b[4];
      first51 = b[5];
      p = first01;
      m = first11;
      ql = first21;
      dl = first31;
      qr = first41;
      dr = first51;
      tmp5 = pdr > 0;
      scrut = pqr && tmp5;
      if (scrut === true) {
        return [
          p,
          m,
          ql,
          dl,
          qr,
          dr
        ]
      } else {
        return [
          p,
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
};
check_right = function check_right(a, b) {
  let first7, first6, first5, first4, first3, first2, first1, first0, pid_, port, pm, pql, pdl, pqr, pdr, e, first51, first41, first31, first21, first11, first01, p, m, ql, dl, qr, dr, scrut, tmp5;
  if (globalThis.Array.isArray(a) && a.length === 8) {
    first0 = a[0];
    first1 = a[1];
    first2 = a[2];
    first3 = a[3];
    first4 = a[4];
    first5 = a[5];
    first6 = a[6];
    first7 = a[7];
    pid_ = first0;
    port = first1;
    pm = first2;
    pql = first3;
    pdl = first4;
    pqr = first5;
    pdr = first6;
    e = first7;
    if (globalThis.Array.isArray(b) && b.length === 6) {
      first01 = b[0];
      first11 = b[1];
      first21 = b[2];
      first31 = b[3];
      first41 = b[4];
      first51 = b[5];
      p = first01;
      m = first11;
      ql = first21;
      dl = first31;
      qr = first41;
      dr = first51;
      tmp5 = pdl > 0;
      scrut = pql && tmp5;
      if (scrut === true) {
        return [
          p,
          m,
          ql,
          dl,
          qr,
          dr
        ]
      } else {
        return [
          p,
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
};
update_o = function update_o(lp_rp, out_) {
  let first1, first0, lp, rp, tmp5;
  if (globalThis.Array.isArray(lp_rp) && lp_rp.length === 2) {
    first0 = lp_rp[0];
    first1 = lp_rp[1];
    lp = first0;
    rp = first1;
    tmp5 = check_right(rp, out_);
    return check_left(lp, tmp5)
  } else {
    throw new globalThis.Error("match error");
  }
};
update_io = function update_io(d, lrps, state) {
  let update_is, update_os, tmp5;
  update_is = function update_is(state1) {
    let tmp6, tmp7;
    tmp6 = inports(state1);
    tmp7 = NofibPrelude.foldr(update_i, tmp6, lrps);
    return updateInports(state1, tmp7)
  };
  update_os = function update_os(state1) {
    let scrut, tmp6, tmp7, tmp8;
    tmp6 = pathDepth(state1);
    scrut = tmp6 == d;
    if (scrut === true) {
      tmp7 = outports(state1);
      tmp8 = NofibPrelude.zipWith(update_o, lrps, tmp7);
      return updateOutports(state1, tmp8)
    } else {
      return state1
    }
  };
  tmp5 = update_is(state);
  return update_os(tmp5)
};
do_send = function do_send(d, states) {
  let states1, send_results, pss_, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, lambda1, lambda2, lambda3;
  lambda1 = (undefined, function (s) {
    return check_depth(d, s)
  });
  tmp5 = NofibPrelude.map(lambda1, states);
  states1 = tmp5;
  tmp6 = NofibPrelude.map(make_packet, states1);
  tmp7 = pad_packets(tmp6);
  tmp8 = NofibPrelude.transpose(tmp7);
  lambda2 = (undefined, function (x) {
    let tmp11;
    tmp11 = send(x);
    return NofibPrelude.snd(tmp11)
  });
  tmp9 = NofibPrelude.map(lambda2, tmp8);
  send_results = tmp9;
  tmp10 = NofibPrelude.transpose(send_results);
  pss_ = tmp10;
  lambda3 = (undefined, function (x, y) {
    return update_io(d, x, y)
  });
  return NofibPrelude.zipWith(lambda3, pss_, states)
};
do_sends = function do_sends(d, states) {
  let lambda1, lambda2;
  lambda1 = (undefined, function (s) {
    return acknowledge(d, s)
  });
  lambda2 = (undefined, function (x) {
    return do_send(d, x)
  });
  return NofibPrelude.until(lambda1, lambda2, states)
};
simulate_component = function simulate_component(d, state) {
  let lscomp, out_signals, new_value, scrut, scrut1, param0, v, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10;
  lscomp = function lscomp(ls) {
    let param01, param1, h, t, first2, first1, first0, sig, tmp11;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param01 = ls.head;
      param1 = ls.tail;
      h = param01;
      t = param1;
      if (globalThis.Array.isArray(h) && h.length === 3) {
        first0 = h[0];
        first1 = h[1];
        first2 = h[2];
        sig = first2;
        tmp11 = lscomp(t);
        return NofibPrelude.Cons(sig, tmp11)
      } else {
        return lscomp(t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp5 = inports(state);
  tmp6 = lscomp(tmp5);
  out_signals = tmp6;
  tmp7 = compType(state);
  tmp8 = apply_component(tmp7, out_signals);
  new_value = tmp8;
  tmp9 = pathDepth(state);
  scrut = d == tmp9;
  if (scrut === true) {
    tmp10 = new_value === NofibPrelude.None;
    scrut1 = BenchmarkPrelude.not(tmp10);
    if (scrut1 === true) {
      if (new_value instanceof NofibPrelude.Some.class) {
        param0 = new_value.x;
        v = param0;
        return update_outports(state, v)
      } else {
        return state
      }
    } else {
      return state
    }
  } else {
    return state
  }
};
simulate_components = function simulate_components(depth, states) {
  let lambda1;
  lambda1 = (undefined, function (s) {
    return simulate_component(depth, s)
  });
  return NofibPrelude.map(lambda1, states)
};
do_cycle = function do_cycle(cpd, tp4, inputs) {
  let sim_then_send, first3, first2, first1, first0, size, ins, outs, states, states1, states2, states3, states4, tmp5, tmp6, tmp7, tmp8, tmp9, lambda1;
  sim_then_send = function sim_then_send(state, d) {
    let tmp10;
    tmp10 = simulate_components(d, state);
    return do_sends(d, tmp10)
  };
  if (globalThis.Array.isArray(tp4) && tp4.length === 4) {
    first0 = tp4[0];
    first1 = tp4[1];
    first2 = tp4[2];
    first3 = tp4[3];
    size = first0;
    ins = first1;
    outs = first2;
    states = first3;
    lambda1 = (undefined, function (s) {
      let tmp10;
      tmp10 = NofibPrelude.zip(ins, inputs);
      return store_inputs(tmp10, s)
    });
    tmp5 = NofibPrelude.map(lambda1, states);
    states1 = tmp5;
    tmp6 = do_sends(0, states1);
    states2 = tmp6;
    tmp7 = NofibPrelude.enumFromTo(1, cpd);
    tmp8 = NofibPrelude.foldl(sim_then_send, states2, tmp7);
    states3 = tmp8;
    tmp9 = restore_requests(states, states3);
    states4 = tmp9;
    return [
      size,
      ins,
      outs,
      states4
    ]
  } else {
    throw globalThis.Error(tp4);
  }
};
simulate = function simulate(inputs_list, b) {
  let first3, first2, first1, first0, size, ins, outs, states, tmp5, tmp6, lambda1;
  if (globalThis.Array.isArray(b) && b.length === 4) {
    first0 = b[0];
    first1 = b[1];
    first2 = b[2];
    first3 = b[3];
    size = first0;
    ins = first1;
    outs = first2;
    states = first3;
    tmp5 = NofibPrelude.map(init_dffs, states);
    lambda1 = (undefined, function (x, y) {
      let tmp7;
      tmp7 = critical_path_depth([
        size,
        ins,
        outs,
        states
      ]);
      return do_cycle(tmp7, x, y)
    });
    tmp6 = NofibPrelude.scanl(lambda1, [
      size,
      ins,
      outs,
      tmp5
    ], inputs_list);
    return NofibPrelude.tail(tmp6)
  } else {
    throw new globalThis.Error("match error");
  }
};
reg = function reg(sto, n) {
  let tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44;
  tmp5 = NofibPrelude.Cons([
    0,
    F1,
    false,
    0,
    true,
    4
  ], NofibPrelude.Nil);
  tmp6 = PS1(n, Inp1, 0, NofibPrelude.Nil, tmp5);
  tmp7 = n + 1;
  tmp8 = n + 5;
  tmp9 = NofibPrelude.Cons([
    tmp8,
    0,
    F1
  ], NofibPrelude.Nil);
  tmp10 = NofibPrelude.Cons([
    0,
    F1,
    false,
    0,
    true,
    5
  ], NofibPrelude.Nil);
  tmp11 = PS1(tmp7, Dff1, 1, tmp9, tmp10);
  tmp12 = n + 2;
  tmp13 = NofibPrelude.Cons([
    sto,
    0,
    F1
  ], NofibPrelude.Nil);
  tmp14 = NofibPrelude.Cons([
    0,
    F1,
    false,
    0,
    true,
    1
  ], NofibPrelude.Nil);
  tmp15 = PS1(tmp12, Inv1, 1, tmp13, tmp14);
  tmp16 = n + 3;
  tmp17 = n + 1;
  tmp18 = n + 2;
  tmp19 = NofibPrelude.Cons([
    tmp18,
    0,
    F1
  ], NofibPrelude.Nil);
  tmp20 = NofibPrelude.Cons([
    tmp17,
    0,
    F1
  ], tmp19);
  tmp21 = NofibPrelude.Cons([
    0,
    F1,
    false,
    0,
    true,
    2
  ], NofibPrelude.Nil);
  tmp22 = PS1(tmp16, And21, 2, tmp20, tmp21);
  tmp23 = n + 4;
  tmp24 = NofibPrelude.Cons([
    n,
    0,
    F1
  ], NofibPrelude.Nil);
  tmp25 = NofibPrelude.Cons([
    sto,
    0,
    F1
  ], tmp24);
  tmp26 = NofibPrelude.Cons([
    0,
    F1,
    false,
    0,
    true,
    1
  ], NofibPrelude.Nil);
  tmp27 = PS1(tmp23, And21, 1, tmp25, tmp26);
  tmp28 = n + 5;
  tmp29 = n + 3;
  tmp30 = n + 4;
  tmp31 = NofibPrelude.Cons([
    tmp30,
    0,
    F1
  ], NofibPrelude.Nil);
  tmp32 = NofibPrelude.Cons([
    tmp29,
    0,
    F1
  ], tmp31);
  tmp33 = NofibPrelude.Cons([
    0,
    F1,
    true,
    4,
    false,
    0
  ], NofibPrelude.Nil);
  tmp34 = PS1(tmp28, Or21, 3, tmp32, tmp33);
  tmp35 = n + 6;
  tmp36 = n + 1;
  tmp37 = NofibPrelude.Cons([
    tmp36,
    0,
    F1
  ], NofibPrelude.Nil);
  tmp38 = PS1(tmp35, Outp1, 4, tmp37, NofibPrelude.Nil);
  tmp39 = NofibPrelude.Cons(tmp38, NofibPrelude.Nil);
  tmp40 = NofibPrelude.Cons(tmp34, tmp39);
  tmp41 = NofibPrelude.Cons(tmp27, tmp40);
  tmp42 = NofibPrelude.Cons(tmp22, tmp41);
  tmp43 = NofibPrelude.Cons(tmp15, tmp42);
  tmp44 = NofibPrelude.Cons(tmp11, tmp43);
  return NofibPrelude.Cons(tmp6, tmp44)
};
regs = function regs(bits) {
  let ilabel, olabel, is_, os, sto, states, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, lambda1, lambda2, lambda3, lambda4;
  ilabel = function ilabel(n, pid_) {
    let tmp29, tmp30;
    tmp29 = NofibPrelude.stringOfInt(n);
    tmp30 = NofibPrelude.stringConcat("x", tmp29);
    return [
      tmp30,
      pid_
    ]
  };
  olabel = function olabel(n, pid_) {
    let tmp29, tmp30;
    tmp29 = NofibPrelude.stringOfInt(n);
    tmp30 = NofibPrelude.stringConcat("y", tmp29);
    return [
      tmp30,
      pid_
    ]
  };
  tmp5 = NofibPrelude.enumFrom(0);
  tmp6 = bits - 1;
  tmp7 = NofibPrelude.enumFromTo(0, tmp6);
  lambda1 = (undefined, function (x) {
    let tmp29;
    tmp29 = 7 * x;
    return tmp29 + 1
  });
  tmp8 = NofibPrelude.map(lambda1, tmp7);
  tmp9 = NofibPrelude.zipWith_lz_nl(ilabel, tmp5, tmp8);
  tmp10 = NofibPrelude.Cons([
    "sto",
    0
  ], tmp9);
  is_ = tmp10;
  tmp11 = NofibPrelude.enumFrom(0);
  tmp12 = bits - 1;
  tmp13 = NofibPrelude.enumFromTo(0, tmp12);
  lambda2 = (undefined, function (x) {
    let tmp29;
    tmp29 = 7 * x;
    return tmp29 + 7
  });
  tmp14 = NofibPrelude.map(lambda2, tmp13);
  tmp15 = NofibPrelude.zipWith_lz_nl(olabel, tmp11, tmp14);
  os = tmp15;
  tmp16 = bits - 1;
  tmp17 = 8 * tmp16;
  tmp18 = tmp17 + 5;
  tmp19 = NofibPrelude.Cons([
    0,
    F1,
    false,
    0,
    true,
    tmp18
  ], NofibPrelude.Nil);
  tmp20 = PS1(0, Inp1, 0, NofibPrelude.Nil, tmp19);
  sto = tmp20;
  tmp21 = bits - 1;
  tmp22 = NofibPrelude.enumFromTo(0, tmp21);
  lambda3 = (undefined, function (x) {
    let tmp29;
    tmp29 = 7 * x;
    return tmp29 + 1
  });
  tmp23 = NofibPrelude.map(lambda3, tmp22);
  lambda4 = (undefined, function (x) {
    return reg(0, x)
  });
  tmp24 = NofibPrelude.map(lambda4, tmp23);
  tmp25 = NofibPrelude.concat(tmp24);
  tmp26 = NofibPrelude.Cons(sto, tmp25);
  states = tmp26;
  tmp27 = 7 * bits;
  tmp28 = 1 + tmp27;
  return [
    tmp28,
    is_,
    os,
    states
  ]
};
circuit_simulate = function circuit_simulate(inputs_list, circuit) {
  let tmp5;
  tmp5 = simulate(inputs_list, circuit);
  return NofibPrelude.map(collect_outputs, tmp5)
};
run = function run(num_bits, num_cycles) {
  let example, inputs, cycles, tmp5, tmp6, tmp7, tmp8, tmp9;
  tmp5 = regs(num_bits);
  tmp6 = pad_circuit(tmp5);
  example = tmp6;
  tmp7 = num_bits + 1;
  tmp8 = NofibPrelude.replicate(tmp7, T1);
  inputs = tmp8;
  tmp9 = NofibPrelude.replicate(num_cycles, inputs);
  cycles = tmp9;
  return circuit_simulate(cycles, example)
};
testCircsim_nofib = function testCircsim_nofib(n) {
  return run(8, n)
};
BinTree1 = class BinTree {
  constructor() {}
  toString() { return "BinTree"; }
};
Cell1 = function Cell(value1) {
  return new Cell.class(value1);
};
Cell1.class = class Cell extends BinTree1 {
  constructor(value) {
    super();
    this.value = value;
  }
  toString() { return "Cell(" + globalThis.Predef.render(this.value) + ")"; }
};
Node1 = function Node(value1, left1, right1) {
  return new Node.class(value1, left1, right1);
};
Node1.class = class Node extends BinTree1 {
  constructor(value, left, right) {
    super();
    this.value = value;
    this.left = left;
    this.right = right;
  }
  toString() { return "Node(" + globalThis.Predef.render(this.value) + ", " + globalThis.Predef.render(this.left) + ", " + globalThis.Predef.render(this.right) + ")"; }
};
Componenet1 = class Componenet {
  constructor() {}
  toString() { return "Componenet"; }
};
const None_$class = class None_ extends Componenet1 {
  constructor() {
    super();
  }
  toString() { return "None_"; }
}; None_1 = new None_$class;
None_1.class = None_$class;
const Inp$class = class Inp extends Componenet1 {
  constructor() {
    super();
  }
  toString() { return "Inp"; }
}; Inp1 = new Inp$class;
Inp1.class = Inp$class;
const Outp$class = class Outp extends Componenet1 {
  constructor() {
    super();
  }
  toString() { return "Outp"; }
}; Outp1 = new Outp$class;
Outp1.class = Outp$class;
const Dff$class = class Dff extends Componenet1 {
  constructor() {
    super();
  }
  toString() { return "Dff"; }
}; Dff1 = new Dff$class;
Dff1.class = Dff$class;
const Inv$class = class Inv extends Componenet1 {
  constructor() {
    super();
  }
  toString() { return "Inv"; }
}; Inv1 = new Inv$class;
Inv1.class = Inv$class;
const And2$class = class And2 extends Componenet1 {
  constructor() {
    super();
  }
  toString() { return "And2"; }
}; And21 = new And2$class;
And21.class = And2$class;
const Or2$class = class Or2 extends Componenet1 {
  constructor() {
    super();
  }
  toString() { return "Or2"; }
}; Or21 = new Or2$class;
Or21.class = Or2$class;
const Xor$class = class Xor extends Componenet1 {
  constructor() {
    super();
  }
  toString() { return "Xor"; }
}; Xor1 = new Xor$class;
Xor1.class = Xor$class;
const Unit$class = class Unit {
  constructor() {}
  toString() { return "Unit"; }
}; Unit1 = new Unit$class;
Unit1.class = Unit$class;
PS1 = function PS(pid2, compType2, pathDepth2, inports2, outports2) {
  return new PS.class(pid2, compType2, pathDepth2, inports2, outports2);
};
PS1.class = class PS {
  constructor(pid1, compType1, pathDepth1, inports1, outports1) {
    this.pid = pid1;
    this.compType = compType1;
    this.pathDepth = pathDepth1;
    this.inports = inports1;
    this.outports = outports1;
  }
  toString() { return "PS(" + globalThis.Predef.render(this.pid) + ", " + globalThis.Predef.render(this.compType) + ", " + globalThis.Predef.render(this.pathDepth) + ", " + globalThis.Predef.render(this.inports) + ", " + globalThis.Predef.render(this.outports) + ")"; }
};
Boolean1 = class Boolean {
  constructor() {}
  toString() { return "Boolean"; }
};
const F$class = class F extends Boolean1 {
  constructor() {
    super();
  }
  toString() { return "F"; }
}; F1 = new F$class;
F1.class = F$class;
const T$class = class T extends Boolean1 {
  constructor() {
    super();
  }
  toString() { return "T"; }
}; T1 = new T$class;
T1.class = T$class;
tmp = - 1;
tmp1 = - 1;
tmp2 = PS1(tmp, None_1, tmp1, NofibPrelude.Nil, NofibPrelude.Nil);
emptyState = tmp2;
tmp3 = - 1;
tmp4 = - 1;
emptyPacket = [
  tmp3,
  tmp4,
  F1,
  false,
  0,
  false,
  0,
  1
];
lambda = (undefined, function () {
  let tmp5;
  tmp5 = testCircsim_nofib(40);
  return runtime.safeCall(tmp5.toString())
});
BenchmarkPrelude.benchmark(lambda)