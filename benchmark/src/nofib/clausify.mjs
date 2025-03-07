import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let conjunct, insert, interleave, opri, clauseHelper, testClausify_nofib, Formula1, split, uniclHelper, Eqv1, Ast1, clause, spri, splitHelper, Con1, clauses, negin, charLt, Sym1, Imp1, elim, tautclause, StackFrame1, Lex1, disin, Dis1, charLeq, parse, unicl, disp, charGt, Not1, parseHelper, redstar, charGeq, spaces, red, lambda;
charLt = function charLt(a, b) {
  return a < b
};
charLeq = function charLeq(a, b) {
  return a <= b
};
charGt = function charGt(a, b) {
  return a > b
};
charGeq = function charGeq(a, b) {
  return a >= b
};
insert = function insert(x, ys) {
  let param0, param1, y, ys1, scrut, scrut1, tmp, tmp1;
  if (ys instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Cons(x, NofibPrelude.Nil)
  } else if (ys instanceof NofibPrelude.Cons.class) {
    param0 = ys.head;
    param1 = ys.tail;
    y = param0;
    ys1 = param1;
    scrut1 = charLt(x, y);
    if (scrut1 === true) {
      tmp = NofibPrelude.Cons(y, ys1);
      return NofibPrelude.Cons(x, tmp)
    } else {
      scrut = charGt(x, y);
      if (scrut === true) {
        tmp1 = insert(x, ys1);
        return NofibPrelude.Cons(y, tmp1)
      } else {
        return NofibPrelude.Cons(y, ys1)
      }
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
clauseHelper = function clauseHelper(p, x) {
  let param0, param01, s, first1, first0, c, a, param02, s1, c1, a1, param03, param1, p1, q, tmp, tmp1, tmp2;
  if (p instanceof Dis1.class) {
    param03 = p.a;
    param1 = p.b;
    p1 = param03;
    q = param1;
    tmp = clauseHelper(q, x);
    return clauseHelper(p1, tmp)
  } else if (p instanceof Sym1.class) {
    param02 = p.a;
    s1 = param02;
    if (globalThis.Array.isArray(x) && x.length === 2) {
      first0 = x[0];
      first1 = x[1];
      c1 = first0;
      a1 = first1;
      tmp1 = insert(s1, c1);
      return [
        tmp1,
        a1
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } else if (p instanceof Not1.class) {
    param0 = p.a;
    if (param0 instanceof Sym1.class) {
      param01 = param0.a;
      s = param01;
      if (globalThis.Array.isArray(x) && x.length === 2) {
        first0 = x[0];
        first1 = x[1];
        c = first0;
        a = first1;
        tmp2 = insert(s, a);
        return [
          c,
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
};
clause = function clause(p) {
  return clauseHelper(p, [
    NofibPrelude.Nil,
    NofibPrelude.Nil
  ])
};
conjunct = function conjunct(p) {
  let param0, param1;
  if (p instanceof Con1.class) {
    param0 = p.a;
    param1 = p.b;
    return true
  } else {
    return false
  }
};
disin = function disin(p) {
  let param0, param1, p1, q, param01, param11, p2, q1, dp, dq, scrut, param02, param12, p3, q2, r, p4, param03, param13, q3, r1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
  if (p instanceof Dis1.class) {
    param01 = p.a;
    param11 = p.b;
    p4 = param01;
    if (param11 instanceof Con1.class) {
      param03 = param11.a;
      param13 = param11.b;
      q3 = param03;
      r1 = param13;
      tmp = Dis1(p4, q3);
      tmp1 = disin(tmp);
      tmp2 = Dis1(p4, r1);
      tmp3 = disin(tmp2);
      return Con1(tmp1, tmp3)
    } else {
      if (param01 instanceof Con1.class) {
        param02 = param01.a;
        param12 = param01.b;
        p3 = param02;
        q2 = param12;
        r = param11;
        tmp4 = Dis1(p3, r);
        tmp5 = disin(tmp4);
        tmp6 = Dis1(q2, r);
        tmp7 = disin(tmp6);
        return Con1(tmp5, tmp7)
      } else {
        p2 = param01;
        q1 = param11;
        tmp8 = disin(p2);
        dp = tmp8;
        tmp9 = disin(q1);
        dq = tmp9;
        tmp10 = conjunct(dp);
        tmp11 = conjunct(dq);
        scrut = tmp10 || tmp11;
        if (scrut === true) {
          tmp12 = Dis1(dp, dq);
          return disin(tmp12)
        } else {
          return Dis1(dp, dq)
        }
      }
    }
  } else if (p instanceof Con1.class) {
    param0 = p.a;
    param1 = p.b;
    p1 = param0;
    q = param1;
    tmp13 = disin(p1);
    tmp14 = disin(q);
    return Con1(tmp13, tmp14)
  } else {
    return p
  }
};
elim = function elim(p) {
  let param0, param1, f, f_, param01, param11, p1, q, param02, param12, p2, q1, param03, param13, p3, q2, param04, p4, param05, s, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
  if (p instanceof Sym1.class) {
    param05 = p.a;
    s = param05;
    return Sym1(s)
  } else if (p instanceof Not1.class) {
    param04 = p.a;
    p4 = param04;
    tmp = elim(p4);
    return Not1(tmp)
  } else if (p instanceof Dis1.class) {
    param03 = p.a;
    param13 = p.b;
    p3 = param03;
    q2 = param13;
    tmp1 = elim(p3);
    tmp2 = elim(q2);
    return Dis1(tmp1, tmp2)
  } else if (p instanceof Con1.class) {
    param02 = p.a;
    param12 = p.b;
    p2 = param02;
    q1 = param12;
    tmp3 = elim(p2);
    tmp4 = elim(q1);
    return Con1(tmp3, tmp4)
  } else if (p instanceof Imp1.class) {
    param01 = p.a;
    param11 = p.b;
    p1 = param01;
    q = param11;
    tmp5 = elim(p1);
    tmp6 = Not1(tmp5);
    tmp7 = elim(q);
    return Dis1(tmp6, tmp7)
  } else if (p instanceof Eqv1.class) {
    param0 = p.a;
    param1 = p.b;
    f = param0;
    f_ = param1;
    tmp8 = Imp1(f, f_);
    tmp9 = elim(tmp8);
    tmp10 = Imp1(f_, f);
    tmp11 = elim(tmp10);
    return Con1(tmp9, tmp11)
  } else {
    throw new globalThis.Error("match error");
  }
};
interleave = function interleave(xs, ys) {
  let param0, param1, x, xs1, tmp;
  if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs1 = param1;
    tmp = interleave(ys, xs1);
    return NofibPrelude.Cons(x, tmp)
  } else if (xs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else {
    throw new globalThis.Error("match error");
  }
};
negin = function negin(p) {
  let param0, param1, p1, q, param01, param11, p2, q1, param02, param03, param12, p3, q2, param04, param13, p4, q3, param05, p5, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
  if (p instanceof Not1.class) {
    param02 = p.a;
    if (param02 instanceof Not1.class) {
      param05 = param02.a;
      p5 = param05;
      return negin(p5)
    } else if (param02 instanceof Con1.class) {
      param04 = param02.a;
      param13 = param02.b;
      p4 = param04;
      q3 = param13;
      tmp = Not1(p4);
      tmp1 = negin(tmp);
      tmp2 = Not1(q3);
      tmp3 = negin(tmp2);
      return Dis1(tmp1, tmp3)
    } else if (param02 instanceof Dis1.class) {
      param03 = param02.a;
      param12 = param02.b;
      p3 = param03;
      q2 = param12;
      tmp4 = Not1(p3);
      tmp5 = negin(tmp4);
      tmp6 = Not1(q2);
      tmp7 = negin(tmp6);
      return Con1(tmp5, tmp7)
    } else {
      return p
    }
  } else if (p instanceof Dis1.class) {
    param01 = p.a;
    param11 = p.b;
    p2 = param01;
    q1 = param11;
    tmp8 = negin(p2);
    tmp9 = negin(q1);
    return Dis1(tmp8, tmp9)
  } else if (p instanceof Con1.class) {
    param0 = p.a;
    param1 = p.b;
    p1 = param0;
    q = param1;
    tmp10 = negin(p1);
    tmp11 = negin(q);
    return Con1(tmp10, tmp11)
  } else {
    return p
  }
};
opri = function opri(c) {
  let scrut, scrut1, scrut2, scrut3, scrut4, scrut5;
  scrut5 = c === "(";
  if (scrut5 === true) {
    return 0
  } else {
    scrut4 = c === "=";
    if (scrut4 === true) {
      return 1
    } else {
      scrut3 = c === ">";
      if (scrut3 === true) {
        return 2
      } else {
        scrut2 = c === "|";
        if (scrut2 === true) {
          return 3
        } else {
          scrut1 = c === "&";
          if (scrut1 === true) {
            return 4
          } else {
            scrut = c === "~";
            if (scrut === true) {
              return 5
            } else {
              throw globalThis.Error(c);
            }
          }
        }
      }
    }
  }
};
red = function red(s) {
  let param0, param1, param01, p, param02, param11, param03, s1, p1, param04, param12, param05, q, s2, p2, q1, s3, p3, q2, s4, p4, q3, s5, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
  if (s instanceof NofibPrelude.Cons.class) {
    param0 = s.head;
    param1 = s.tail;
    if (param0 instanceof Ast1.class) {
      param01 = param0.f;
      p4 = param01;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param02 = param1.head;
        param11 = param1.tail;
        if (param02 instanceof Lex1.class) {
          param03 = param02.s;
          p3 = param01;
          p2 = param01;
          p1 = param01;
          p = param01;
          if (param03 === "=") {
            if (param11 instanceof NofibPrelude.Cons.class) {
              param04 = param11.head;
              param12 = param11.tail;
              if (param04 instanceof Ast1.class) {
                param05 = param04.f;
                q3 = param05;
                s5 = param12;
                tmp = Eqv1(q3, p4);
                tmp1 = Ast1(tmp);
                return NofibPrelude.Cons(tmp1, s5)
              } else {
                p3 = param01;
                p2 = param01;
                p1 = param01;
                p = param01;
                throw new globalThis.Error("match error");
              }
            } else {
              p3 = param01;
              p2 = param01;
              p1 = param01;
              p = param01;
              throw new globalThis.Error("match error");
            }
          } else if (param03 === ">") {
            if (param11 instanceof NofibPrelude.Cons.class) {
              param04 = param11.head;
              param12 = param11.tail;
              if (param04 instanceof Ast1.class) {
                param05 = param04.f;
                q2 = param05;
                s4 = param12;
                tmp2 = Imp1(q2, p3);
                tmp3 = Ast1(tmp2);
                return NofibPrelude.Cons(tmp3, s4)
              } else {
                p2 = param01;
                p1 = param01;
                p = param01;
                throw new globalThis.Error("match error");
              }
            } else {
              p2 = param01;
              p1 = param01;
              p = param01;
              throw new globalThis.Error("match error");
            }
          } else if (param03 === "|") {
            if (param11 instanceof NofibPrelude.Cons.class) {
              param04 = param11.head;
              param12 = param11.tail;
              if (param04 instanceof Ast1.class) {
                param05 = param04.f;
                q1 = param05;
                s3 = param12;
                tmp4 = Dis1(q1, p2);
                tmp5 = Ast1(tmp4);
                return NofibPrelude.Cons(tmp5, s3)
              } else {
                p1 = param01;
                p = param01;
                throw new globalThis.Error("match error");
              }
            } else {
              p1 = param01;
              p = param01;
              throw new globalThis.Error("match error");
            }
          } else if (param03 === "&") {
            if (param11 instanceof NofibPrelude.Cons.class) {
              param04 = param11.head;
              param12 = param11.tail;
              if (param04 instanceof Ast1.class) {
                param05 = param04.f;
                q = param05;
                s2 = param12;
                tmp6 = Con1(q, p1);
                tmp7 = Ast1(tmp6);
                return NofibPrelude.Cons(tmp7, s2)
              } else {
                p = param01;
                throw new globalThis.Error("match error");
              }
            } else {
              p = param01;
              throw new globalThis.Error("match error");
            }
          } else if (param03 === "~") {
            s1 = param11;
            tmp8 = Not1(p);
            tmp9 = Ast1(tmp8);
            return NofibPrelude.Cons(tmp9, s1)
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          p3 = param01;
          p2 = param01;
          p1 = param01;
          p = param01;
          throw new globalThis.Error("match error");
        }
      } else {
        p3 = param01;
        p2 = param01;
        p1 = param01;
        p = param01;
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
spri = function spri(s) {
  let param0, param1, param01, x, param02, param11, param03, c, s1;
  if (s instanceof NofibPrelude.Cons.class) {
    param0 = s.head;
    param1 = s.tail;
    if (param0 instanceof Ast1.class) {
      param01 = param0.f;
      x = param01;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param02 = param1.head;
        param11 = param1.tail;
        if (param02 instanceof Lex1.class) {
          param03 = param02.s;
          c = param03;
          s1 = param11;
          return opri(c)
        } else {
          return 0
        }
      } else {
        return 0
      }
    } else {
      return 0
    }
  } else {
    return 0
  }
};
redstar = function redstar(s) {
  let lambda1;
  lambda1 = (undefined, function (s1) {
    let tmp;
    tmp = spri(s1);
    return tmp != 0
  });
  return NofibPrelude.while_(lambda1, red, s)
};
spaces = function spaces(n) {
  return NofibPrelude.replicate(n, " ")
};
parseHelper = function parseHelper(t, s) {
  let param0, param1, c, t1, scrut, scrut1, t2, scrut2, param01, param11, x, param02, param12, param03, ss, t3, t4, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57;
  if (t instanceof NofibPrelude.Nil.class) {
    return redstar(s)
  } else if (t instanceof NofibPrelude.Cons.class) {
    param0 = t.head;
    param1 = t.tail;
    if (param0 === " ") {
      t4 = param1;
      return parseHelper(t4, s)
    } else if (param0 === "(") {
      t3 = param1;
      tmp = Lex1("(");
      tmp1 = NofibPrelude.Cons(tmp, s);
      return parseHelper(t3, tmp1)
    } else if (param0 === ")") {
      t2 = param1;
      scrut2 = redstar(s);
      if (scrut2 instanceof NofibPrelude.Cons.class) {
        param01 = scrut2.head;
        param11 = scrut2.tail;
        x = param01;
        if (param11 instanceof NofibPrelude.Cons.class) {
          param02 = param11.head;
          param12 = param11.tail;
          if (param02 instanceof Lex1.class) {
            param03 = param02.s;
            if (param03 === "(") {
              ss = param12;
              tmp2 = NofibPrelude.Cons(x, ss);
              return parseHelper(t2, tmp2)
            } else {
              c = param0;
              t1 = param1;
              tmp3 = charLeq("a", c);
              tmp4 = charLeq(c, "z");
              scrut1 = tmp3 && tmp4;
              if (scrut1 === true) {
                tmp5 = Sym1(c);
                tmp6 = Ast1(tmp5);
                tmp7 = NofibPrelude.Cons(tmp6, s);
                return parseHelper(t1, tmp7)
              } else {
                tmp8 = spri(s);
                tmp9 = opri(c);
                scrut = tmp8 > tmp9;
                if (scrut === true) {
                  tmp10 = NofibPrelude.Cons(c, t1);
                  tmp11 = red(s);
                  return parseHelper(tmp10, tmp11)
                } else {
                  tmp12 = Lex1(c);
                  tmp13 = NofibPrelude.Cons(tmp12, s);
                  return parseHelper(t1, tmp13)
                }
              }
            }
          } else {
            c = param0;
            t1 = param1;
            tmp14 = charLeq("a", c);
            tmp15 = charLeq(c, "z");
            scrut1 = tmp14 && tmp15;
            if (scrut1 === true) {
              tmp16 = Sym1(c);
              tmp17 = Ast1(tmp16);
              tmp18 = NofibPrelude.Cons(tmp17, s);
              return parseHelper(t1, tmp18)
            } else {
              tmp19 = spri(s);
              tmp20 = opri(c);
              scrut = tmp19 > tmp20;
              if (scrut === true) {
                tmp21 = NofibPrelude.Cons(c, t1);
                tmp22 = red(s);
                return parseHelper(tmp21, tmp22)
              } else {
                tmp23 = Lex1(c);
                tmp24 = NofibPrelude.Cons(tmp23, s);
                return parseHelper(t1, tmp24)
              }
            }
          }
        } else {
          c = param0;
          t1 = param1;
          tmp25 = charLeq("a", c);
          tmp26 = charLeq(c, "z");
          scrut1 = tmp25 && tmp26;
          if (scrut1 === true) {
            tmp27 = Sym1(c);
            tmp28 = Ast1(tmp27);
            tmp29 = NofibPrelude.Cons(tmp28, s);
            return parseHelper(t1, tmp29)
          } else {
            tmp30 = spri(s);
            tmp31 = opri(c);
            scrut = tmp30 > tmp31;
            if (scrut === true) {
              tmp32 = NofibPrelude.Cons(c, t1);
              tmp33 = red(s);
              return parseHelper(tmp32, tmp33)
            } else {
              tmp34 = Lex1(c);
              tmp35 = NofibPrelude.Cons(tmp34, s);
              return parseHelper(t1, tmp35)
            }
          }
        }
      } else {
        c = param0;
        t1 = param1;
        tmp36 = charLeq("a", c);
        tmp37 = charLeq(c, "z");
        scrut1 = tmp36 && tmp37;
        if (scrut1 === true) {
          tmp38 = Sym1(c);
          tmp39 = Ast1(tmp38);
          tmp40 = NofibPrelude.Cons(tmp39, s);
          return parseHelper(t1, tmp40)
        } else {
          tmp41 = spri(s);
          tmp42 = opri(c);
          scrut = tmp41 > tmp42;
          if (scrut === true) {
            tmp43 = NofibPrelude.Cons(c, t1);
            tmp44 = red(s);
            return parseHelper(tmp43, tmp44)
          } else {
            tmp45 = Lex1(c);
            tmp46 = NofibPrelude.Cons(tmp45, s);
            return parseHelper(t1, tmp46)
          }
        }
      }
    } else {
      c = param0;
      t1 = param1;
      tmp47 = charLeq("a", c);
      tmp48 = charLeq(c, "z");
      scrut1 = tmp47 && tmp48;
      if (scrut1 === true) {
        tmp49 = Sym1(c);
        tmp50 = Ast1(tmp49);
        tmp51 = NofibPrelude.Cons(tmp50, s);
        return parseHelper(t1, tmp51)
      } else {
        tmp52 = spri(s);
        tmp53 = opri(c);
        scrut = tmp52 > tmp53;
        if (scrut === true) {
          tmp54 = NofibPrelude.Cons(c, t1);
          tmp55 = red(s);
          return parseHelper(tmp54, tmp55)
        } else {
          tmp56 = Lex1(c);
          tmp57 = NofibPrelude.Cons(tmp56, s);
          return parseHelper(t1, tmp57)
        }
      }
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
parse = function parse(t) {
  let scrut, param0, param1, param01, f;
  scrut = parseHelper(t, NofibPrelude.Nil);
  if (scrut instanceof NofibPrelude.Cons.class) {
    param0 = scrut.head;
    param1 = scrut.tail;
    if (param0 instanceof Ast1.class) {
      param01 = param0.f;
      f = param01;
      if (param1 instanceof NofibPrelude.Nil.class) {
        return f
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
splitHelper = function splitHelper(p, a) {
  let param0, param1, p1, q, tmp;
  if (p instanceof Con1.class) {
    param0 = p.a;
    param1 = p.b;
    p1 = param0;
    q = param1;
    tmp = splitHelper(q, a);
    return splitHelper(p1, tmp)
  } else {
    return NofibPrelude.Cons(p, a)
  }
};
split = function split(p) {
  return splitHelper(p, NofibPrelude.Nil)
};
tautclause = function tautclause(c_a) {
  let lscomp, first1, first0, c, a, tmp;
  if (globalThis.Array.isArray(c_a) && c_a.length === 2) {
    first0 = c_a[0];
    first1 = c_a[1];
    c = first0;
    a = first1;
    lscomp = function lscomp(ls) {
      let param0, param1, h, t, scrut, tmp1;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        h = param0;
        t = param1;
        scrut = NofibPrelude.inList(h, a);
        if (scrut === true) {
          tmp1 = lscomp(t);
          return NofibPrelude.Cons(h, tmp1)
        } else {
          return lscomp(t)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp = lscomp(c);
    return NofibPrelude.listNeq(tmp, NofibPrelude.Nil)
  } else {
    throw new globalThis.Error("match error");
  }
};
uniclHelper = function uniclHelper(p, x) {
  let cp, scrut, tmp;
  tmp = clause(p);
  cp = tmp;
  scrut = tautclause(cp);
  if (scrut === true) {
    return x
  } else {
    return insert(cp, x)
  }
};
unicl = function unicl(a) {
  return NofibPrelude.foldr(uniclHelper, NofibPrelude.Nil, a)
};
disp = function disp(l_r) {
  let first1, first0, l, r, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
  if (globalThis.Array.isArray(l_r) && l_r.length === 2) {
    first0 = l_r[0];
    first1 = l_r[1];
    l = first0;
    r = first1;
    tmp = NofibPrelude.listLen(l);
    tmp1 = spaces(tmp);
    tmp2 = interleave(l, tmp1);
    tmp3 = NofibPrelude.nofibStringToList("<=");
    tmp4 = NofibPrelude.listLen(r);
    tmp5 = spaces(tmp4);
    tmp6 = interleave(tmp5, r);
    tmp7 = NofibPrelude.nofibStringToList("\n");
    tmp8 = NofibPrelude.append(tmp6, tmp7);
    tmp9 = NofibPrelude.append(tmp3, tmp8);
    return NofibPrelude.append(tmp2, tmp9)
  } else {
    throw new globalThis.Error("match error");
  }
};
clauses = function clauses(t) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
  tmp = parse(t);
  tmp1 = elim(tmp);
  tmp2 = negin(tmp1);
  tmp3 = disin(tmp2);
  tmp4 = split(tmp3);
  tmp5 = unicl(tmp4);
  tmp6 = NofibPrelude.map(disp, tmp5);
  return NofibPrelude.concat(tmp6)
};
testClausify_nofib = function testClausify_nofib(n) {
  let xs, tmp, tmp1, tmp2;
  tmp = NofibPrelude.nofibStringToList("a = a = a");
  tmp1 = NofibPrelude.replicate(n, tmp);
  xs = tmp1;
  tmp2 = NofibPrelude.map(clauses, xs);
  return NofibPrelude.concat(tmp2)
};
Formula1 = class Formula {
  constructor() {}
  toString() { return "Formula"; }
};
Sym1 = function Sym(a1) {
  return new Sym.class(a1);
};
Sym1.class = class Sym extends Formula1 {
  constructor(a) {
    super();
    this.a = a;
  }
  toString() { return "Sym(" + globalThis.Predef.render(this.a) + ")"; }
};
Not1 = function Not(a1) {
  return new Not.class(a1);
};
Not1.class = class Not extends Formula1 {
  constructor(a) {
    super();
    this.a = a;
  }
  toString() { return "Not(" + globalThis.Predef.render(this.a) + ")"; }
};
Dis1 = function Dis(a1, b1) {
  return new Dis.class(a1, b1);
};
Dis1.class = class Dis extends Formula1 {
  constructor(a, b) {
    super();
    this.a = a;
    this.b = b;
  }
  toString() { return "Dis(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
};
Con1 = function Con(a1, b1) {
  return new Con.class(a1, b1);
};
Con1.class = class Con extends Formula1 {
  constructor(a, b) {
    super();
    this.a = a;
    this.b = b;
  }
  toString() { return "Con(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
};
Imp1 = function Imp(a1, b1) {
  return new Imp.class(a1, b1);
};
Imp1.class = class Imp extends Formula1 {
  constructor(a, b) {
    super();
    this.a = a;
    this.b = b;
  }
  toString() { return "Imp(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
};
Eqv1 = function Eqv(a1, b1) {
  return new Eqv.class(a1, b1);
};
Eqv1.class = class Eqv extends Formula1 {
  constructor(a, b) {
    super();
    this.a = a;
    this.b = b;
  }
  toString() { return "Eqv(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
};
StackFrame1 = class StackFrame {
  constructor() {}
  toString() { return "StackFrame"; }
};
Ast1 = function Ast(f1) {
  return new Ast.class(f1);
};
Ast1.class = class Ast extends StackFrame1 {
  constructor(f) {
    super();
    this.f = f;
  }
  toString() { return "Ast(" + globalThis.Predef.render(this.f) + ")"; }
};
Lex1 = function Lex(s1) {
  return new Lex.class(s1);
};
Lex1.class = class Lex extends StackFrame1 {
  constructor(s) {
    super();
    this.s = s;
  }
  toString() { return "Lex(" + globalThis.Predef.render(this.s) + ")"; }
};
lambda = (undefined, function () {
  let tmp;
  tmp = testClausify_nofib(10);
  return NofibPrelude.nofibListToString(tmp)
});
BenchmarkPrelude.benchmark(lambda)