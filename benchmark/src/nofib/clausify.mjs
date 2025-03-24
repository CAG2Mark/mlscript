import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let clausify1;
clausify1 = class clausify {
  static {
    clausify1 = clausify;
    let lambda;
    this.Formula = class Formula {
      constructor() {}
      toString() { return "Formula"; }
    };
    this.Sym = function Sym(a1) {
      return new Sym.class(a1);
    };
    this.Sym.class = class Sym extends clausify.Formula {
      constructor(a) {
        super();
        this.a = a;
      }
      toString() { return "Sym(" + globalThis.Predef.render(this.a) + ")"; }
    };
    this.Not = function Not(a1) {
      return new Not.class(a1);
    };
    this.Not.class = class Not extends clausify.Formula {
      constructor(a) {
        super();
        this.a = a;
      }
      toString() { return "Not(" + globalThis.Predef.render(this.a) + ")"; }
    };
    this.Dis = function Dis(a1, b1) {
      return new Dis.class(a1, b1);
    };
    this.Dis.class = class Dis extends clausify.Formula {
      constructor(a, b) {
        super();
        this.a = a;
        this.b = b;
      }
      toString() { return "Dis(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    this.Con = function Con(a1, b1) {
      return new Con.class(a1, b1);
    };
    this.Con.class = class Con extends clausify.Formula {
      constructor(a, b) {
        super();
        this.a = a;
        this.b = b;
      }
      toString() { return "Con(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    this.Imp = function Imp(a1, b1) {
      return new Imp.class(a1, b1);
    };
    this.Imp.class = class Imp extends clausify.Formula {
      constructor(a, b) {
        super();
        this.a = a;
        this.b = b;
      }
      toString() { return "Imp(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    this.Eqv = function Eqv(a1, b1) {
      return new Eqv.class(a1, b1);
    };
    this.Eqv.class = class Eqv extends clausify.Formula {
      constructor(a, b) {
        super();
        this.a = a;
        this.b = b;
      }
      toString() { return "Eqv(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    this.StackFrame = class StackFrame {
      constructor() {}
      toString() { return "StackFrame"; }
    };
    this.Ast = function Ast(f1) {
      return new Ast.class(f1);
    };
    this.Ast.class = class Ast extends clausify.StackFrame {
      constructor(f) {
        super();
        this.f = f;
      }
      toString() { return "Ast(" + globalThis.Predef.render(this.f) + ")"; }
    };
    this.Lex = function Lex(s1) {
      return new Lex.class(s1);
    };
    this.Lex.class = class Lex extends clausify.StackFrame {
      constructor(s) {
        super();
        this.s = s;
      }
      toString() { return "Lex(" + globalThis.Predef.render(this.s) + ")"; }
    };
    lambda = (undefined, function () {
      let tmp;
      tmp = clausify.testClausify_nofib(10);
      return NofibPrelude.nofibListToString(tmp)
    });
    BenchmarkPrelude.benchmark(lambda)
  }
  static charLt(a, b) {
    return a < b
  } 
  static charLeq(a1, b1) {
    return a1 <= b1
  } 
  static charGt(a2, b2) {
    return a2 > b2
  } 
  static charGeq(a3, b3) {
    return a3 >= b3
  } 
  static insert(x, ys) {
    let param0, param1, y, ys1, scrut, scrut1, tmp, tmp1;
    if (ys instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Cons(x, NofibPrelude.Nil)
    } else if (ys instanceof NofibPrelude.Cons.class) {
      param0 = ys.head;
      param1 = ys.tail;
      y = param0;
      ys1 = param1;
      scrut1 = clausify.charLt(x, y);
      if (scrut1 === true) {
        tmp = NofibPrelude.Cons(y, ys1);
        return NofibPrelude.Cons(x, tmp)
      } else {
        scrut = clausify.charGt(x, y);
        if (scrut === true) {
          tmp1 = clausify.insert(x, ys1);
          return NofibPrelude.Cons(y, tmp1)
        } else {
          return NofibPrelude.Cons(y, ys1)
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static clauseHelper(p, x1) {
    let param0, param01, s, first1, first0, c, a4, param02, s1, c1, a5, param03, param1, p1, q, tmp, tmp1, tmp2;
    if (p instanceof clausify.Dis.class) {
      param03 = p.a;
      param1 = p.b;
      p1 = param03;
      q = param1;
      tmp = clausify.clauseHelper(q, x1);
      return clausify.clauseHelper(p1, tmp)
    } else if (p instanceof clausify.Sym.class) {
      param02 = p.a;
      s1 = param02;
      if (globalThis.Array.isArray(x1) && x1.length === 2) {
        first0 = x1[0];
        first1 = x1[1];
        c1 = first0;
        a5 = first1;
        tmp1 = clausify.insert(s1, c1);
        return [
          tmp1,
          a5
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (p instanceof clausify.Not.class) {
      param0 = p.a;
      if (param0 instanceof clausify.Sym.class) {
        param01 = param0.a;
        s = param01;
        if (globalThis.Array.isArray(x1) && x1.length === 2) {
          first0 = x1[0];
          first1 = x1[1];
          c = first0;
          a4 = first1;
          tmp2 = clausify.insert(s, a4);
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
  } 
  static clause(p1) {
    return clausify.clauseHelper(p1, [
      NofibPrelude.Nil,
      NofibPrelude.Nil
    ])
  } 
  static conjunct(p2) {
    let param0, param1;
    if (p2 instanceof clausify.Con.class) {
      param0 = p2.a;
      param1 = p2.b;
      return true
    } else {
      return false
    }
  } 
  static disin(p3) {
    let param0, param1, p4, q, param01, param11, p5, q1, dp, dq, scrut, param02, param12, p6, q2, r, p7, param03, param13, q3, r1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
    if (p3 instanceof clausify.Dis.class) {
      param01 = p3.a;
      param11 = p3.b;
      p7 = param01;
      if (param11 instanceof clausify.Con.class) {
        param03 = param11.a;
        param13 = param11.b;
        q3 = param03;
        r1 = param13;
        tmp = clausify.Dis(p7, q3);
        tmp1 = clausify.disin(tmp);
        tmp2 = clausify.Dis(p7, r1);
        tmp3 = clausify.disin(tmp2);
        return clausify.Con(tmp1, tmp3)
      } else {
        if (param01 instanceof clausify.Con.class) {
          param02 = param01.a;
          param12 = param01.b;
          p6 = param02;
          q2 = param12;
          r = param11;
          tmp4 = clausify.Dis(p6, r);
          tmp5 = clausify.disin(tmp4);
          tmp6 = clausify.Dis(q2, r);
          tmp7 = clausify.disin(tmp6);
          return clausify.Con(tmp5, tmp7)
        } else {
          p5 = param01;
          q1 = param11;
          tmp8 = clausify.disin(p5);
          dp = tmp8;
          tmp9 = clausify.disin(q1);
          dq = tmp9;
          tmp10 = clausify.conjunct(dp);
          tmp11 = clausify.conjunct(dq);
          scrut = tmp10 || tmp11;
          if (scrut === true) {
            tmp12 = clausify.Dis(dp, dq);
            return clausify.disin(tmp12)
          } else {
            return clausify.Dis(dp, dq)
          }
        }
      }
    } else if (p3 instanceof clausify.Con.class) {
      param0 = p3.a;
      param1 = p3.b;
      p4 = param0;
      q = param1;
      tmp13 = clausify.disin(p4);
      tmp14 = clausify.disin(q);
      return clausify.Con(tmp13, tmp14)
    } else {
      return p3
    }
  } 
  static elim(p4) {
    let param0, param1, f, f_, param01, param11, p5, q, param02, param12, p6, q1, param03, param13, p7, q2, param04, p8, param05, s, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
    if (p4 instanceof clausify.Sym.class) {
      param05 = p4.a;
      s = param05;
      return clausify.Sym(s)
    } else if (p4 instanceof clausify.Not.class) {
      param04 = p4.a;
      p8 = param04;
      tmp = clausify.elim(p8);
      return clausify.Not(tmp)
    } else if (p4 instanceof clausify.Dis.class) {
      param03 = p4.a;
      param13 = p4.b;
      p7 = param03;
      q2 = param13;
      tmp1 = clausify.elim(p7);
      tmp2 = clausify.elim(q2);
      return clausify.Dis(tmp1, tmp2)
    } else if (p4 instanceof clausify.Con.class) {
      param02 = p4.a;
      param12 = p4.b;
      p6 = param02;
      q1 = param12;
      tmp3 = clausify.elim(p6);
      tmp4 = clausify.elim(q1);
      return clausify.Con(tmp3, tmp4)
    } else if (p4 instanceof clausify.Imp.class) {
      param01 = p4.a;
      param11 = p4.b;
      p5 = param01;
      q = param11;
      tmp5 = clausify.elim(p5);
      tmp6 = clausify.Not(tmp5);
      tmp7 = clausify.elim(q);
      return clausify.Dis(tmp6, tmp7)
    } else if (p4 instanceof clausify.Eqv.class) {
      param0 = p4.a;
      param1 = p4.b;
      f = param0;
      f_ = param1;
      tmp8 = clausify.Imp(f, f_);
      tmp9 = clausify.elim(tmp8);
      tmp10 = clausify.Imp(f_, f);
      tmp11 = clausify.elim(tmp10);
      return clausify.Con(tmp9, tmp11)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static interleave(xs, ys1) {
    let param0, param1, x2, xs1, tmp;
    if (xs instanceof NofibPrelude.Cons.class) {
      param0 = xs.head;
      param1 = xs.tail;
      x2 = param0;
      xs1 = param1;
      tmp = clausify.interleave(ys1, xs1);
      return NofibPrelude.Cons(x2, tmp)
    } else if (xs instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static negin(p5) {
    let param0, param1, p6, q, param01, param11, p7, q1, param02, param03, param12, p8, q2, param04, param13, p9, q3, param05, p10, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
    if (p5 instanceof clausify.Not.class) {
      param02 = p5.a;
      if (param02 instanceof clausify.Not.class) {
        param05 = param02.a;
        p10 = param05;
        return clausify.negin(p10)
      } else if (param02 instanceof clausify.Con.class) {
        param04 = param02.a;
        param13 = param02.b;
        p9 = param04;
        q3 = param13;
        tmp = clausify.Not(p9);
        tmp1 = clausify.negin(tmp);
        tmp2 = clausify.Not(q3);
        tmp3 = clausify.negin(tmp2);
        return clausify.Dis(tmp1, tmp3)
      } else if (param02 instanceof clausify.Dis.class) {
        param03 = param02.a;
        param12 = param02.b;
        p8 = param03;
        q2 = param12;
        tmp4 = clausify.Not(p8);
        tmp5 = clausify.negin(tmp4);
        tmp6 = clausify.Not(q2);
        tmp7 = clausify.negin(tmp6);
        return clausify.Con(tmp5, tmp7)
      } else {
        return p5
      }
    } else if (p5 instanceof clausify.Dis.class) {
      param01 = p5.a;
      param11 = p5.b;
      p7 = param01;
      q1 = param11;
      tmp8 = clausify.negin(p7);
      tmp9 = clausify.negin(q1);
      return clausify.Dis(tmp8, tmp9)
    } else if (p5 instanceof clausify.Con.class) {
      param0 = p5.a;
      param1 = p5.b;
      p6 = param0;
      q = param1;
      tmp10 = clausify.negin(p6);
      tmp11 = clausify.negin(q);
      return clausify.Con(tmp10, tmp11)
    } else {
      return p5
    }
  } 
  static opri(c) {
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
  } 
  static red(s) {
    let param0, param1, param01, p6, param02, param11, param03, s1, p7, param04, param12, param05, q, s2, p8, q1, s3, p9, q2, s4, p10, q3, s5, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    if (s instanceof NofibPrelude.Cons.class) {
      param0 = s.head;
      param1 = s.tail;
      if (param0 instanceof clausify.Ast.class) {
        param01 = param0.f;
        p10 = param01;
        if (param1 instanceof NofibPrelude.Cons.class) {
          param02 = param1.head;
          param11 = param1.tail;
          if (param02 instanceof clausify.Lex.class) {
            param03 = param02.s;
            p9 = param01;
            p8 = param01;
            p7 = param01;
            p6 = param01;
            if (param03 === "=") {
              if (param11 instanceof NofibPrelude.Cons.class) {
                param04 = param11.head;
                param12 = param11.tail;
                if (param04 instanceof clausify.Ast.class) {
                  param05 = param04.f;
                  q3 = param05;
                  s5 = param12;
                  tmp = clausify.Eqv(q3, p10);
                  tmp1 = clausify.Ast(tmp);
                  return NofibPrelude.Cons(tmp1, s5)
                } else {
                  p9 = param01;
                  p8 = param01;
                  p7 = param01;
                  p6 = param01;
                  throw new globalThis.Error("match error");
                }
              } else {
                p9 = param01;
                p8 = param01;
                p7 = param01;
                p6 = param01;
                throw new globalThis.Error("match error");
              }
            } else if (param03 === ">") {
              if (param11 instanceof NofibPrelude.Cons.class) {
                param04 = param11.head;
                param12 = param11.tail;
                if (param04 instanceof clausify.Ast.class) {
                  param05 = param04.f;
                  q2 = param05;
                  s4 = param12;
                  tmp2 = clausify.Imp(q2, p9);
                  tmp3 = clausify.Ast(tmp2);
                  return NofibPrelude.Cons(tmp3, s4)
                } else {
                  p8 = param01;
                  p7 = param01;
                  p6 = param01;
                  throw new globalThis.Error("match error");
                }
              } else {
                p8 = param01;
                p7 = param01;
                p6 = param01;
                throw new globalThis.Error("match error");
              }
            } else if (param03 === "|") {
              if (param11 instanceof NofibPrelude.Cons.class) {
                param04 = param11.head;
                param12 = param11.tail;
                if (param04 instanceof clausify.Ast.class) {
                  param05 = param04.f;
                  q1 = param05;
                  s3 = param12;
                  tmp4 = clausify.Dis(q1, p8);
                  tmp5 = clausify.Ast(tmp4);
                  return NofibPrelude.Cons(tmp5, s3)
                } else {
                  p7 = param01;
                  p6 = param01;
                  throw new globalThis.Error("match error");
                }
              } else {
                p7 = param01;
                p6 = param01;
                throw new globalThis.Error("match error");
              }
            } else if (param03 === "&") {
              if (param11 instanceof NofibPrelude.Cons.class) {
                param04 = param11.head;
                param12 = param11.tail;
                if (param04 instanceof clausify.Ast.class) {
                  param05 = param04.f;
                  q = param05;
                  s2 = param12;
                  tmp6 = clausify.Con(q, p7);
                  tmp7 = clausify.Ast(tmp6);
                  return NofibPrelude.Cons(tmp7, s2)
                } else {
                  p6 = param01;
                  throw new globalThis.Error("match error");
                }
              } else {
                p6 = param01;
                throw new globalThis.Error("match error");
              }
            } else if (param03 === "~") {
              s1 = param11;
              tmp8 = clausify.Not(p6);
              tmp9 = clausify.Ast(tmp8);
              return NofibPrelude.Cons(tmp9, s1)
            } else {
              throw new globalThis.Error("match error");
            }
          } else {
            p9 = param01;
            p8 = param01;
            p7 = param01;
            p6 = param01;
            throw new globalThis.Error("match error");
          }
        } else {
          p9 = param01;
          p8 = param01;
          p7 = param01;
          p6 = param01;
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static spri(s1) {
    let param0, param1, param01, x2, param02, param11, param03, c1, s2;
    if (s1 instanceof NofibPrelude.Cons.class) {
      param0 = s1.head;
      param1 = s1.tail;
      if (param0 instanceof clausify.Ast.class) {
        param01 = param0.f;
        x2 = param01;
        if (param1 instanceof NofibPrelude.Cons.class) {
          param02 = param1.head;
          param11 = param1.tail;
          if (param02 instanceof clausify.Lex.class) {
            param03 = param02.s;
            c1 = param03;
            s2 = param11;
            return clausify.opri(c1)
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
  } 
  static redstar(s2) {
    let lambda;
    lambda = (undefined, function (s3) {
      let tmp;
      tmp = clausify.spri(s3);
      return tmp != 0
    });
    return NofibPrelude.while_(lambda, clausify.red, s2)
  } 
  static spaces(n) {
    return NofibPrelude.replicate(n, " ")
  } 
  static parseHelper(t, s3) {
    let param0, param1, c1, t1, scrut, scrut1, t2, scrut2, param01, param11, x2, param02, param12, param03, ss, t3, t4, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57;
    if (t instanceof NofibPrelude.Nil.class) {
      return clausify.redstar(s3)
    } else if (t instanceof NofibPrelude.Cons.class) {
      param0 = t.head;
      param1 = t.tail;
      if (param0 === " ") {
        t4 = param1;
        return clausify.parseHelper(t4, s3)
      } else if (param0 === "(") {
        t3 = param1;
        tmp = clausify.Lex("(");
        tmp1 = NofibPrelude.Cons(tmp, s3);
        return clausify.parseHelper(t3, tmp1)
      } else if (param0 === ")") {
        t2 = param1;
        scrut2 = clausify.redstar(s3);
        if (scrut2 instanceof NofibPrelude.Cons.class) {
          param01 = scrut2.head;
          param11 = scrut2.tail;
          x2 = param01;
          if (param11 instanceof NofibPrelude.Cons.class) {
            param02 = param11.head;
            param12 = param11.tail;
            if (param02 instanceof clausify.Lex.class) {
              param03 = param02.s;
              if (param03 === "(") {
                ss = param12;
                tmp2 = NofibPrelude.Cons(x2, ss);
                return clausify.parseHelper(t2, tmp2)
              } else {
                c1 = param0;
                t1 = param1;
                tmp3 = clausify.charLeq("a", c1);
                tmp4 = clausify.charLeq(c1, "z");
                scrut1 = tmp3 && tmp4;
                if (scrut1 === true) {
                  tmp5 = clausify.Sym(c1);
                  tmp6 = clausify.Ast(tmp5);
                  tmp7 = NofibPrelude.Cons(tmp6, s3);
                  return clausify.parseHelper(t1, tmp7)
                } else {
                  tmp8 = clausify.spri(s3);
                  tmp9 = clausify.opri(c1);
                  scrut = tmp8 > tmp9;
                  if (scrut === true) {
                    tmp10 = NofibPrelude.Cons(c1, t1);
                    tmp11 = clausify.red(s3);
                    return clausify.parseHelper(tmp10, tmp11)
                  } else {
                    tmp12 = clausify.Lex(c1);
                    tmp13 = NofibPrelude.Cons(tmp12, s3);
                    return clausify.parseHelper(t1, tmp13)
                  }
                }
              }
            } else {
              c1 = param0;
              t1 = param1;
              tmp14 = clausify.charLeq("a", c1);
              tmp15 = clausify.charLeq(c1, "z");
              scrut1 = tmp14 && tmp15;
              if (scrut1 === true) {
                tmp16 = clausify.Sym(c1);
                tmp17 = clausify.Ast(tmp16);
                tmp18 = NofibPrelude.Cons(tmp17, s3);
                return clausify.parseHelper(t1, tmp18)
              } else {
                tmp19 = clausify.spri(s3);
                tmp20 = clausify.opri(c1);
                scrut = tmp19 > tmp20;
                if (scrut === true) {
                  tmp21 = NofibPrelude.Cons(c1, t1);
                  tmp22 = clausify.red(s3);
                  return clausify.parseHelper(tmp21, tmp22)
                } else {
                  tmp23 = clausify.Lex(c1);
                  tmp24 = NofibPrelude.Cons(tmp23, s3);
                  return clausify.parseHelper(t1, tmp24)
                }
              }
            }
          } else {
            c1 = param0;
            t1 = param1;
            tmp25 = clausify.charLeq("a", c1);
            tmp26 = clausify.charLeq(c1, "z");
            scrut1 = tmp25 && tmp26;
            if (scrut1 === true) {
              tmp27 = clausify.Sym(c1);
              tmp28 = clausify.Ast(tmp27);
              tmp29 = NofibPrelude.Cons(tmp28, s3);
              return clausify.parseHelper(t1, tmp29)
            } else {
              tmp30 = clausify.spri(s3);
              tmp31 = clausify.opri(c1);
              scrut = tmp30 > tmp31;
              if (scrut === true) {
                tmp32 = NofibPrelude.Cons(c1, t1);
                tmp33 = clausify.red(s3);
                return clausify.parseHelper(tmp32, tmp33)
              } else {
                tmp34 = clausify.Lex(c1);
                tmp35 = NofibPrelude.Cons(tmp34, s3);
                return clausify.parseHelper(t1, tmp35)
              }
            }
          }
        } else {
          c1 = param0;
          t1 = param1;
          tmp36 = clausify.charLeq("a", c1);
          tmp37 = clausify.charLeq(c1, "z");
          scrut1 = tmp36 && tmp37;
          if (scrut1 === true) {
            tmp38 = clausify.Sym(c1);
            tmp39 = clausify.Ast(tmp38);
            tmp40 = NofibPrelude.Cons(tmp39, s3);
            return clausify.parseHelper(t1, tmp40)
          } else {
            tmp41 = clausify.spri(s3);
            tmp42 = clausify.opri(c1);
            scrut = tmp41 > tmp42;
            if (scrut === true) {
              tmp43 = NofibPrelude.Cons(c1, t1);
              tmp44 = clausify.red(s3);
              return clausify.parseHelper(tmp43, tmp44)
            } else {
              tmp45 = clausify.Lex(c1);
              tmp46 = NofibPrelude.Cons(tmp45, s3);
              return clausify.parseHelper(t1, tmp46)
            }
          }
        }
      } else {
        c1 = param0;
        t1 = param1;
        tmp47 = clausify.charLeq("a", c1);
        tmp48 = clausify.charLeq(c1, "z");
        scrut1 = tmp47 && tmp48;
        if (scrut1 === true) {
          tmp49 = clausify.Sym(c1);
          tmp50 = clausify.Ast(tmp49);
          tmp51 = NofibPrelude.Cons(tmp50, s3);
          return clausify.parseHelper(t1, tmp51)
        } else {
          tmp52 = clausify.spri(s3);
          tmp53 = clausify.opri(c1);
          scrut = tmp52 > tmp53;
          if (scrut === true) {
            tmp54 = NofibPrelude.Cons(c1, t1);
            tmp55 = clausify.red(s3);
            return clausify.parseHelper(tmp54, tmp55)
          } else {
            tmp56 = clausify.Lex(c1);
            tmp57 = NofibPrelude.Cons(tmp56, s3);
            return clausify.parseHelper(t1, tmp57)
          }
        }
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static parse(t1) {
    let scrut, param0, param1, param01, f;
    scrut = clausify.parseHelper(t1, NofibPrelude.Nil);
    if (scrut instanceof NofibPrelude.Cons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      if (param0 instanceof clausify.Ast.class) {
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
  } 
  static splitHelper(p6, a4) {
    let param0, param1, p7, q, tmp;
    if (p6 instanceof clausify.Con.class) {
      param0 = p6.a;
      param1 = p6.b;
      p7 = param0;
      q = param1;
      tmp = clausify.splitHelper(q, a4);
      return clausify.splitHelper(p7, tmp)
    } else {
      return NofibPrelude.Cons(p6, a4)
    }
  } 
  static split(p7) {
    return clausify.splitHelper(p7, NofibPrelude.Nil)
  } 
  static tautclause(c_a) {
    let lscomp, first1, first0, c1, a5, tmp;
    if (globalThis.Array.isArray(c_a) && c_a.length === 2) {
      first0 = c_a[0];
      first1 = c_a[1];
      c1 = first0;
      a5 = first1;
      lscomp = function lscomp(ls) {
        let param0, param1, h, t2, scrut, tmp1;
        if (ls instanceof NofibPrelude.Nil.class) {
          return NofibPrelude.Nil
        } else if (ls instanceof NofibPrelude.Cons.class) {
          param0 = ls.head;
          param1 = ls.tail;
          h = param0;
          t2 = param1;
          scrut = NofibPrelude.inList(h, a5);
          if (scrut === true) {
            tmp1 = lscomp(t2);
            return NofibPrelude.Cons(h, tmp1)
          } else {
            return lscomp(t2)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      };
      tmp = lscomp(c1);
      return NofibPrelude.listNeq(tmp, NofibPrelude.Nil)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static uniclHelper(p8, x2) {
    let cp, scrut, tmp;
    tmp = clausify.clause(p8);
    cp = tmp;
    scrut = clausify.tautclause(cp);
    if (scrut === true) {
      return x2
    } else {
      return clausify.insert(cp, x2)
    }
  } 
  static unicl(a5) {
    return NofibPrelude.foldr(clausify.uniclHelper, NofibPrelude.Nil, a5)
  } 
  static disp(l_r) {
    let first1, first0, l, r, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
    if (globalThis.Array.isArray(l_r) && l_r.length === 2) {
      first0 = l_r[0];
      first1 = l_r[1];
      l = first0;
      r = first1;
      tmp = NofibPrelude.listLen(l);
      tmp1 = clausify.spaces(tmp);
      tmp2 = clausify.interleave(l, tmp1);
      tmp3 = NofibPrelude.nofibStringToList("<=");
      tmp4 = NofibPrelude.listLen(r);
      tmp5 = clausify.spaces(tmp4);
      tmp6 = clausify.interleave(tmp5, r);
      tmp7 = NofibPrelude.nofibStringToList("\n");
      tmp8 = NofibPrelude.append(tmp6, tmp7);
      tmp9 = NofibPrelude.append(tmp3, tmp8);
      return NofibPrelude.append(tmp2, tmp9)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static clauses(t2) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = clausify.parse(t2);
    tmp1 = clausify.elim(tmp);
    tmp2 = clausify.negin(tmp1);
    tmp3 = clausify.disin(tmp2);
    tmp4 = clausify.split(tmp3);
    tmp5 = clausify.unicl(tmp4);
    tmp6 = NofibPrelude.map(clausify.disp, tmp5);
    return NofibPrelude.concat(tmp6)
  } 
  static testClausify_nofib(n1) {
    let xs1, tmp, tmp1, tmp2;
    tmp = NofibPrelude.nofibStringToList("a = a = a");
    tmp1 = NofibPrelude.replicate(n1, tmp);
    xs1 = tmp1;
    tmp2 = NofibPrelude.map(clausify.clauses, xs1);
    return NofibPrelude.concat(tmp2)
  }
  static toString() { return "clausify"; }
};
let clausify = clausify1; export default clausify;
