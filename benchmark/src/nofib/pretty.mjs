import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let pp_word, pretty_stuff, pretty1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda$, lambda$1, lambda$2, pretty_stuff$, lambda$3;
pp_word = function pp_word(a, b) {
  let tmp;
  tmp = NofibPrelude.nofibStringToList("xxxxx");
  return pretty1.ppStr(tmp, a, b)
};
lambda6 = (undefined, function (a, b) {
  let tmp;
  tmp = NofibPrelude.nofibStringToList("This is a string");
  return pretty1.ppStr(tmp, a, b)
});
lambda7 = (undefined, function (a, b) {
  return pretty1.ppChar("@", a, b)
});
lambda8 = (undefined, function (a, b) {
  let tmp;
  tmp = - 42;
  return pretty1.ppInt(tmp, a, b)
});
lambda10 = (undefined, function (a, b) {
  let tmp;
  tmp = NofibPrelude.nofibStringToList("This is the label");
  return pretty1.ppStr(tmp, a, b)
});
lambda$3 = function lambda$(pp_words, a, b) {
  let tmp;
  tmp = pretty1.ppCat(pp_words);
  return pretty1.ppHang(lambda10, 8, tmp, a, b)
};
lambda9 = (undefined, function (pp_words) {
  return (a, b) => {
    return lambda$3(pp_words, a, b)
  }
});
lambda11 = (undefined, function (a, b) {
  return pretty1.pp_SP(a, b)
});
pretty_stuff$ = function pretty_stuff$(pp_words, a, b) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, lambda$this;
  tmp = NofibPrelude.Cons(lambda6, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(lambda7, tmp);
  tmp2 = NofibPrelude.Cons(lambda8, tmp1);
  tmp3 = pretty1.ppBesides(tmp2);
  lambda$this = runtime.safeCall(lambda9(pp_words));
  tmp4 = NofibPrelude.Cons(lambda$this, NofibPrelude.Nil);
  tmp5 = NofibPrelude.Cons(lambda11, tmp4);
  tmp6 = NofibPrelude.Cons(tmp3, tmp5);
  return pretty1.ppAboves(tmp6, a, b)
};
pretty_stuff = function pretty_stuff(pp_words) {
  return (a, b) => {
    return pretty_stuff$(pp_words, a, b)
  }
};
lambda$2 = function lambda$(a, b, c, d) {
  return pretty1.ppAbove(a, b, c, d)
};
lambda5 = (undefined, function (a, b) {
  return (c, d) => {
    return lambda$2(a, b, c, d)
  }
});
lambda4 = (undefined, function (a, b) {
  return runtime.safeCall(lambda5(a, b))
});
lambda$1 = function lambda$(a, b, c, d) {
  return pretty1.ppBesideSP(a, b, c, d)
};
lambda3 = (undefined, function (a, b) {
  return (c, d) => {
    return lambda$1(a, b, c, d)
  }
});
lambda2 = (undefined, function (a, b) {
  return runtime.safeCall(lambda3(a, b))
});
lambda$ = function lambda$(a, b, c, d) {
  return pretty1.ppBeside(a, b, c, d)
};
lambda1 = (undefined, function (a, b) {
  return (c, d) => {
    return lambda$(a, b, c, d)
  }
});
lambda = (undefined, function (a, b) {
  return runtime.safeCall(lambda1(a, b))
});
pretty1 = class pretty {
  static {
    pretty1 = pretty;
    let lambda12;
    this.CSeq = class CSeq {
      constructor() {}
      toString() { return "CSeq"; }
    };
    this.CAppend = function CAppend(a1, b1) {
      return new CAppend.class(a1, b1);
    };
    this.CAppend.class = class CAppend extends pretty.CSeq {
      constructor(a, b) {
        super();
        this.a = a;
        this.b = b;
      }
      toString() { return "CAppend(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    this.CIndent = function CIndent(a1, b1) {
      return new CIndent.class(a1, b1);
    };
    this.CIndent.class = class CIndent extends pretty.CSeq {
      constructor(a, b) {
        super();
        this.a = a;
        this.b = b;
      }
      toString() { return "CIndent(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
    };
    this.CStr = function CStr(a1) {
      return new CStr.class(a1);
    };
    this.CStr.class = class CStr extends pretty.CSeq {
      constructor(a) {
        super();
        this.a = a;
      }
      toString() { return "CStr(" + globalThis.Predef.render(this.a) + ")"; }
    };
    this.CCh = function CCh(a1) {
      return new CCh.class(a1);
    };
    this.CCh.class = class CCh extends pretty.CSeq {
      constructor(a) {
        super();
        this.a = a;
      }
      toString() { return "CCh(" + globalThis.Predef.render(this.a) + ")"; }
    };
    const CNil$class = class CNil extends pretty.CSeq {
      constructor() {
        super();
      }
      toString() { return "CNil"; }
    };
    this.CNil = new CNil$class;
    this.CNil.class = CNil$class;
    const CNewline$class = class CNewline extends pretty.CSeq {
      constructor() {
        super();
      }
      toString() { return "CNewline"; }
    };
    this.CNewline = new CNewline$class;
    this.CNewline.class = CNewline$class;
    this.PprStyle = class PprStyle {
      constructor() {}
      toString() { return "PprStyle"; }
    };
    const PprForUser$class = class PprForUser extends pretty.PprStyle {
      constructor() {
        super();
      }
      toString() { return "PprForUser"; }
    };
    this.PprForUser = new PprForUser$class;
    this.PprForUser.class = PprForUser$class;
    const PprDebug$class = class PprDebug extends pretty.PprStyle {
      constructor() {
        super();
      }
      toString() { return "PprDebug"; }
    };
    this.PprDebug = new PprDebug$class;
    this.PprDebug.class = PprDebug$class;
    const PprShowAll$class = class PprShowAll extends pretty.PprStyle {
      constructor() {
        super();
      }
      toString() { return "PprShowAll"; }
    };
    this.PprShowAll = new PprShowAll$class;
    this.PprShowAll.class = PprShowAll$class;
    const PprInterface$class = class PprInterface extends pretty.PprStyle {
      constructor() {
        super();
      }
      toString() { return "PprInterface"; }
    };
    this.PprInterface = new PprInterface$class;
    this.PprInterface.class = PprInterface$class;
    this.cNil = pretty.CNil;
    this.cNL = pretty.CNewline;
    this.MkPrettyRep = function MkPrettyRep(cseq1, n1, b11, b21) {
      return new MkPrettyRep.class(cseq1, n1, b11, b21);
    };
    this.MkPrettyRep.class = class MkPrettyRep {
      constructor(cseq, n, b1, b2) {
        this.cseq = cseq;
        this.n = n;
        this.b1 = b1;
        this.b2 = b2;
      }
      toString() { return "MkPrettyRep(" + globalThis.Predef.render(this.cseq) + ", " + globalThis.Predef.render(this.n) + ", " + globalThis.Predef.render(this.b1) + ", " + globalThis.Predef.render(this.b2) + ")"; }
    };
    lambda12 = (undefined, function () {
      let tmp;
      tmp = pretty.testPretty_nofib();
      return NofibPrelude.nofibListToString(tmp)
    });
    BenchmarkPrelude.benchmark(lambda12)
  }
  static cAppend(cs1, cs2) {
    return pretty.CAppend(cs1, cs2)
  } 
  static cIndent(n, cs) {
    return pretty.CIndent(n, cs)
  } 
  static cStr(s) {
    return pretty.CStr(s)
  } 
  static cCh(c) {
    return pretty.CCh(c)
  } 
  static mkIndent(n1, s1) {
    let scrut, scrut1, tmp, tmp1, tmp2, tmp3;
    scrut1 = n1 === 0;
    if (scrut1 === true) {
      return s1
    } else {
      scrut = n1 >= 8;
      if (scrut === true) {
        tmp = n1 - 8;
        tmp1 = pretty.mkIndent(tmp, s1);
        return NofibPrelude.Cons("\t", tmp1)
      } else {
        tmp2 = n1 - 1;
        tmp3 = pretty.mkIndent(tmp2, s1);
        return NofibPrelude.Cons(" ", tmp3)
      }
    }
  } 
  static flattenS(nlp, seqs) {
    let param0, param1, first1, first0, col, seq, seqs1;
    if (seqs instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (seqs instanceof NofibPrelude.Cons.class) {
      param0 = seqs.head;
      param1 = seqs.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        col = first0;
        seq = first1;
        seqs1 = param1;
        return pretty.flatten(col, nlp, seq, seqs1)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static flatten(n2, nlp1, cseq, seqs1) {
    let param0, c1, param01, s2, param02, param1, n_, seq, param03, param11, seq1, seq2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    if (cseq instanceof pretty.CNil.class) {
      return pretty.flattenS(nlp1, seqs1)
    } else if (cseq instanceof pretty.CAppend.class) {
      param03 = cseq.a;
      param11 = cseq.b;
      seq1 = param03;
      seq2 = param11;
      tmp = NofibPrelude.Cons([
        n2,
        seq2
      ], seqs1);
      return pretty.flatten(n2, nlp1, seq1, tmp)
    } else if (cseq instanceof pretty.CIndent.class) {
      param02 = cseq.a;
      param1 = cseq.b;
      n_ = param02;
      seq = param1;
      tmp1 = n_ + n2;
      return pretty.flatten(tmp1, nlp1, seq, seqs1)
    } else if (cseq instanceof pretty.CNewline.class) {
      tmp2 = pretty.flattenS(true, seqs1);
      return NofibPrelude.Cons("\n", tmp2)
    } else if (cseq instanceof pretty.CStr.class) {
      param01 = cseq.a;
      s2 = param01;
      if (nlp1 === true) {
        tmp3 = pretty.flattenS(false, seqs1);
        tmp4 = NofibPrelude.append(s2, tmp3);
        return pretty.mkIndent(n2, tmp4)
      } else {
        tmp5 = pretty.flattenS(false, seqs1);
        return NofibPrelude.append(s2, tmp5)
      }
    } else if (cseq instanceof pretty.CCh.class) {
      param0 = cseq.a;
      c1 = param0;
      if (nlp1 === true) {
        tmp6 = pretty.flattenS(false, seqs1);
        tmp7 = NofibPrelude.Cons(c1, tmp6);
        return pretty.mkIndent(n2, tmp7)
      } else {
        tmp8 = pretty.flattenS(false, seqs1);
        return NofibPrelude.Cons(c1, tmp8)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static cShow(seq) {
    return pretty.flatten(0, true, seq, NofibPrelude.Nil)
  } 
  static ppShow(width, p) {
    let scrut, param0, param1, param2, param3, seq1, ll, emp, sl;
    scrut = runtime.safeCall(p(width, false));
    if (scrut instanceof pretty.MkPrettyRep.class) {
      param0 = scrut.cseq;
      param1 = scrut.n;
      param2 = scrut.b1;
      param3 = scrut.b2;
      seq1 = param0;
      ll = param1;
      emp = param2;
      sl = param3;
      return pretty.cShow(seq1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static ppUnformatted(p1) {
    let scrut, param0, param1, param2, param3, seq1, ll, emp, sl;
    scrut = runtime.safeCall(p1(80, false));
    if (scrut instanceof pretty.MkPrettyRep.class) {
      param0 = scrut.cseq;
      param1 = scrut.n;
      param2 = scrut.b1;
      param3 = scrut.b2;
      seq1 = param0;
      ll = param1;
      emp = param2;
      sl = param3;
      return pretty.cShow(seq1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static ppNil(width1, is_vert) {
    let tmp;
    tmp = width1 >= 0;
    return pretty.MkPrettyRep(pretty.cNil, 0, true, tmp)
  } 
  static ppStr(s2, width2, is_vert1) {
    let ls, tmp, tmp1, tmp2;
    tmp = NofibPrelude.listLen(s2);
    ls = tmp;
    tmp1 = pretty.cStr(s2);
    tmp2 = width2 >= ls;
    return pretty.MkPrettyRep(tmp1, ls, false, tmp2)
  } 
  static ppChar(c1, width3, is_vert2) {
    let tmp, tmp1;
    tmp = pretty.cCh(c1);
    tmp1 = width3 >= 1;
    return pretty.MkPrettyRep(tmp, 1, false, tmp1)
  } 
  static ppInt(n3, width4, is_vert3) {
    let tmp, tmp1;
    tmp = NofibPrelude.stringOfInt(n3);
    tmp1 = NofibPrelude.nofibStringToList(tmp);
    return pretty.ppStr(tmp1, width4, is_vert3)
  } 
  static pp_SP(a, b) {
    let tmp;
    tmp = NofibPrelude.nofibStringToList(", ");
    return pretty.ppStr(tmp, a, b)
  } 
  static ppSP(a1, b1) {
    return pretty.ppChar(" ", a1, b1)
  } 
  static ppLbrack(a2, b2) {
    return pretty.ppChar("[", a2, b2)
  } 
  static ppRbrack(a3, b3) {
    return pretty.ppChar("]", a3, b3)
  } 
  static ppLparen(a4, b4) {
    return pretty.ppChar("(", a4, b4)
  } 
  static ppRparen(a5, b5) {
    return pretty.ppChar(")", a5, b5)
  } 
  static ppSemi(a6, b6) {
    return pretty.ppChar(";", a6, b6)
  } 
  static ppComma(a7, b7) {
    return pretty.ppChar(",", a7, b7)
  } 
  static andL(a8, b8) {
    if (a8 === true) {
      return b8
    } else {
      return false
    }
  } 
  static orL(a9, b9) {
    if (a9 === true) {
      return true
    } else {
      return b9
    }
  } 
  static ppBeside(p11, p2, width5, is_vert4) {
    let scrut, param0, param1, param2, param3, seq1, ll1, emp1, sl1, scrut1, param01, param11, param21, param31, seq2, ll2, emp2, sl2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    scrut = runtime.safeCall(p11(width5, false));
    if (scrut instanceof pretty.MkPrettyRep.class) {
      param0 = scrut.cseq;
      param1 = scrut.n;
      param2 = scrut.b1;
      param3 = scrut.b2;
      seq1 = param0;
      ll1 = param1;
      emp1 = param2;
      sl1 = param3;
      tmp = width5 - ll1;
      scrut1 = runtime.safeCall(p2(tmp, false));
      if (scrut1 instanceof pretty.MkPrettyRep.class) {
        param01 = scrut1.cseq;
        param11 = scrut1.n;
        param21 = scrut1.b1;
        param31 = scrut1.b2;
        seq2 = param01;
        ll2 = param11;
        emp2 = param21;
        sl2 = param31;
        tmp1 = pretty.cIndent(ll1, seq2);
        tmp2 = pretty.cAppend(seq1, tmp1);
        tmp3 = ll1 + ll2;
        tmp4 = pretty.andL(emp1, emp2);
        tmp5 = width5 >= 0;
        tmp6 = pretty.andL(sl1, sl2);
        tmp7 = pretty.andL(tmp5, tmp6);
        return pretty.MkPrettyRep(tmp2, tmp3, tmp4, tmp7)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static ppBesides(ps) {
    if (ps instanceof NofibPrelude.Nil.class) {
      return pretty.ppNil
    } else {
      return NofibPrelude.foldr1(lambda, ps)
    }
  } 
  static ppBesideSP(p12, p21, width6, is_vert5) {
    let scrut, param0, param1, param2, param3, seq1, ll1, emp1, sl1, li, scrut1, param01, param11, param21, param31, seq2, ll2, emp2, sl2, wi, sp, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
    scrut = runtime.safeCall(p12(width6, false));
    if (scrut instanceof pretty.MkPrettyRep.class) {
      param0 = scrut.cseq;
      param1 = scrut.n;
      param2 = scrut.b1;
      param3 = scrut.b2;
      seq1 = param0;
      ll1 = param1;
      emp1 = param2;
      sl1 = param3;
      if (emp1 === true) {
        tmp = 0;
      } else {
        tmp = ll1 + 1;
      }
      li = tmp;
      tmp1 = width6 - li;
      scrut1 = runtime.safeCall(p21(tmp1, false));
      if (scrut1 instanceof pretty.MkPrettyRep.class) {
        param01 = scrut1.cseq;
        param11 = scrut1.n;
        param21 = scrut1.b1;
        param31 = scrut1.b2;
        seq2 = param01;
        ll2 = param11;
        emp2 = param21;
        sl2 = param31;
        if (emp1 === true) {
          tmp2 = 0;
        } else {
          tmp2 = 1;
        }
        wi = tmp2;
        scrut2 = pretty.orL(emp1, emp2);
        if (scrut2 === true) {
          tmp3 = pretty.cNil;
        } else {
          tmp3 = pretty.cCh(" ");
        }
        sp = tmp3;
        tmp4 = pretty.cIndent(li, seq2);
        tmp5 = pretty.cAppend(sp, tmp4);
        tmp6 = pretty.cAppend(seq1, tmp5);
        tmp7 = li + ll2;
        tmp8 = pretty.andL(emp1, emp2);
        tmp9 = width6 >= wi;
        tmp10 = pretty.andL(sl1, sl2);
        tmp11 = pretty.andL(tmp9, tmp10);
        return pretty.MkPrettyRep(tmp6, tmp7, tmp8, tmp11)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static ppCat(ps1) {
    if (ps1 instanceof NofibPrelude.Nil.class) {
      return pretty.ppNil
    } else {
      return NofibPrelude.foldr1(lambda2, ps1)
    }
  } 
  static ppAbove(p13, p22, width7, is_vert6) {
    let scrut, param0, param1, param2, param3, seq1, ll1, emp1, sl1, scrut1, param01, param11, param21, param31, seq2, ll2, emp2, sl2, nl, scrut2, tmp, tmp1, tmp2, tmp3;
    scrut = runtime.safeCall(p13(width7, true));
    if (scrut instanceof pretty.MkPrettyRep.class) {
      param0 = scrut.cseq;
      param1 = scrut.n;
      param2 = scrut.b1;
      param3 = scrut.b2;
      seq1 = param0;
      ll1 = param1;
      emp1 = param2;
      sl1 = param3;
      scrut1 = runtime.safeCall(p22(width7, true));
      if (scrut1 instanceof pretty.MkPrettyRep.class) {
        param01 = scrut1.cseq;
        param11 = scrut1.n;
        param21 = scrut1.b1;
        param31 = scrut1.b2;
        seq2 = param01;
        ll2 = param11;
        emp2 = param21;
        sl2 = param31;
        scrut2 = pretty.orL(emp1, emp2);
        if (scrut2 === true) {
          tmp = pretty.cNil;
        } else {
          tmp = pretty.cNL;
        }
        nl = tmp;
        tmp1 = pretty.cAppend(nl, seq2);
        tmp2 = pretty.cAppend(seq1, tmp1);
        tmp3 = pretty.andL(emp1, emp2);
        return pretty.MkPrettyRep(tmp2, ll2, tmp3, false)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static ppAboves(ps2, a10, b10) {
    let tmp;
    if (ps2 instanceof NofibPrelude.Nil.class) {
      return pretty.ppNil(a10, b10)
    } else {
      tmp = NofibPrelude.foldr1(lambda4, ps2);
      return runtime.safeCall(tmp(a10, b10))
    }
  } 
  static ppNest(n4, p3, width8, is_vert7) {
    let scrut, param0, param1, param2, param3, seq1, ll, emp, sl, tmp, tmp1, tmp2;
    if (is_vert7 === true) {
      tmp = width8 - n4;
      scrut = runtime.safeCall(p3(tmp, true));
      if (scrut instanceof pretty.MkPrettyRep.class) {
        param0 = scrut.cseq;
        param1 = scrut.n;
        param2 = scrut.b1;
        param3 = scrut.b2;
        seq1 = param0;
        ll = param1;
        emp = param2;
        sl = param3;
        tmp1 = pretty.cIndent(n4, seq1);
        tmp2 = ll + n4;
        return pretty.MkPrettyRep(tmp1, tmp2, emp, sl)
      } else {
        return runtime.safeCall(p3(width8, false))
      }
    } else {
      return runtime.safeCall(p3(width8, false))
    }
  } 
  static ppHang(p14, n5, p23, width9, is_vert8) {
    let scrut, param0, param1, param2, param3, seq1, ll1, emp1, sl1, scrut1, param01, param11, param21, param31, seq2, ll2, emp2, sl2, scrut2, param02, param12, param22, param32, seq2_, ll2_, emp2_, sl2_, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
    scrut = runtime.safeCall(p14(width9, false));
    if (scrut instanceof pretty.MkPrettyRep.class) {
      param0 = scrut.cseq;
      param1 = scrut.n;
      param2 = scrut.b1;
      param3 = scrut.b2;
      seq1 = param0;
      ll1 = param1;
      emp1 = param2;
      sl1 = param3;
      tmp = ll1 + 1;
      tmp1 = width9 - tmp;
      scrut1 = runtime.safeCall(p23(tmp1, false));
      if (scrut1 instanceof pretty.MkPrettyRep.class) {
        param01 = scrut1.cseq;
        param11 = scrut1.n;
        param21 = scrut1.b1;
        param31 = scrut1.b2;
        seq2 = param01;
        ll2 = param11;
        emp2 = param21;
        sl2 = param31;
        tmp2 = width9 - n5;
        scrut2 = runtime.safeCall(p23(tmp2, false));
        if (scrut2 instanceof pretty.MkPrettyRep.class) {
          param02 = scrut2.cseq;
          param12 = scrut2.n;
          param22 = scrut2.b1;
          param32 = scrut2.b2;
          seq2_ = param02;
          ll2_ = param12;
          emp2_ = param22;
          sl2_ = param32;
          if (emp1 === true) {
            return runtime.safeCall(p23(width9, is_vert8))
          } else {
            tmp3 = ll1 <= n5;
            scrut3 = pretty.orL(tmp3, sl2);
            if (scrut3 === true) {
              tmp4 = pretty.cCh(" ");
              tmp5 = ll1 + 1;
              tmp6 = pretty.cIndent(tmp5, seq2);
              tmp7 = pretty.cAppend(tmp4, tmp6);
              tmp8 = pretty.cAppend(seq1, tmp7);
              tmp9 = ll1 + 1;
              tmp10 = tmp9 + ll2;
              tmp11 = pretty.andL(sl1, sl2);
              return pretty.MkPrettyRep(tmp8, tmp10, false, tmp11)
            } else {
              tmp12 = pretty.cIndent(n5, seq2_);
              tmp13 = pretty.cAppend(pretty.cNL, tmp12);
              tmp14 = pretty.cAppend(seq1, tmp13);
              return pretty.MkPrettyRep(tmp14, ll2_, false, false)
            }
          }
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
  static ppSep(ps3, width10, is_vert9) {
    let scrut, param0, param1, param2, param3, seq1, ll, emp, sl, param01, param11, p4;
    if (ps3 instanceof NofibPrelude.Nil.class) {
      return pretty.ppNil(width10, is_vert9)
    } else if (ps3 instanceof NofibPrelude.Cons.class) {
      param01 = ps3.head;
      param11 = ps3.tail;
      p4 = param01;
      if (param11 instanceof NofibPrelude.Nil.class) {
        return runtime.safeCall(p4(width10, is_vert9))
      } else {
        scrut = pretty.ppCat(ps3, width10, is_vert9);
        if (scrut instanceof pretty.MkPrettyRep.class) {
          param0 = scrut.cseq;
          param1 = scrut.n;
          param2 = scrut.b1;
          param3 = scrut.b2;
          seq1 = param0;
          ll = param1;
          emp = param2;
          sl = param3;
          if (sl === true) {
            return pretty.MkPrettyRep(seq1, ll, emp, sl)
          } else {
            return pretty.ppAboves(ps3, width10, is_vert9)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      }
    } else {
      scrut = pretty.ppCat(ps3, width10, is_vert9);
      if (scrut instanceof pretty.MkPrettyRep.class) {
        param0 = scrut.cseq;
        param1 = scrut.n;
        param2 = scrut.b1;
        param3 = scrut.b2;
        seq1 = param0;
        ll = param1;
        emp = param2;
        sl = param3;
        if (sl === true) {
          return pretty.MkPrettyRep(seq1, ll, emp, sl)
        } else {
          return pretty.ppAboves(ps3, width10, is_vert9)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } 
  static testPretty_nofib() {
    let pp_words, tmp, tmp1, tmp2, pretty_stuff$this;
    tmp = NofibPrelude.replicate(50, pp_word);
    pp_words = tmp;
    pretty_stuff$this = runtime.safeCall(pretty_stuff(pp_words));
    tmp1 = pretty.ppShow(80, pretty_stuff$this);
    tmp2 = NofibPrelude.nofibStringToList("\n");
    return NofibPrelude.append(tmp1, tmp2)
  }
  static toString() { return "pretty"; }
};
let pretty = pretty1; export default pretty;
