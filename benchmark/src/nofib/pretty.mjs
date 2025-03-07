import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let CNewline1, ppHang, flattenS, testPretty_nofib, ppRbrack, PprStyle1, ppCat, ppAboves, ppUnformatted, cIndent, andL, flatten, ppNest, cShow, ppNil, CStr1, cStr, CIndent1, cCh, ppSP, ppLbrack, MkPrettyRep1, PprInterface1, CAppend1, ppBeside, pp_SP, orL, ppSemi, ppSep, ppRparen, cAppend, ppAbove, ppChar, ppStr, CSeq1, PprShowAll1, ppLparen, CCh1, ppBesideSP, PprForUser1, mkIndent, PprDebug1, ppShow, ppComma, CNil1, ppInt, ppBesides, cNil, cNL, lambda;
cAppend = function cAppend(cs1, cs2) {
  return CAppend1(cs1, cs2)
};
cIndent = function cIndent(n, cs) {
  return CIndent1(n, cs)
};
cStr = function cStr(s) {
  return CStr1(s)
};
cCh = function cCh(c) {
  return CCh1(c)
};
mkIndent = function mkIndent(n, s) {
  let scrut, scrut1, tmp, tmp1, tmp2, tmp3;
  scrut1 = n === 0;
  if (scrut1 === true) {
    return s
  } else {
    scrut = n >= 8;
    if (scrut === true) {
      tmp = n - 8;
      tmp1 = mkIndent(tmp, s);
      return NofibPrelude.Cons("\t", tmp1)
    } else {
      tmp2 = n - 1;
      tmp3 = mkIndent(tmp2, s);
      return NofibPrelude.Cons(" ", tmp3)
    }
  }
};
flattenS = function flattenS(nlp, seqs) {
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
      return flatten(col, nlp, seq, seqs1)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
flatten = function flatten(n, nlp, cseq, seqs) {
  let param0, c, param01, s, param02, param1, n_, seq, param03, param11, seq1, seq2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
  if (cseq instanceof CNil1.class) {
    return flattenS(nlp, seqs)
  } else if (cseq instanceof CAppend1.class) {
    param03 = cseq.a;
    param11 = cseq.b;
    seq1 = param03;
    seq2 = param11;
    tmp = NofibPrelude.Cons([
      n,
      seq2
    ], seqs);
    return flatten(n, nlp, seq1, tmp)
  } else if (cseq instanceof CIndent1.class) {
    param02 = cseq.a;
    param1 = cseq.b;
    n_ = param02;
    seq = param1;
    tmp1 = n_ + n;
    return flatten(tmp1, nlp, seq, seqs)
  } else if (cseq instanceof CNewline1.class) {
    tmp2 = flattenS(true, seqs);
    return NofibPrelude.Cons("\n", tmp2)
  } else if (cseq instanceof CStr1.class) {
    param01 = cseq.a;
    s = param01;
    if (nlp === true) {
      tmp3 = flattenS(false, seqs);
      tmp4 = NofibPrelude.append(s, tmp3);
      return mkIndent(n, tmp4)
    } else {
      tmp5 = flattenS(false, seqs);
      return NofibPrelude.append(s, tmp5)
    }
  } else if (cseq instanceof CCh1.class) {
    param0 = cseq.a;
    c = param0;
    if (nlp === true) {
      tmp6 = flattenS(false, seqs);
      tmp7 = NofibPrelude.Cons(c, tmp6);
      return mkIndent(n, tmp7)
    } else {
      tmp8 = flattenS(false, seqs);
      return NofibPrelude.Cons(c, tmp8)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
cShow = function cShow(seq) {
  return flatten(0, true, seq, NofibPrelude.Nil)
};
ppShow = function ppShow(width, p) {
  let scrut, param0, param1, param2, param3, seq, ll, emp, sl;
  scrut = runtime.safeCall(p(width, false));
  if (scrut instanceof MkPrettyRep1.class) {
    param0 = scrut.cseq;
    param1 = scrut.n;
    param2 = scrut.b1;
    param3 = scrut.b2;
    seq = param0;
    ll = param1;
    emp = param2;
    sl = param3;
    return cShow(seq)
  } else {
    throw new globalThis.Error("match error");
  }
};
ppUnformatted = function ppUnformatted(p) {
  let scrut, param0, param1, param2, param3, seq, ll, emp, sl;
  scrut = runtime.safeCall(p(80, false));
  if (scrut instanceof MkPrettyRep1.class) {
    param0 = scrut.cseq;
    param1 = scrut.n;
    param2 = scrut.b1;
    param3 = scrut.b2;
    seq = param0;
    ll = param1;
    emp = param2;
    sl = param3;
    return cShow(seq)
  } else {
    throw new globalThis.Error("match error");
  }
};
ppNil = function ppNil(width, is_vert) {
  let tmp;
  tmp = width >= 0;
  return MkPrettyRep1(cNil, 0, true, tmp)
};
ppStr = function ppStr(s, width, is_vert) {
  let ls, tmp, tmp1, tmp2;
  tmp = NofibPrelude.listLen(s);
  ls = tmp;
  tmp1 = cStr(s);
  tmp2 = width >= ls;
  return MkPrettyRep1(tmp1, ls, false, tmp2)
};
ppChar = function ppChar(c, width, is_vert) {
  let tmp, tmp1;
  tmp = cCh(c);
  tmp1 = width >= 1;
  return MkPrettyRep1(tmp, 1, false, tmp1)
};
ppInt = function ppInt(n, width, is_vert) {
  let tmp, tmp1;
  tmp = NofibPrelude.stringOfInt(n);
  tmp1 = NofibPrelude.nofibStringToList(tmp);
  return ppStr(tmp1, width, is_vert)
};
pp_SP = function pp_SP(a, b) {
  let tmp;
  tmp = NofibPrelude.nofibStringToList(", ");
  return ppStr(tmp, a, b)
};
ppSP = function ppSP(a, b) {
  return ppChar(" ", a, b)
};
ppLbrack = function ppLbrack(a, b) {
  return ppChar("[", a, b)
};
ppRbrack = function ppRbrack(a, b) {
  return ppChar("]", a, b)
};
ppLparen = function ppLparen(a, b) {
  return ppChar("(", a, b)
};
ppRparen = function ppRparen(a, b) {
  return ppChar(")", a, b)
};
ppSemi = function ppSemi(a, b) {
  return ppChar(";", a, b)
};
ppComma = function ppComma(a, b) {
  return ppChar(",", a, b)
};
andL = function andL(a, b) {
  if (a === true) {
    return b
  } else {
    return false
  }
};
orL = function orL(a, b) {
  if (a === true) {
    return true
  } else {
    return b
  }
};
ppBeside = function ppBeside(p1, p2, width, is_vert) {
  let scrut, param0, param1, param2, param3, seq1, ll1, emp1, sl1, scrut1, param01, param11, param21, param31, seq2, ll2, emp2, sl2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  scrut = runtime.safeCall(p1(width, false));
  if (scrut instanceof MkPrettyRep1.class) {
    param0 = scrut.cseq;
    param1 = scrut.n;
    param2 = scrut.b1;
    param3 = scrut.b2;
    seq1 = param0;
    ll1 = param1;
    emp1 = param2;
    sl1 = param3;
    tmp = width - ll1;
    scrut1 = runtime.safeCall(p2(tmp, false));
    if (scrut1 instanceof MkPrettyRep1.class) {
      param01 = scrut1.cseq;
      param11 = scrut1.n;
      param21 = scrut1.b1;
      param31 = scrut1.b2;
      seq2 = param01;
      ll2 = param11;
      emp2 = param21;
      sl2 = param31;
      tmp1 = cIndent(ll1, seq2);
      tmp2 = cAppend(seq1, tmp1);
      tmp3 = ll1 + ll2;
      tmp4 = andL(emp1, emp2);
      tmp5 = width >= 0;
      tmp6 = andL(sl1, sl2);
      tmp7 = andL(tmp5, tmp6);
      return MkPrettyRep1(tmp2, tmp3, tmp4, tmp7)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
ppBesides = function ppBesides(ps) {
  let lambda1;
  if (ps instanceof NofibPrelude.Nil.class) {
    return ppNil
  } else {
    lambda1 = (undefined, function (a, b) {
      let lambda2;
      lambda2 = (undefined, function (c, d) {
        return ppBeside(a, b, c, d)
      });
      return lambda2
    });
    return NofibPrelude.foldr1(lambda1, ps)
  }
};
ppBesideSP = function ppBesideSP(p1, p2, width, is_vert) {
  let scrut, param0, param1, param2, param3, seq1, ll1, emp1, sl1, li, scrut1, param01, param11, param21, param31, seq2, ll2, emp2, sl2, wi, sp, scrut2, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
  scrut = runtime.safeCall(p1(width, false));
  if (scrut instanceof MkPrettyRep1.class) {
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
    tmp1 = width - li;
    scrut1 = runtime.safeCall(p2(tmp1, false));
    if (scrut1 instanceof MkPrettyRep1.class) {
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
      scrut2 = orL(emp1, emp2);
      if (scrut2 === true) {
        tmp3 = cNil;
      } else {
        tmp3 = cCh(" ");
      }
      sp = tmp3;
      tmp4 = cIndent(li, seq2);
      tmp5 = cAppend(sp, tmp4);
      tmp6 = cAppend(seq1, tmp5);
      tmp7 = li + ll2;
      tmp8 = andL(emp1, emp2);
      tmp9 = width >= wi;
      tmp10 = andL(sl1, sl2);
      tmp11 = andL(tmp9, tmp10);
      return MkPrettyRep1(tmp6, tmp7, tmp8, tmp11)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
ppCat = function ppCat(ps) {
  let lambda1;
  if (ps instanceof NofibPrelude.Nil.class) {
    return ppNil
  } else {
    lambda1 = (undefined, function (a, b) {
      let lambda2;
      lambda2 = (undefined, function (c, d) {
        return ppBesideSP(a, b, c, d)
      });
      return lambda2
    });
    return NofibPrelude.foldr1(lambda1, ps)
  }
};
ppAbove = function ppAbove(p1, p2, width, is_vert) {
  let scrut, param0, param1, param2, param3, seq1, ll1, emp1, sl1, scrut1, param01, param11, param21, param31, seq2, ll2, emp2, sl2, nl, scrut2, tmp, tmp1, tmp2, tmp3;
  scrut = runtime.safeCall(p1(width, true));
  if (scrut instanceof MkPrettyRep1.class) {
    param0 = scrut.cseq;
    param1 = scrut.n;
    param2 = scrut.b1;
    param3 = scrut.b2;
    seq1 = param0;
    ll1 = param1;
    emp1 = param2;
    sl1 = param3;
    scrut1 = runtime.safeCall(p2(width, true));
    if (scrut1 instanceof MkPrettyRep1.class) {
      param01 = scrut1.cseq;
      param11 = scrut1.n;
      param21 = scrut1.b1;
      param31 = scrut1.b2;
      seq2 = param01;
      ll2 = param11;
      emp2 = param21;
      sl2 = param31;
      scrut2 = orL(emp1, emp2);
      if (scrut2 === true) {
        tmp = cNil;
      } else {
        tmp = cNL;
      }
      nl = tmp;
      tmp1 = cAppend(nl, seq2);
      tmp2 = cAppend(seq1, tmp1);
      tmp3 = andL(emp1, emp2);
      return MkPrettyRep1(tmp2, ll2, tmp3, false)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
ppAboves = function ppAboves(ps, a, b) {
  let tmp, lambda1;
  if (ps instanceof NofibPrelude.Nil.class) {
    return ppNil(a, b)
  } else {
    lambda1 = (undefined, function (a1, b1) {
      let lambda2;
      lambda2 = (undefined, function (c, d) {
        return ppAbove(a1, b1, c, d)
      });
      return lambda2
    });
    tmp = NofibPrelude.foldr1(lambda1, ps);
    return runtime.safeCall(tmp(a, b))
  }
};
ppNest = function ppNest(n, p, width, is_vert) {
  let scrut, param0, param1, param2, param3, seq, ll, emp, sl, tmp, tmp1, tmp2;
  if (is_vert === true) {
    tmp = width - n;
    scrut = runtime.safeCall(p(tmp, true));
    if (scrut instanceof MkPrettyRep1.class) {
      param0 = scrut.cseq;
      param1 = scrut.n;
      param2 = scrut.b1;
      param3 = scrut.b2;
      seq = param0;
      ll = param1;
      emp = param2;
      sl = param3;
      tmp1 = cIndent(n, seq);
      tmp2 = ll + n;
      return MkPrettyRep1(tmp1, tmp2, emp, sl)
    } else {
      return runtime.safeCall(p(width, false))
    }
  } else {
    return runtime.safeCall(p(width, false))
  }
};
ppHang = function ppHang(p1, n, p2, width, is_vert) {
  let scrut, param0, param1, param2, param3, seq1, ll1, emp1, sl1, scrut1, param01, param11, param21, param31, seq2, ll2, emp2, sl2, scrut2, param02, param12, param22, param32, seq2_, ll2_, emp2_, sl2_, scrut3, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14;
  scrut = runtime.safeCall(p1(width, false));
  if (scrut instanceof MkPrettyRep1.class) {
    param0 = scrut.cseq;
    param1 = scrut.n;
    param2 = scrut.b1;
    param3 = scrut.b2;
    seq1 = param0;
    ll1 = param1;
    emp1 = param2;
    sl1 = param3;
    tmp = ll1 + 1;
    tmp1 = width - tmp;
    scrut1 = runtime.safeCall(p2(tmp1, false));
    if (scrut1 instanceof MkPrettyRep1.class) {
      param01 = scrut1.cseq;
      param11 = scrut1.n;
      param21 = scrut1.b1;
      param31 = scrut1.b2;
      seq2 = param01;
      ll2 = param11;
      emp2 = param21;
      sl2 = param31;
      tmp2 = width - n;
      scrut2 = runtime.safeCall(p2(tmp2, false));
      if (scrut2 instanceof MkPrettyRep1.class) {
        param02 = scrut2.cseq;
        param12 = scrut2.n;
        param22 = scrut2.b1;
        param32 = scrut2.b2;
        seq2_ = param02;
        ll2_ = param12;
        emp2_ = param22;
        sl2_ = param32;
        if (emp1 === true) {
          return runtime.safeCall(p2(width, is_vert))
        } else {
          tmp3 = ll1 <= n;
          scrut3 = orL(tmp3, sl2);
          if (scrut3 === true) {
            tmp4 = cCh(" ");
            tmp5 = ll1 + 1;
            tmp6 = cIndent(tmp5, seq2);
            tmp7 = cAppend(tmp4, tmp6);
            tmp8 = cAppend(seq1, tmp7);
            tmp9 = ll1 + 1;
            tmp10 = tmp9 + ll2;
            tmp11 = andL(sl1, sl2);
            return MkPrettyRep1(tmp8, tmp10, false, tmp11)
          } else {
            tmp12 = cIndent(n, seq2_);
            tmp13 = cAppend(cNL, tmp12);
            tmp14 = cAppend(seq1, tmp13);
            return MkPrettyRep1(tmp14, ll2_, false, false)
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
};
ppSep = function ppSep(ps, width, is_vert) {
  let scrut, param0, param1, param2, param3, seq, ll, emp, sl, param01, param11, p;
  if (ps instanceof NofibPrelude.Nil.class) {
    return ppNil(width, is_vert)
  } else if (ps instanceof NofibPrelude.Cons.class) {
    param01 = ps.head;
    param11 = ps.tail;
    p = param01;
    if (param11 instanceof NofibPrelude.Nil.class) {
      return runtime.safeCall(p(width, is_vert))
    } else {
      scrut = ppCat(ps, width, is_vert);
      if (scrut instanceof MkPrettyRep1.class) {
        param0 = scrut.cseq;
        param1 = scrut.n;
        param2 = scrut.b1;
        param3 = scrut.b2;
        seq = param0;
        ll = param1;
        emp = param2;
        sl = param3;
        if (sl === true) {
          return MkPrettyRep1(seq, ll, emp, sl)
        } else {
          return ppAboves(ps, width, is_vert)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } else {
    scrut = ppCat(ps, width, is_vert);
    if (scrut instanceof MkPrettyRep1.class) {
      param0 = scrut.cseq;
      param1 = scrut.n;
      param2 = scrut.b1;
      param3 = scrut.b2;
      seq = param0;
      ll = param1;
      emp = param2;
      sl = param3;
      if (sl === true) {
        return MkPrettyRep1(seq, ll, emp, sl)
      } else {
        return ppAboves(ps, width, is_vert)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  }
};
testPretty_nofib = function testPretty_nofib() {
  let pp_word, pretty_stuff, pp_words, tmp, tmp1, tmp2;
  pp_word = function pp_word(a, b) {
    let tmp3;
    tmp3 = NofibPrelude.nofibStringToList("xxxxx");
    return ppStr(tmp3, a, b)
  };
  pretty_stuff = function pretty_stuff(a, b) {
    let tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, lambda1, lambda2, lambda3, lambda4, lambda5;
    lambda1 = (undefined, function (a1, b1) {
      let tmp10;
      tmp10 = NofibPrelude.nofibStringToList("This is a string");
      return ppStr(tmp10, a1, b1)
    });
    tmp3 = NofibPrelude.Cons(lambda1, NofibPrelude.Nil);
    lambda2 = (undefined, function (a1, b1) {
      return ppChar("@", a1, b1)
    });
    tmp4 = NofibPrelude.Cons(lambda2, tmp3);
    lambda3 = (undefined, function (a1, b1) {
      let tmp10;
      tmp10 = - 42;
      return ppInt(tmp10, a1, b1)
    });
    tmp5 = NofibPrelude.Cons(lambda3, tmp4);
    tmp6 = ppBesides(tmp5);
    lambda4 = (undefined, function (a1, b1) {
      let tmp10, lambda6;
      tmp10 = ppCat(pp_words);
      lambda6 = (undefined, function (a2, b2) {
        let tmp11;
        tmp11 = NofibPrelude.nofibStringToList("This is the label");
        return ppStr(tmp11, a2, b2)
      });
      return ppHang(lambda6, 8, tmp10, a1, b1)
    });
    tmp7 = NofibPrelude.Cons(lambda4, NofibPrelude.Nil);
    lambda5 = (undefined, function (a1, b1) {
      return pp_SP(a1, b1)
    });
    tmp8 = NofibPrelude.Cons(lambda5, tmp7);
    tmp9 = NofibPrelude.Cons(tmp6, tmp8);
    return ppAboves(tmp9, a, b)
  };
  tmp = NofibPrelude.replicate(50, pp_word);
  pp_words = tmp;
  tmp1 = ppShow(80, pretty_stuff);
  tmp2 = NofibPrelude.nofibStringToList("\n");
  return NofibPrelude.append(tmp1, tmp2)
};
CSeq1 = class CSeq {
  constructor() {}
  toString() { return "CSeq"; }
};
CAppend1 = function CAppend(a1, b1) {
  return new CAppend.class(a1, b1);
};
CAppend1.class = class CAppend extends CSeq1 {
  constructor(a, b) {
    super();
    this.a = a;
    this.b = b;
  }
  toString() { return "CAppend(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
};
CIndent1 = function CIndent(a1, b1) {
  return new CIndent.class(a1, b1);
};
CIndent1.class = class CIndent extends CSeq1 {
  constructor(a, b) {
    super();
    this.a = a;
    this.b = b;
  }
  toString() { return "CIndent(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.b) + ")"; }
};
CStr1 = function CStr(a1) {
  return new CStr.class(a1);
};
CStr1.class = class CStr extends CSeq1 {
  constructor(a) {
    super();
    this.a = a;
  }
  toString() { return "CStr(" + globalThis.Predef.render(this.a) + ")"; }
};
CCh1 = function CCh(a1) {
  return new CCh.class(a1);
};
CCh1.class = class CCh extends CSeq1 {
  constructor(a) {
    super();
    this.a = a;
  }
  toString() { return "CCh(" + globalThis.Predef.render(this.a) + ")"; }
};
const CNil$class = class CNil extends CSeq1 {
  constructor() {
    super();
  }
  toString() { return "CNil"; }
}; CNil1 = new CNil$class;
CNil1.class = CNil$class;
const CNewline$class = class CNewline extends CSeq1 {
  constructor() {
    super();
  }
  toString() { return "CNewline"; }
}; CNewline1 = new CNewline$class;
CNewline1.class = CNewline$class;
PprStyle1 = class PprStyle {
  constructor() {}
  toString() { return "PprStyle"; }
};
const PprForUser$class = class PprForUser extends PprStyle1 {
  constructor() {
    super();
  }
  toString() { return "PprForUser"; }
}; PprForUser1 = new PprForUser$class;
PprForUser1.class = PprForUser$class;
const PprDebug$class = class PprDebug extends PprStyle1 {
  constructor() {
    super();
  }
  toString() { return "PprDebug"; }
}; PprDebug1 = new PprDebug$class;
PprDebug1.class = PprDebug$class;
const PprShowAll$class = class PprShowAll extends PprStyle1 {
  constructor() {
    super();
  }
  toString() { return "PprShowAll"; }
}; PprShowAll1 = new PprShowAll$class;
PprShowAll1.class = PprShowAll$class;
const PprInterface$class = class PprInterface extends PprStyle1 {
  constructor() {
    super();
  }
  toString() { return "PprInterface"; }
}; PprInterface1 = new PprInterface$class;
PprInterface1.class = PprInterface$class;
cNil = CNil1;
cNL = CNewline1;
MkPrettyRep1 = function MkPrettyRep(cseq1, n1, b11, b21) {
  return new MkPrettyRep.class(cseq1, n1, b11, b21);
};
MkPrettyRep1.class = class MkPrettyRep {
  constructor(cseq, n, b1, b2) {
    this.cseq = cseq;
    this.n = n;
    this.b1 = b1;
    this.b2 = b2;
  }
  toString() { return "MkPrettyRep(" + globalThis.Predef.render(this.cseq) + ", " + globalThis.Predef.render(this.n) + ", " + globalThis.Predef.render(this.b1) + ", " + globalThis.Predef.render(this.b2) + ")"; }
};
lambda = (undefined, function () {
  let tmp;
  tmp = testPretty_nofib();
  return NofibPrelude.nofibListToString(tmp)
});
BenchmarkPrelude.benchmark(lambda)