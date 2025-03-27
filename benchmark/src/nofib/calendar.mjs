import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let body, pad, banner, entries, pic, title, months, table, calendar1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda$, table$, pad$, pic$, body$, lambda$1;
lambda8 = (undefined, function (x) {
  return calendar1.cal(x)
});
banner = function banner(yr) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.stringOfInt(yr);
  tmp1 = NofibPrelude.nofibStringToList(tmp);
  tmp2 = calendar1.cjustify(75, tmp1);
  tmp3 = calendar1.emptyPic([
    1,
    75
  ]);
  return NofibPrelude.Cons(tmp2, tmp3)
};
lambda$1 = function lambda$(side, end, daynames, x) {
  let tmp;
  tmp = pic$(daynames, x);
  return pad$(side, end, tmp)
};
lambda7 = (undefined, function (side, end, daynames) {
  return (x) => {
    return lambda$1(side, end, daynames, x)
  }
});
body$ = function body$(side, end, daynames, yr) {
  let tmp, tmp1, lambda$this;
  tmp = months(yr);
  lambda$this = runtime.safeCall(lambda7(side, end, daynames));
  tmp1 = NofibPrelude.map(lambda$this, tmp);
  return calendar1.block(3, tmp1)
};
body = function body(side, end, daynames) {
  return (yr) => {
    return body$(side, end, daynames, yr)
  }
};
pic$ = function pic$(daynames, mnfdml) {
  let first2, first1, first0, mn, fd, ml, tmp, tmp1;
  if (globalThis.Array.isArray(mnfdml) && mnfdml.length === 3) {
    first0 = mnfdml[0];
    first1 = mnfdml[1];
    first2 = mnfdml[2];
    mn = first0;
    fd = first1;
    ml = first2;
    tmp = title(mn);
    tmp1 = table$(daynames, fd, ml);
    return NofibPrelude.append(tmp, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
pic = function pic(daynames) {
  return (mnfdml) => {
    return pic$(daynames, mnfdml)
  }
};
pad$ = function pad$(side, end, p) {
  let tmp, tmp1;
  tmp = NofibPrelude.zipWith(NofibPrelude.append, side, p);
  tmp1 = NofibPrelude.zipWith(NofibPrelude.append, tmp, side);
  return NofibPrelude.append(tmp1, end)
};
pad = function pad(side, end) {
  return (p) => {
    return pad$(side, end, p)
  }
};
title = function title(mn) {
  let tmp;
  tmp = calendar1.cjustify(21, mn);
  return NofibPrelude.Cons(tmp, NofibPrelude.Nil)
};
table$ = function table$(daynames, fd, ml) {
  let tmp;
  tmp = entries(fd, ml);
  return NofibPrelude.append(daynames, tmp)
};
table = function table(daynames) {
  return (fd, ml) => {
    return table$(daynames, fd, ml)
  }
};
entries = function entries(fd, ml) {
  let tmp;
  tmp = calendar1.dates(fd, ml);
  return calendar1.block(7, tmp)
};
months = function months(yer) {
  let tmp, tmp1;
  tmp = calendar1.firstDays(yer);
  tmp1 = calendar1.monthLengths(yer);
  return NofibPrelude.zip3(calendar1.monthNames, tmp, tmp1)
};
lambda$ = function lambda$(ml, d) {
  return calendar1.date(ml, d)
};
lambda6 = (undefined, function (ml) {
  return (d) => {
    return lambda$(ml, d)
  }
});
lambda4 = (undefined, function (a, b) {
  return a + b
});
lambda5 = (undefined, function (x) {
  return NofibPrelude.intMod(x, 7)
});
lambda3 = (undefined, function (a, b) {
  return NofibPrelude.append(a, b)
});
lambda2 = (undefined, function (a, b) {
  return NofibPrelude.zipWith(lambda3, a, b)
});
lambda1 = (undefined, function (a, b) {
  return NofibPrelude.append(a, b)
});
lambda = (undefined, function (x) {
  let tmp;
  tmp = NofibPrelude.Cons("\n", NofibPrelude.Nil);
  return NofibPrelude.append(x, tmp)
});
calendar1 = class calendar {
  static {
    calendar1 = calendar;
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, lambda9;
    tmp = NofibPrelude.nofibStringToList("January");
    tmp1 = NofibPrelude.nofibStringToList("February");
    tmp2 = NofibPrelude.nofibStringToList("March");
    tmp3 = NofibPrelude.nofibStringToList("April");
    tmp4 = NofibPrelude.nofibStringToList("May");
    tmp5 = NofibPrelude.nofibStringToList("June");
    tmp6 = NofibPrelude.nofibStringToList("July");
    tmp7 = NofibPrelude.nofibStringToList("August");
    tmp8 = NofibPrelude.nofibStringToList("September");
    tmp9 = NofibPrelude.nofibStringToList("October");
    tmp10 = NofibPrelude.nofibStringToList("November");
    tmp11 = NofibPrelude.nofibStringToList("December");
    tmp12 = NofibPrelude.Cons(tmp11, NofibPrelude.Nil);
    tmp13 = NofibPrelude.Cons(tmp10, tmp12);
    tmp14 = NofibPrelude.Cons(tmp9, tmp13);
    tmp15 = NofibPrelude.Cons(tmp8, tmp14);
    tmp16 = NofibPrelude.Cons(tmp7, tmp15);
    tmp17 = NofibPrelude.Cons(tmp6, tmp16);
    tmp18 = NofibPrelude.Cons(tmp5, tmp17);
    tmp19 = NofibPrelude.Cons(tmp4, tmp18);
    tmp20 = NofibPrelude.Cons(tmp3, tmp19);
    tmp21 = NofibPrelude.Cons(tmp2, tmp20);
    tmp22 = NofibPrelude.Cons(tmp1, tmp21);
    tmp23 = NofibPrelude.Cons(tmp, tmp22);
    this.monthNames = tmp23;
    lambda9 = (undefined, function () {
      let tmp25, tmp26, tmp27;
      tmp25 = calendar.testCalendar_nofib(0);
      tmp26 = NofibPrelude.concat(tmp25);
      tmp27 = NofibPrelude.nofibListToString(tmp26);
      return BenchmarkPrelude.print(tmp27)
    });
    tmp24 = lambda9;
    BenchmarkPrelude.benchmark(tmp24)
  }
  static unlines(ls) {
    let tmp;
    tmp = NofibPrelude.map(lambda, ls);
    return NofibPrelude.concat(tmp)
  } 
  static height(p) {
    return NofibPrelude.listLen(p)
  } 
  static width(p1) {
    let tmp;
    tmp = NofibPrelude.head(p1);
    return NofibPrelude.listLen(tmp)
  } 
  static stack(ls1) {
    return NofibPrelude.foldr1(lambda1, ls1)
  } 
  static spread(ls2) {
    return NofibPrelude.foldr1(lambda2, ls2)
  } 
  static emptyPic(hw) {
    let first1, first0, h, w, tmp;
    if (globalThis.Array.isArray(hw) && hw.length === 2) {
      first0 = hw[0];
      first1 = hw[1];
      h = first0;
      w = first1;
      tmp = NofibPrelude.replicate(w, " ");
      return NofibPrelude.replicate(h, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static groop(n, xs) {
    let tmp, tmp1, tmp2;
    if (xs instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      tmp = NofibPrelude.take(n, xs);
      tmp1 = NofibPrelude.drop(n, xs);
      tmp2 = calendar.groop(n, tmp1);
      return NofibPrelude.Cons(tmp, tmp2)
    }
  } 
  static block(n1, t) {
    let tmp, tmp1;
    tmp = calendar.groop(n1, t);
    tmp1 = NofibPrelude.map(calendar.spread, tmp);
    return calendar.stack(tmp1)
  } 
  static blockT(n2, t1) {
    let tmp, tmp1;
    tmp = calendar.groop(n2, t1);
    tmp1 = NofibPrelude.map(calendar.stack, tmp);
    return calendar.stack(tmp1)
  } 
  static lframe(mn, p2) {
    let first1, first0, m, n3, h, w, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    if (globalThis.Array.isArray(mn) && mn.length === 2) {
      first0 = mn[0];
      first1 = mn[1];
      m = first0;
      n3 = first1;
      tmp = calendar.height(p2);
      h = tmp;
      tmp1 = calendar.width(p2);
      w = tmp1;
      tmp2 = n3 - w;
      tmp3 = calendar.emptyPic([
        h,
        tmp2
      ]);
      tmp4 = NofibPrelude.zipWith(NofibPrelude.append, p2, tmp3);
      tmp5 = m - h;
      tmp6 = calendar.emptyPic([
        tmp5,
        n3
      ]);
      return NofibPrelude.append(tmp4, tmp6)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static leap(year) {
    let scrut, tmp, tmp1, tmp2;
    tmp = NofibPrelude.intMod(year, 100);
    scrut = tmp == 0;
    if (scrut === true) {
      tmp1 = NofibPrelude.intMod(year, 400);
      return tmp1 == 0
    } else {
      tmp2 = NofibPrelude.intMod(year, 4);
      return tmp2 == 0
    }
  } 
  static monthLengths(year1) {
    let feb, scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
    scrut = calendar.leap(year1);
    if (scrut === true) {
      tmp = 29;
    } else {
      tmp = 28;
    }
    feb = tmp;
    tmp1 = NofibPrelude.Cons(31, NofibPrelude.Nil);
    tmp2 = NofibPrelude.Cons(30, tmp1);
    tmp3 = NofibPrelude.Cons(31, tmp2);
    tmp4 = NofibPrelude.Cons(30, tmp3);
    tmp5 = NofibPrelude.Cons(31, tmp4);
    tmp6 = NofibPrelude.Cons(31, tmp5);
    tmp7 = NofibPrelude.Cons(30, tmp6);
    tmp8 = NofibPrelude.Cons(31, tmp7);
    tmp9 = NofibPrelude.Cons(30, tmp8);
    tmp10 = NofibPrelude.Cons(31, tmp9);
    tmp11 = NofibPrelude.Cons(feb, tmp10);
    return NofibPrelude.Cons(31, tmp11)
  } 
  static jan1st(year2) {
    let last, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = year2 - 1;
    last = tmp;
    tmp1 = NofibPrelude.intDiv(last, 4);
    tmp2 = year2 + tmp1;
    tmp3 = NofibPrelude.intDiv(last, 100);
    tmp4 = tmp2 - tmp3;
    tmp5 = NofibPrelude.intDiv(last, 400);
    tmp6 = tmp4 + tmp5;
    return NofibPrelude.intMod(tmp6, 7)
  } 
  static firstDays(year3) {
    let tmp, tmp1, tmp2, tmp3;
    tmp = calendar.jan1st(year3);
    tmp1 = calendar.monthLengths(year3);
    tmp2 = NofibPrelude.scanl(lambda4, tmp, tmp1);
    tmp3 = NofibPrelude.map(lambda5, tmp2);
    return NofibPrelude.take(12, tmp3)
  } 
  static space(n3) {
    return NofibPrelude.replicate(n3, " ")
  } 
  static ljustify(n4, s) {
    let tmp, tmp1, tmp2;
    tmp = NofibPrelude.listLen(s);
    tmp1 = n4 - tmp;
    tmp2 = calendar.space(tmp1);
    return NofibPrelude.append(s, tmp2)
  } 
  static rjustify(n5, s1) {
    let tmp, tmp1, tmp2;
    tmp = NofibPrelude.listLen(s1);
    tmp1 = n5 - tmp;
    tmp2 = calendar.space(tmp1);
    return NofibPrelude.append(tmp2, s1)
  } 
  static date(ml, d) {
    let scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    tmp = d < 1;
    tmp1 = ml < d;
    scrut = tmp || tmp1;
    if (scrut === true) {
      tmp2 = NofibPrelude.nofibStringToList("   ");
      return NofibPrelude.Cons(tmp2, NofibPrelude.Nil)
    } else {
      tmp3 = NofibPrelude.stringOfInt(d);
      tmp4 = NofibPrelude.nofibStringToList(tmp3);
      tmp5 = calendar.rjustify(3, tmp4);
      return NofibPrelude.Cons(tmp5, NofibPrelude.Nil)
    }
  } 
  static dates(fd, ml1) {
    let tmp, tmp1, tmp2, lambda$this;
    tmp = 1 - fd;
    tmp1 = 42 - fd;
    tmp2 = NofibPrelude.enumFromTo(tmp, tmp1);
    lambda$this = runtime.safeCall(lambda6(ml1));
    return NofibPrelude.map(lambda$this, tmp2)
  } 
  static cjustify(n6, s2) {
    let m, halfm, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = NofibPrelude.listLen(s2);
    tmp1 = n6 - tmp;
    m = tmp1;
    tmp2 = NofibPrelude.intDiv(m, 2);
    halfm = tmp2;
    tmp3 = calendar.space(halfm);
    tmp4 = m - halfm;
    tmp5 = calendar.space(tmp4);
    tmp6 = NofibPrelude.append(s2, tmp5);
    return NofibPrelude.append(tmp3, tmp6)
  } 
  static cal(year4) {
    let side, end, daynames, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
    tmp = calendar.emptyPic([
      8,
      2
    ]);
    side = tmp;
    tmp1 = calendar.emptyPic([
      1,
      25
    ]);
    end = tmp1;
    tmp2 = NofibPrelude.nofibStringToList(" Su Mo Tu We Th Fr Sa");
    tmp3 = NofibPrelude.Cons(tmp2, NofibPrelude.Nil);
    daynames = tmp3;
    tmp4 = banner(year4);
    tmp5 = body$(side, end, daynames, year4);
    tmp6 = NofibPrelude.append(tmp4, tmp5);
    return calendar.unlines(tmp6)
  } 
  static testCalendar_nofib(n7) {
    let tmp, tmp1;
    tmp = 1993 + n7;
    tmp1 = NofibPrelude.enumFromTo(1993, tmp);
    return NofibPrelude.map(lambda8, tmp1)
  }
  static toString() { return "calendar"; }
};
let calendar = calendar1; export default calendar;
