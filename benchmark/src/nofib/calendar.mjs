import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let emptyPic, spread, rjustify, jan1st, unlines, height, cal, block, space, blockT, stack, cjustify, ljustify, width, lframe, monthLengths, testCalendar_nofib, groop, dates, date, leap, firstDays, monthNames, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, lambda;
unlines = function unlines(ls) {
  let tmp25, lambda1;
  lambda1 = (undefined, function (x) {
    let tmp26;
    tmp26 = NofibPrelude.Cons("\n", NofibPrelude.Nil);
    return NofibPrelude.append(x, tmp26)
  });
  tmp25 = NofibPrelude.map(lambda1, ls);
  return NofibPrelude.concat(tmp25)
};
height = function height(p) {
  return NofibPrelude.listLen(p)
};
width = function width(p) {
  let tmp25;
  tmp25 = NofibPrelude.head(p);
  return NofibPrelude.listLen(tmp25)
};
stack = function stack(ls) {
  let lambda1;
  lambda1 = (undefined, function (a, b) {
    return NofibPrelude.append(a, b)
  });
  return NofibPrelude.foldr1(lambda1, ls)
};
spread = function spread(ls) {
  let lambda1;
  lambda1 = (undefined, function (a, b) {
    let lambda2;
    lambda2 = (undefined, function (a1, b1) {
      return NofibPrelude.append(a1, b1)
    });
    return NofibPrelude.zipWith(lambda2, a, b)
  });
  return NofibPrelude.foldr1(lambda1, ls)
};
emptyPic = function emptyPic(hw) {
  let first1, first0, h, w, tmp25;
  if (globalThis.Array.isArray(hw) && hw.length === 2) {
    first0 = hw[0];
    first1 = hw[1];
    h = first0;
    w = first1;
    tmp25 = NofibPrelude.replicate(w, " ");
    return NofibPrelude.replicate(h, tmp25)
  } else {
    throw new globalThis.Error("match error");
  }
};
groop = function groop(n, xs) {
  let tmp25, tmp26, tmp27;
  if (xs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else {
    tmp25 = NofibPrelude.take(n, xs);
    tmp26 = NofibPrelude.drop(n, xs);
    tmp27 = groop(n, tmp26);
    return NofibPrelude.Cons(tmp25, tmp27)
  }
};
block = function block(n, t) {
  let tmp25, tmp26;
  tmp25 = groop(n, t);
  tmp26 = NofibPrelude.map(spread, tmp25);
  return stack(tmp26)
};
blockT = function blockT(n, t) {
  let tmp25, tmp26;
  tmp25 = groop(n, t);
  tmp26 = NofibPrelude.map(stack, tmp25);
  return stack(tmp26)
};
lframe = function lframe(mn, p) {
  let first1, first0, m, n, h, w, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31;
  if (globalThis.Array.isArray(mn) && mn.length === 2) {
    first0 = mn[0];
    first1 = mn[1];
    m = first0;
    n = first1;
    tmp25 = height(p);
    h = tmp25;
    tmp26 = width(p);
    w = tmp26;
    tmp27 = n - w;
    tmp28 = emptyPic([
      h,
      tmp27
    ]);
    tmp29 = NofibPrelude.zipWith(NofibPrelude.append, p, tmp28);
    tmp30 = m - h;
    tmp31 = emptyPic([
      tmp30,
      n
    ]);
    return NofibPrelude.append(tmp29, tmp31)
  } else {
    throw new globalThis.Error("match error");
  }
};
leap = function leap(year) {
  let scrut, tmp25, tmp26, tmp27;
  tmp25 = NofibPrelude.intMod(year, 100);
  scrut = tmp25 == 0;
  if (scrut === true) {
    tmp26 = NofibPrelude.intMod(year, 400);
    return tmp26 == 0
  } else {
    tmp27 = NofibPrelude.intMod(year, 4);
    return tmp27 == 0
  }
};
monthLengths = function monthLengths(year) {
  let feb, scrut, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36;
  scrut = leap(year);
  if (scrut === true) {
    tmp25 = 29;
  } else {
    tmp25 = 28;
  }
  feb = tmp25;
  tmp26 = NofibPrelude.Cons(31, NofibPrelude.Nil);
  tmp27 = NofibPrelude.Cons(30, tmp26);
  tmp28 = NofibPrelude.Cons(31, tmp27);
  tmp29 = NofibPrelude.Cons(30, tmp28);
  tmp30 = NofibPrelude.Cons(31, tmp29);
  tmp31 = NofibPrelude.Cons(31, tmp30);
  tmp32 = NofibPrelude.Cons(30, tmp31);
  tmp33 = NofibPrelude.Cons(31, tmp32);
  tmp34 = NofibPrelude.Cons(30, tmp33);
  tmp35 = NofibPrelude.Cons(31, tmp34);
  tmp36 = NofibPrelude.Cons(feb, tmp35);
  return NofibPrelude.Cons(31, tmp36)
};
jan1st = function jan1st(year) {
  let last, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31;
  tmp25 = year - 1;
  last = tmp25;
  tmp26 = NofibPrelude.intDiv(last, 4);
  tmp27 = year + tmp26;
  tmp28 = NofibPrelude.intDiv(last, 100);
  tmp29 = tmp27 - tmp28;
  tmp30 = NofibPrelude.intDiv(last, 400);
  tmp31 = tmp29 + tmp30;
  return NofibPrelude.intMod(tmp31, 7)
};
firstDays = function firstDays(year) {
  let tmp25, tmp26, tmp27, tmp28, lambda1, lambda2;
  tmp25 = jan1st(year);
  tmp26 = monthLengths(year);
  lambda1 = (undefined, function (a, b) {
    return a + b
  });
  tmp27 = NofibPrelude.scanl(lambda1, tmp25, tmp26);
  lambda2 = (undefined, function (x) {
    return NofibPrelude.intMod(x, 7)
  });
  tmp28 = NofibPrelude.map(lambda2, tmp27);
  return NofibPrelude.take(12, tmp28)
};
space = function space(n) {
  return NofibPrelude.replicate(n, " ")
};
ljustify = function ljustify(n, s) {
  let tmp25, tmp26, tmp27;
  tmp25 = NofibPrelude.listLen(s);
  tmp26 = n - tmp25;
  tmp27 = space(tmp26);
  return NofibPrelude.append(s, tmp27)
};
rjustify = function rjustify(n, s) {
  let tmp25, tmp26, tmp27;
  tmp25 = NofibPrelude.listLen(s);
  tmp26 = n - tmp25;
  tmp27 = space(tmp26);
  return NofibPrelude.append(tmp27, s)
};
date = function date(ml, d) {
  let scrut, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30;
  tmp25 = d < 1;
  tmp26 = ml < d;
  scrut = tmp25 || tmp26;
  if (scrut === true) {
    tmp27 = NofibPrelude.nofibStringToList("   ");
    return NofibPrelude.Cons(tmp27, NofibPrelude.Nil)
  } else {
    tmp28 = NofibPrelude.stringOfInt(d);
    tmp29 = NofibPrelude.nofibStringToList(tmp28);
    tmp30 = rjustify(3, tmp29);
    return NofibPrelude.Cons(tmp30, NofibPrelude.Nil)
  }
};
dates = function dates(fd, ml) {
  let tmp25, tmp26, tmp27, lambda1;
  tmp25 = 1 - fd;
  tmp26 = 42 - fd;
  tmp27 = NofibPrelude.enumFromTo(tmp25, tmp26);
  lambda1 = (undefined, function (d) {
    return date(ml, d)
  });
  return NofibPrelude.map(lambda1, tmp27)
};
cjustify = function cjustify(n, s) {
  let m, halfm, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31;
  tmp25 = NofibPrelude.listLen(s);
  tmp26 = n - tmp25;
  m = tmp26;
  tmp27 = NofibPrelude.intDiv(m, 2);
  halfm = tmp27;
  tmp28 = space(halfm);
  tmp29 = m - halfm;
  tmp30 = space(tmp29);
  tmp31 = NofibPrelude.append(s, tmp30);
  return NofibPrelude.append(tmp28, tmp31)
};
cal = function cal(year) {
  let body, pad, banner, entries, pic, title, months, table, side, end, daynames, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31;
  banner = function banner(yr) {
    let tmp32, tmp33, tmp34, tmp35;
    tmp32 = NofibPrelude.stringOfInt(yr);
    tmp33 = NofibPrelude.nofibStringToList(tmp32);
    tmp34 = cjustify(75, tmp33);
    tmp35 = emptyPic([
      1,
      75
    ]);
    return NofibPrelude.Cons(tmp34, tmp35)
  };
  body = function body(yr) {
    let tmp32, tmp33, lambda1;
    tmp32 = months(yr);
    lambda1 = (undefined, function (x) {
      let tmp34;
      tmp34 = pic(x);
      return pad(tmp34)
    });
    tmp33 = NofibPrelude.map(lambda1, tmp32);
    return block(3, tmp33)
  };
  pic = function pic(mnfdml) {
    let first2, first1, first0, mn, fd, ml, tmp32, tmp33;
    if (globalThis.Array.isArray(mnfdml) && mnfdml.length === 3) {
      first0 = mnfdml[0];
      first1 = mnfdml[1];
      first2 = mnfdml[2];
      mn = first0;
      fd = first1;
      ml = first2;
      tmp32 = title(mn);
      tmp33 = table(fd, ml);
      return NofibPrelude.append(tmp32, tmp33)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  pad = function pad(p) {
    let tmp32, tmp33;
    tmp32 = NofibPrelude.zipWith(NofibPrelude.append, side, p);
    tmp33 = NofibPrelude.zipWith(NofibPrelude.append, tmp32, side);
    return NofibPrelude.append(tmp33, end)
  };
  title = function title(mn) {
    let tmp32;
    tmp32 = cjustify(21, mn);
    return NofibPrelude.Cons(tmp32, NofibPrelude.Nil)
  };
  table = function table(fd, ml) {
    let tmp32;
    tmp32 = entries(fd, ml);
    return NofibPrelude.append(daynames, tmp32)
  };
  entries = function entries(fd, ml) {
    let tmp32;
    tmp32 = dates(fd, ml);
    return block(7, tmp32)
  };
  months = function months(yer) {
    let tmp32, tmp33;
    tmp32 = firstDays(yer);
    tmp33 = monthLengths(yer);
    return NofibPrelude.zip3(monthNames, tmp32, tmp33)
  };
  tmp25 = emptyPic([
    8,
    2
  ]);
  side = tmp25;
  tmp26 = emptyPic([
    1,
    25
  ]);
  end = tmp26;
  tmp27 = NofibPrelude.nofibStringToList(" Su Mo Tu We Th Fr Sa");
  tmp28 = NofibPrelude.Cons(tmp27, NofibPrelude.Nil);
  daynames = tmp28;
  tmp29 = banner(year);
  tmp30 = body(year);
  tmp31 = NofibPrelude.append(tmp29, tmp30);
  return unlines(tmp31)
};
testCalendar_nofib = function testCalendar_nofib(n) {
  let tmp25, tmp26, lambda1;
  tmp25 = 1993 + n;
  tmp26 = NofibPrelude.enumFromTo(1993, tmp25);
  lambda1 = (undefined, function (x) {
    return cal(x)
  });
  return NofibPrelude.map(lambda1, tmp26)
};
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
monthNames = tmp23;
lambda = (undefined, function () {
  let tmp25, tmp26, tmp27;
  tmp25 = testCalendar_nofib(0);
  tmp26 = NofibPrelude.concat(tmp25);
  tmp27 = NofibPrelude.nofibListToString(tmp26);
  return BenchmarkPrelude.print(tmp27)
});
tmp24 = lambda;
BenchmarkPrelude.benchmark(tmp24)