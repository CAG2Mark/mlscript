import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let quotient, if_, sub1, plus, f, implies, times, exp_, gcd_, difference, nlistp, one, remainder, four, and_, reverse_, greaterp, or_, odd_, two, lessp, cons, add1, divides, nilp, listp, consp, lesseqp, equal, append_, greatereqp, member, zerop, not_, iff, length_, even_, boyer1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda12, lambda13, lambda14, lambda15, lambda16, lambda17, lambda18, lambda19, lambda20, lambda21, lambda22, lambda23, lambda24, lambda25, lambda26, lambda27, lambda28, lambda29, lambda30, lambda31, lambda32, lambda33, lambda34, lambda35, lambda36, lambda37, lambda38, lambda39, lambda40, lambda41, lambda$, zerop$, lambda$1, times$, lambda$2, sub1$, lambda$3, reverse_$, lambda$4, remainder$, lambda$5, quotient$, lambda$6, plus$, lambda$7, or_$, lambda$8, odd_$, lambda$9, nlistp$, lambda$10, member$, lambda$11, listp$, lambda$12, nilp$, lambda$13, lessp$, lambda$14, lesseqp$, lambda$15, length_$, lambda$16, iff$, lambda$17, implies$, lambda$18, greaterp$, lambda$19, greatereqp$, lambda$20, gcd_$, lambda$21, exp_$, lambda$22, even_$, lambda$23, equal$, lambda$24, divides$, lambda$25, difference$, lambda$26, consp$, lambda$27, append_$, lambda$28, and_$, lambda$29, not_$, lambda$30, if_$, lambda$31, four$, lambda$32, two$, lambda$33, one$, lambda$34;
lambda$34 = function lambda$(zero) {
  let tmp, tmp1;
  tmp = one$(zero);
  tmp1 = add1(zero);
  return NofibPrelude.Cons([
    tmp,
    tmp1
  ], NofibPrelude.Nil)
};
lambda1 = (undefined, function (zero) {
  return () => {
    return lambda$34(zero)
  }
});
one$ = function one$(zero) {
  let tmp, tmp1;
  tmp = runtime.safeCall(lambda1(zero));
  tmp1 = NofibPrelude.lazy(tmp);
  return boyer1.Fun(boyer1.ONE, NofibPrelude.Nil, tmp1)
};
one = function one(zero) {
  return () => {
    return one$(zero)
  }
};
lambda$33 = function lambda$(zero) {
  let tmp, tmp1, tmp2;
  tmp = two$(zero);
  tmp1 = one$(zero);
  tmp2 = add1(tmp1);
  return NofibPrelude.Cons([
    tmp,
    tmp2
  ], NofibPrelude.Nil)
};
lambda2 = (undefined, function (zero) {
  return () => {
    return lambda$33(zero)
  }
});
two$ = function two$(zero) {
  let tmp, tmp1;
  tmp = runtime.safeCall(lambda2(zero));
  tmp1 = NofibPrelude.lazy(tmp);
  return boyer1.Fun(boyer1.TWO, NofibPrelude.Nil, tmp1)
};
two = function two(zero) {
  return () => {
    return two$(zero)
  }
};
lambda$32 = function lambda$(zero) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = four$(zero);
  tmp1 = two$(zero);
  tmp2 = add1(tmp1);
  tmp3 = add1(tmp2);
  return NofibPrelude.Cons([
    tmp,
    tmp3
  ], NofibPrelude.Nil)
};
lambda3 = (undefined, function (zero) {
  return () => {
    return lambda$32(zero)
  }
});
four$ = function four$(zero) {
  let tmp, tmp1;
  tmp = runtime.safeCall(lambda3(zero));
  tmp1 = NofibPrelude.lazy(tmp);
  return boyer1.Fun(boyer1.FOUR, NofibPrelude.Nil, tmp1)
};
four = function four(zero) {
  return () => {
    return four$(zero)
  }
};
lambda4 = (undefined, function () {
  return NofibPrelude.Nil
});
add1 = function add1(a) {
  let tmp, tmp1;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = NofibPrelude.lazy(lambda4);
  return boyer1.Fun(boyer1.ADD1, tmp, tmp1)
};
lambda$31 = function lambda$(u, w, x, y, z) {
  let tmp, tmp1, tmp2, tmp3, tmp4;
  tmp = if_$(u, w, x, y, z, x, y, z);
  tmp1 = if_$(u, w, x, y, z, tmp, u, w);
  tmp2 = if_$(u, w, x, y, z, y, u, w);
  tmp3 = if_$(u, w, x, y, z, z, u, w);
  tmp4 = if_$(u, w, x, y, z, x, tmp2, tmp3);
  return NofibPrelude.Cons([
    tmp1,
    tmp4
  ], NofibPrelude.Nil)
};
lambda5 = (undefined, function (u, w, x, y, z) {
  return () => {
    return lambda$31(u, w, x, y, z)
  }
});
if_$ = function if_$(u, w, x, y, z, a, b, c) {
  let tmp, tmp1, tmp2, tmp3, tmp4;
  tmp = NofibPrelude.Cons(c, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(b, tmp);
  tmp2 = NofibPrelude.Cons(a, tmp1);
  tmp3 = runtime.safeCall(lambda5(u, w, x, y, z));
  tmp4 = NofibPrelude.lazy(tmp3);
  return boyer1.Fun(boyer1.IF, tmp2, tmp4)
};
if_ = function if_(u, w, x, y, z) {
  return (a, b, c) => {
    return if_$(u, w, x, y, z, a, b, c)
  }
};
lambda$30 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue) {
  let tmp, tmp1;
  tmp = not_$(u, w, x, y, z, boyerFalse, boyerTrue, x);
  tmp1 = if_$(u, w, x, y, z, x, boyerFalse, boyerTrue);
  return NofibPrelude.Cons([
    tmp,
    tmp1
  ], NofibPrelude.Nil)
};
lambda6 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue) {
  return () => {
    return lambda$30(u, w, x, y, z, boyerFalse, boyerTrue)
  }
});
not_$ = function not_$(u, w, x, y, z, boyerFalse, boyerTrue, a) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = runtime.safeCall(lambda6(u, w, x, y, z, boyerFalse, boyerTrue));
  tmp2 = NofibPrelude.lazy(tmp1);
  return boyer1.Fun(boyer1.NOT, tmp, tmp2)
};
not_ = function not_(u, w, x, y, z, boyerFalse, boyerTrue) {
  return (a) => {
    return not_$(u, w, x, y, z, boyerFalse, boyerTrue, a)
  }
};
lambda$29 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue) {
  let tmp, tmp1, tmp2;
  tmp = and_$(u, w, x, y, z, boyerFalse, boyerTrue, x, y);
  tmp1 = if_$(u, w, x, y, z, y, boyerTrue, boyerFalse);
  tmp2 = if_$(u, w, x, y, z, x, tmp1, boyerFalse);
  return NofibPrelude.Cons([
    tmp,
    tmp2
  ], NofibPrelude.Nil)
};
lambda7 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue) {
  return () => {
    return lambda$29(u, w, x, y, z, boyerFalse, boyerTrue)
  }
});
and_$ = function and_$(u, w, x, y, z, boyerFalse, boyerTrue, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda7(u, w, x, y, z, boyerFalse, boyerTrue));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.AND, tmp1, tmp3)
};
and_ = function and_(u, w, x, y, z, boyerFalse, boyerTrue) {
  return (a, b) => {
    return and_$(u, w, x, y, z, boyerFalse, boyerTrue, a, b)
  }
};
lambda$28 = function lambda$(x, y, z) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = append_$(x, y, z, x, y);
  tmp1 = append_$(x, y, z, tmp, z);
  tmp2 = append_$(x, y, z, y, z);
  tmp3 = append_$(x, y, z, x, tmp2);
  return NofibPrelude.Cons([
    tmp1,
    tmp3
  ], NofibPrelude.Nil)
};
lambda8 = (undefined, function (x, y, z) {
  return () => {
    return lambda$28(x, y, z)
  }
});
append_$ = function append_$(x, y, z, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda8(x, y, z));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.APPEND, tmp1, tmp3)
};
append_ = function append_(x, y, z) {
  return (a, b) => {
    return append_$(x, y, z, a, b)
  }
};
lambda9 = (undefined, function () {
  return NofibPrelude.Nil
});
cons = function cons(a, b) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = NofibPrelude.lazy(lambda9);
  return boyer1.Fun(boyer1.CONS, tmp1, tmp2)
};
lambda$27 = function lambda$(x, y, boyerTrue) {
  let tmp, tmp1;
  tmp = cons(x, y);
  tmp1 = consp$(x, y, boyerTrue, tmp);
  return NofibPrelude.Cons([
    tmp1,
    boyerTrue
  ], NofibPrelude.Nil)
};
lambda10 = (undefined, function (x, y, boyerTrue) {
  return () => {
    return lambda$27(x, y, boyerTrue)
  }
});
consp$ = function consp$(x, y, boyerTrue, a) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = runtime.safeCall(lambda10(x, y, boyerTrue));
  tmp2 = NofibPrelude.lazy(tmp1);
  return boyer1.Fun(boyer1.CONSP, tmp, tmp2)
};
consp = function consp(x, y, boyerTrue) {
  return (a) => {
    return consp$(x, y, boyerTrue, a)
  }
};
lambda$26 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26;
  tmp = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, x);
  tmp1 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp2 = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp1, x);
  tmp3 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, x);
  tmp4 = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp3, x);
  tmp5 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp6 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, z);
  tmp7 = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp5, tmp6);
  tmp8 = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp9 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, z);
  tmp10 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, tmp9);
  tmp11 = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp10, x);
  tmp12 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp13 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp14 = add1(tmp13);
  tmp15 = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp14, z);
  tmp16 = add1(y);
  tmp17 = add1(x);
  tmp18 = add1(tmp17);
  tmp19 = two$(zero);
  tmp20 = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp18, tmp19);
  tmp21 = NofibPrelude.Cons([
    tmp20,
    x
  ], NofibPrelude.Nil);
  tmp22 = NofibPrelude.Cons([
    tmp15,
    tmp16
  ], tmp21);
  tmp23 = NofibPrelude.Cons([
    tmp11,
    tmp12
  ], tmp22);
  tmp24 = NofibPrelude.Cons([
    tmp7,
    tmp8
  ], tmp23);
  tmp25 = NofibPrelude.Cons([
    tmp4,
    y
  ], tmp24);
  tmp26 = NofibPrelude.Cons([
    tmp2,
    y
  ], tmp25);
  return NofibPrelude.Cons([
    tmp,
    zero
  ], tmp26)
};
lambda11 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$26(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
difference$ = function difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda11(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.DIFFERENCE, tmp1, tmp3)
};
difference = function difference(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a, b) => {
    return difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b)
  }
};
lambda$25 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2;
  tmp = divides$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp1 = remainder$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, x);
  tmp2 = zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp1);
  return NofibPrelude.Cons([
    tmp,
    tmp2
  ], NofibPrelude.Nil)
};
lambda12 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$25(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
divides$ = function divides$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda12(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.DIVIDES, tmp1, tmp3)
};
divides = function divides(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a, b) => {
    return divides$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b)
  }
};
lambda$24 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74;
  tmp = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp1 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp, zero);
  tmp2 = zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x);
  tmp3 = zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y);
  tmp4 = and_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp2, tmp3);
  tmp5 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp6 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, z);
  tmp7 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp5, tmp6);
  tmp8 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp9 = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp10 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, zero, tmp9);
  tmp11 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, x);
  tmp12 = not_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp11);
  tmp13 = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp14 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp13);
  tmp15 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, zero);
  tmp16 = zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y);
  tmp17 = or_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp15, tmp16);
  tmp18 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp19 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp18, zero);
  tmp20 = zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x);
  tmp21 = zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y);
  tmp22 = or_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp20, tmp21);
  tmp23 = append_$(x, y, z, x, y);
  tmp24 = append_$(x, y, z, x, z);
  tmp25 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp23, tmp24);
  tmp26 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp27 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp28 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, tmp27);
  tmp29 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, zero);
  tmp30 = one$(zero);
  tmp31 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp30);
  tmp32 = or_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp29, tmp31);
  tmp33 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp34 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp33);
  tmp35 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, zero);
  tmp36 = one$(zero);
  tmp37 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, tmp36);
  tmp38 = or_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp35, tmp37);
  tmp39 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp40 = one$(zero);
  tmp41 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp39, tmp40);
  tmp42 = one$(zero);
  tmp43 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp42);
  tmp44 = one$(zero);
  tmp45 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, tmp44);
  tmp46 = and_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp43, tmp45);
  tmp47 = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp48 = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, z, y);
  tmp49 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp47, tmp48);
  tmp50 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp51 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp52 = not_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp51);
  tmp53 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, z, y);
  tmp54 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, x);
  tmp55 = not_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp54);
  tmp56 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, z);
  tmp57 = if_$(u, w, x, y, z, tmp53, tmp55, tmp56);
  tmp58 = if_$(u, w, x, y, z, tmp50, tmp52, tmp57);
  tmp59 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp60 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp59, z);
  tmp61 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp62 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, boyerTrue, z);
  tmp63 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, boyerFalse, z);
  tmp64 = if_$(u, w, x, y, z, tmp61, tmp62, tmp63);
  tmp65 = NofibPrelude.Cons([
    tmp60,
    tmp64
  ], NofibPrelude.Nil);
  tmp66 = NofibPrelude.Cons([
    tmp49,
    tmp58
  ], tmp65);
  tmp67 = NofibPrelude.Cons([
    tmp41,
    tmp46
  ], tmp66);
  tmp68 = NofibPrelude.Cons([
    tmp34,
    tmp38
  ], tmp67);
  tmp69 = NofibPrelude.Cons([
    tmp28,
    tmp32
  ], tmp68);
  tmp70 = NofibPrelude.Cons([
    tmp25,
    tmp26
  ], tmp69);
  tmp71 = NofibPrelude.Cons([
    tmp19,
    tmp22
  ], tmp70);
  tmp72 = NofibPrelude.Cons([
    tmp14,
    tmp17
  ], tmp71);
  tmp73 = NofibPrelude.Cons([
    tmp10,
    tmp12
  ], tmp72);
  tmp74 = NofibPrelude.Cons([
    tmp7,
    tmp8
  ], tmp73);
  return NofibPrelude.Cons([
    tmp1,
    tmp4
  ], tmp74)
};
lambda13 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$24(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
equal$ = function equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda13(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.EQUAL, tmp1, tmp3)
};
equal = function equal(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a, b) => {
    return equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b)
  }
};
lambda$23 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2, tmp3, tmp4;
  tmp = even_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x);
  tmp1 = zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x);
  tmp2 = sub1$(x, x);
  tmp3 = odd_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp2);
  tmp4 = if_$(u, w, x, y, z, tmp1, boyerTrue, tmp3);
  return NofibPrelude.Cons([
    tmp,
    tmp4
  ], NofibPrelude.Nil)
};
lambda14 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$23(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
even_$ = function even_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = runtime.safeCall(lambda14(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp2 = NofibPrelude.lazy(tmp1);
  return boyer1.Fun(boyer1.EVEN, tmp, tmp2)
};
even_ = function even_(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a) => {
    return even_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a)
  }
};
lambda$22 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
  tmp = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp1 = exp_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp);
  tmp2 = exp_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp3 = exp_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, z);
  tmp4 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp2, tmp3);
  tmp5 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp6 = exp_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp5);
  tmp7 = exp_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp8 = exp_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp7, z);
  tmp9 = NofibPrelude.Cons([
    tmp6,
    tmp8
  ], NofibPrelude.Nil);
  return NofibPrelude.Cons([
    tmp1,
    tmp4
  ], tmp9)
};
lambda15 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$22(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
exp_$ = function exp_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda15(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.EXP, tmp1, tmp3)
};
exp_ = function exp_(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a, b) => {
    return exp_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b)
  }
};
lambda16 = (undefined, function () {
  return NofibPrelude.Nil
});
f = function f(a) {
  let tmp, tmp1;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = NofibPrelude.lazy(lambda16);
  return boyer1.Fun(boyer1.F, tmp, tmp1)
};
lambda$21 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  tmp = gcd_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp1 = gcd_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, x);
  tmp2 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, z);
  tmp3 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp4 = gcd_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp2, tmp3);
  tmp5 = gcd_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp6 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, z, tmp5);
  tmp7 = NofibPrelude.Cons([
    tmp4,
    tmp6
  ], NofibPrelude.Nil);
  return NofibPrelude.Cons([
    tmp,
    tmp1
  ], tmp7)
};
lambda17 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$21(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
gcd_$ = function gcd_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda17(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.GCD, tmp1, tmp3)
};
gcd_ = function gcd_(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a, b) => {
    return gcd_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b)
  }
};
lambda$20 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2;
  tmp = greatereqp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp1 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp2 = not_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp1);
  return NofibPrelude.Cons([
    tmp,
    tmp2
  ], NofibPrelude.Nil)
};
lambda18 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$20(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
greatereqp$ = function greatereqp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda18(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.GREATEREQP, tmp1, tmp3)
};
greatereqp = function greatereqp(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a, b) => {
    return greatereqp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b)
  }
};
lambda$19 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1;
  tmp = greaterp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp1 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, x);
  return NofibPrelude.Cons([
    tmp,
    tmp1
  ], NofibPrelude.Nil)
};
lambda19 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$19(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
greaterp$ = function greaterp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda19(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.GREATERP, tmp1, tmp3)
};
greaterp = function greaterp(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a, b) => {
    return greaterp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b)
  }
};
lambda$18 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue) {
  let tmp, tmp1, tmp2;
  tmp = implies$(u, w, x, y, z, boyerFalse, boyerTrue, x, y);
  tmp1 = if_$(u, w, x, y, z, y, boyerTrue, boyerFalse);
  tmp2 = if_$(u, w, x, y, z, x, tmp1, boyerTrue);
  return NofibPrelude.Cons([
    tmp,
    tmp2
  ], NofibPrelude.Nil)
};
lambda20 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue) {
  return () => {
    return lambda$18(u, w, x, y, z, boyerFalse, boyerTrue)
  }
});
implies$ = function implies$(u, w, x, y, z, boyerFalse, boyerTrue, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda20(u, w, x, y, z, boyerFalse, boyerTrue));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.IMPLIES, tmp1, tmp3)
};
implies = function implies(u, w, x, y, z, boyerFalse, boyerTrue) {
  return (a, b) => {
    return implies$(u, w, x, y, z, boyerFalse, boyerTrue, a, b)
  }
};
lambda$17 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = iff$(u, w, x, y, z, boyerFalse, boyerTrue, x, y);
  tmp1 = implies$(u, w, x, y, z, boyerFalse, boyerTrue, x, y);
  tmp2 = implies$(u, w, x, y, z, boyerFalse, boyerTrue, y, x);
  tmp3 = and_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp1, tmp2);
  return NofibPrelude.Cons([
    tmp,
    tmp3
  ], NofibPrelude.Nil)
};
lambda21 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue) {
  return () => {
    return lambda$17(u, w, x, y, z, boyerFalse, boyerTrue)
  }
});
iff$ = function iff$(u, w, x, y, z, boyerFalse, boyerTrue, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda21(u, w, x, y, z, boyerFalse, boyerTrue));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.IFF, tmp1, tmp3)
};
iff = function iff(u, w, x, y, z, boyerFalse, boyerTrue) {
  return (a, b) => {
    return iff$(u, w, x, y, z, boyerFalse, boyerTrue, a, b)
  }
};
lambda$16 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
  tmp = reverse_$(x, y, z, x);
  tmp1 = length_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp);
  tmp2 = length_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x);
  tmp3 = cons(u, w);
  tmp4 = cons(z, tmp3);
  tmp5 = cons(y, tmp4);
  tmp6 = cons(x, tmp5);
  tmp7 = length_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp6);
  tmp8 = four$(zero);
  tmp9 = length_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, w);
  tmp10 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp8, tmp9);
  tmp11 = NofibPrelude.Cons([
    tmp7,
    tmp10
  ], NofibPrelude.Nil);
  return NofibPrelude.Cons([
    tmp1,
    tmp2
  ], tmp11)
};
lambda22 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$16(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
length_$ = function length_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = runtime.safeCall(lambda22(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp2 = NofibPrelude.lazy(tmp1);
  return boyer1.Fun(boyer1.LENGTH, tmp, tmp2)
};
length_ = function length_(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a) => {
    return length_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a)
  }
};
lambda$15 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2;
  tmp = lesseqp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp1 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, x);
  tmp2 = not_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp1);
  return NofibPrelude.Cons([
    tmp,
    tmp2
  ], NofibPrelude.Nil)
};
lambda23 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$15(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
lesseqp$ = function lesseqp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda23(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.LESSEQP, tmp1, tmp3)
};
lesseqp = function lesseqp(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a, b) => {
    return lesseqp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b)
  }
};
lambda$14 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29;
  tmp = remainder$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp1 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp, y);
  tmp2 = zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y);
  tmp3 = not_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp2);
  tmp4 = quotient$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp5 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp4, x);
  tmp6 = zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x);
  tmp7 = not_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp6);
  tmp8 = one$(zero);
  tmp9 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp8, y);
  tmp10 = and_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp7, tmp9);
  tmp11 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp12 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, z);
  tmp13 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp11, tmp12);
  tmp14 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp15 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, z);
  tmp16 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp17 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp15, tmp16);
  tmp18 = zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, z);
  tmp19 = not_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp18);
  tmp20 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp21 = and_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp19, tmp20);
  tmp22 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp23 = lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, tmp22);
  tmp24 = zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x);
  tmp25 = not_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp24);
  tmp26 = NofibPrelude.Cons([
    tmp23,
    tmp25
  ], NofibPrelude.Nil);
  tmp27 = NofibPrelude.Cons([
    tmp17,
    tmp21
  ], tmp26);
  tmp28 = NofibPrelude.Cons([
    tmp13,
    tmp14
  ], tmp27);
  tmp29 = NofibPrelude.Cons([
    tmp5,
    tmp10
  ], tmp28);
  return NofibPrelude.Cons([
    tmp1,
    tmp3
  ], tmp29)
};
lambda24 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$14(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
lessp$ = function lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda24(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.LESSP, tmp1, tmp3)
};
lessp = function lessp(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a, b) => {
    return lessp$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b)
  }
};
lambda$13 = function lambda$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero) {
  let tmp, tmp1;
  tmp = nilp$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero, x);
  tmp1 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, nil);
  return NofibPrelude.Cons([
    tmp,
    tmp1
  ], NofibPrelude.Nil)
};
lambda25 = (undefined, function (u, w, x, y, z, boyerFalse, nil, boyerTrue, zero) {
  return () => {
    return lambda$13(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero)
  }
});
nilp$ = function nilp$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero, a) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = runtime.safeCall(lambda25(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero));
  tmp2 = NofibPrelude.lazy(tmp1);
  return boyer1.Fun(boyer1.NILP, tmp, tmp2)
};
nilp = function nilp(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero) {
  return (a) => {
    return nilp$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero, a)
  }
};
lambda$12 = function lambda$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = listp$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero, x);
  tmp1 = nilp$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero, x);
  tmp2 = consp$(x, y, boyerTrue, x);
  tmp3 = or_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp1, tmp2);
  return NofibPrelude.Cons([
    tmp,
    tmp3
  ], NofibPrelude.Nil)
};
lambda26 = (undefined, function (u, w, x, y, z, boyerFalse, nil, boyerTrue, zero) {
  return () => {
    return lambda$12(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero)
  }
});
listp$ = function listp$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero, a) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = runtime.safeCall(lambda26(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero));
  tmp2 = NofibPrelude.lazy(tmp1);
  return boyer1.Fun(boyer1.LISTP, tmp, tmp2)
};
listp = function listp(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero) {
  return (a) => {
    return listp$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero, a)
  }
};
lambda$11 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
  tmp = append_$(x, y, z, y, z);
  tmp1 = member$(u, w, x, y, z, boyerFalse, boyerTrue, x, tmp);
  tmp2 = member$(u, w, x, y, z, boyerFalse, boyerTrue, x, y);
  tmp3 = member$(u, w, x, y, z, boyerFalse, boyerTrue, x, z);
  tmp4 = or_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp2, tmp3);
  tmp5 = reverse_$(x, y, z, y);
  tmp6 = member$(u, w, x, y, z, boyerFalse, boyerTrue, x, tmp5);
  tmp7 = member$(u, w, x, y, z, boyerFalse, boyerTrue, x, y);
  tmp8 = NofibPrelude.Cons([
    tmp6,
    tmp7
  ], NofibPrelude.Nil);
  return NofibPrelude.Cons([
    tmp1,
    tmp4
  ], tmp8)
};
lambda27 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue) {
  return () => {
    return lambda$11(u, w, x, y, z, boyerFalse, boyerTrue)
  }
});
member$ = function member$(u, w, x, y, z, boyerFalse, boyerTrue, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda27(u, w, x, y, z, boyerFalse, boyerTrue));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.MEMBER, tmp1, tmp3)
};
member = function member(u, w, x, y, z, boyerFalse, boyerTrue) {
  return (a, b) => {
    return member$(u, w, x, y, z, boyerFalse, boyerTrue, a, b)
  }
};
lambda$10 = function lambda$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero) {
  let tmp, tmp1, tmp2;
  tmp = nlistp$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero, x);
  tmp1 = listp$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero, x);
  tmp2 = not_$(u, w, x, y, z, boyerFalse, boyerTrue, tmp1);
  return NofibPrelude.Cons([
    tmp,
    tmp2
  ], NofibPrelude.Nil)
};
lambda28 = (undefined, function (u, w, x, y, z, boyerFalse, nil, boyerTrue, zero) {
  return () => {
    return lambda$10(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero)
  }
});
nlistp$ = function nlistp$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero, a) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = runtime.safeCall(lambda28(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero));
  tmp2 = NofibPrelude.lazy(tmp1);
  return boyer1.Fun(boyer1.NLISTP, tmp, tmp2)
};
nlistp = function nlistp(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero) {
  return (a) => {
    return nlistp$(u, w, x, y, z, boyerFalse, nil, boyerTrue, zero, a)
  }
};
lambda$9 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2;
  tmp = odd_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x);
  tmp1 = sub1$(x, x);
  tmp2 = even_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp1);
  return NofibPrelude.Cons([
    tmp,
    tmp2
  ], NofibPrelude.Nil)
};
lambda29 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$9(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
odd_$ = function odd_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = runtime.safeCall(lambda29(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp2 = NofibPrelude.lazy(tmp1);
  return boyer1.Fun(boyer1.ODD, tmp, tmp2)
};
odd_ = function odd_(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a) => {
    return odd_$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a)
  }
};
lambda$8 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue) {
  let tmp, tmp1, tmp2;
  tmp = or_$(u, w, x, y, z, boyerFalse, boyerTrue, x, y);
  tmp1 = if_$(u, w, x, y, z, y, boyerTrue, boyerFalse);
  tmp2 = if_$(u, w, x, y, z, x, boyerTrue, tmp1);
  return NofibPrelude.Cons([
    tmp,
    tmp2
  ], NofibPrelude.Nil)
};
lambda30 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue) {
  return () => {
    return lambda$8(u, w, x, y, z, boyerFalse, boyerTrue)
  }
});
or_$ = function or_$(u, w, x, y, z, boyerFalse, boyerTrue, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda30(u, w, x, y, z, boyerFalse, boyerTrue));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.OR, tmp1, tmp3)
};
or_ = function or_(u, w, x, y, z, boyerFalse, boyerTrue) {
  return (a, b) => {
    return or_$(u, w, x, y, z, boyerFalse, boyerTrue, a, b)
  }
};
lambda$7 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13;
  tmp = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp1 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp, z);
  tmp2 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp3 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp2);
  tmp4 = remainder$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp5 = quotient$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp6 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, tmp5);
  tmp7 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp4, tmp6);
  tmp8 = add1(y);
  tmp9 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp8);
  tmp10 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp11 = add1(tmp10);
  tmp12 = NofibPrelude.Cons([
    tmp9,
    tmp11
  ], NofibPrelude.Nil);
  tmp13 = NofibPrelude.Cons([
    tmp7,
    x
  ], tmp12);
  return NofibPrelude.Cons([
    tmp1,
    tmp3
  ], tmp13)
};
lambda31 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$7(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
plus$ = function plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda31(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.PLUS, tmp1, tmp3)
};
plus = function plus(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a, b) => {
    return plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b)
  }
};
lambda$6 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11;
  tmp = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp1 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp);
  tmp2 = two$(zero);
  tmp3 = quotient$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp1, tmp2);
  tmp4 = two$(zero);
  tmp5 = quotient$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, tmp4);
  tmp6 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp5);
  tmp7 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, x);
  tmp8 = quotient$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp7, y);
  tmp9 = zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y);
  tmp10 = if_$(u, w, x, y, z, tmp9, zero, x);
  tmp11 = NofibPrelude.Cons([
    tmp8,
    tmp10
  ], NofibPrelude.Nil);
  return NofibPrelude.Cons([
    tmp3,
    tmp6
  ], tmp11)
};
lambda32 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$6(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
quotient$ = function quotient$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda32(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.QUOTIENT, tmp1, tmp3)
};
quotient = function quotient(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a, b) => {
    return quotient$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b)
  }
};
lambda$5 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
  tmp = one$(zero);
  tmp1 = remainder$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp);
  tmp2 = remainder$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, x);
  tmp3 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp4 = remainder$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp3, x);
  tmp5 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp6 = remainder$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp5, y);
  tmp7 = NofibPrelude.Cons([
    tmp6,
    zero
  ], NofibPrelude.Nil);
  tmp8 = NofibPrelude.Cons([
    tmp4,
    zero
  ], tmp7);
  tmp9 = NofibPrelude.Cons([
    tmp2,
    zero
  ], tmp8);
  return NofibPrelude.Cons([
    tmp1,
    zero
  ], tmp9)
};
lambda33 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$5(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
remainder$ = function remainder$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda33(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.REMAINDER, tmp1, tmp3)
};
remainder = function remainder(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a, b) => {
    return remainder$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b)
  }
};
lambda$4 = function lambda$(x, y, z) {
  let tmp, tmp1, tmp2, tmp3, tmp4;
  tmp = append_$(x, y, z, x, y);
  tmp1 = reverse_$(x, y, z, tmp);
  tmp2 = reverse_$(x, y, z, y);
  tmp3 = reverse_$(x, y, z, x);
  tmp4 = append_$(x, y, z, tmp2, tmp3);
  return NofibPrelude.Cons([
    tmp1,
    tmp4
  ], NofibPrelude.Nil)
};
lambda34 = (undefined, function (x, y, z) {
  return () => {
    return lambda$4(x, y, z)
  }
});
reverse_$ = function reverse_$(x, y, z, a) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = runtime.safeCall(lambda34(x, y, z));
  tmp2 = NofibPrelude.lazy(tmp1);
  return boyer1.Fun(boyer1.REVERSE, tmp, tmp2)
};
reverse_ = function reverse_(x, y, z) {
  return (a) => {
    return reverse_$(x, y, z, a)
  }
};
lambda$3 = function lambda$(x) {
  let tmp, tmp1;
  tmp = add1(x);
  tmp1 = sub1$(x, tmp);
  return NofibPrelude.Cons([
    tmp1,
    x
  ], NofibPrelude.Nil)
};
lambda35 = (undefined, function (x) {
  return () => {
    return lambda$3(x)
  }
});
sub1$ = function sub1$(x, a) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = runtime.safeCall(lambda35(x));
  tmp2 = NofibPrelude.lazy(tmp1);
  return boyer1.Fun(boyer1.SUB1, tmp, tmp2)
};
sub1 = function sub1(x) {
  return (a) => {
    return sub1$(x, a)
  }
};
lambda$2 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20;
  tmp = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp1 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp);
  tmp2 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp3 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, z);
  tmp4 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp2, tmp3);
  tmp5 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp6 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp5, z);
  tmp7 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp8 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp7);
  tmp9 = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, z);
  tmp10 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp9);
  tmp11 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, y, x);
  tmp12 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, z, x);
  tmp13 = difference$(u, w, x, y, z, boyerFalse, boyerTrue, zero, tmp11, tmp12);
  tmp14 = add1(y);
  tmp15 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp14);
  tmp16 = times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, y);
  tmp17 = plus$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, tmp16);
  tmp18 = NofibPrelude.Cons([
    tmp15,
    tmp17
  ], NofibPrelude.Nil);
  tmp19 = NofibPrelude.Cons([
    tmp10,
    tmp13
  ], tmp18);
  tmp20 = NofibPrelude.Cons([
    tmp6,
    tmp8
  ], tmp19);
  return NofibPrelude.Cons([
    tmp1,
    tmp4
  ], tmp20)
};
lambda36 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$2(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
times$ = function times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.Cons(b, NofibPrelude.Nil);
  tmp1 = NofibPrelude.Cons(a, tmp);
  tmp2 = runtime.safeCall(lambda36(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp3 = NofibPrelude.lazy(tmp2);
  return boyer1.Fun(boyer1.TIMES, tmp1, tmp3)
};
times = function times(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a, b) => {
    return times$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a, b)
  }
};
lambda$1 = function lambda$(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  let tmp, tmp1;
  tmp = zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x);
  tmp1 = equal$(u, w, x, y, z, boyerFalse, boyerTrue, zero, x, zero);
  return NofibPrelude.Cons([
    tmp,
    tmp1
  ], NofibPrelude.Nil)
};
lambda37 = (undefined, function (u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return () => {
    return lambda$1(u, w, x, y, z, boyerFalse, boyerTrue, zero)
  }
});
zerop$ = function zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.Cons(a, NofibPrelude.Nil);
  tmp1 = runtime.safeCall(lambda37(u, w, x, y, z, boyerFalse, boyerTrue, zero));
  tmp2 = NofibPrelude.lazy(tmp1);
  return boyer1.Fun(boyer1.ZEROP, tmp, tmp2)
};
zerop = function zerop(u, w, x, y, z, boyerFalse, boyerTrue, zero) {
  return (a) => {
    return zerop$(u, w, x, y, z, boyerFalse, boyerTrue, zero, a)
  }
};
lambda38 = (undefined, function () {
  return NofibPrelude.Nil
});
lambda39 = (undefined, function () {
  return NofibPrelude.Nil
});
lambda40 = (undefined, function () {
  return NofibPrelude.Nil
});
lambda41 = (undefined, function () {
  return NofibPrelude.Nil
});
lambda$ = function lambda$(subst, x) {
  return boyer1.apply_subst(subst, x)
};
lambda = (undefined, function (subst) {
  return (x) => {
    return lambda$(subst, x)
  }
});
boyer1 = class boyer {
  static {
    boyer1 = boyer;
    let lambda42;
    this.Id = class Id {
      constructor() {}
      toString() { return "Id"; }
    };
    const A$class = class A extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "A"; }
    };
    this.A = new A$class;
    this.A.class = A$class;
    const B$class = class B extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "B"; }
    };
    this.B = new B$class;
    this.B.class = B$class;
    const C$class = class C extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "C"; }
    };
    this.C = new C$class;
    this.C.class = C$class;
    const D$class = class D extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "D"; }
    };
    this.D = new D$class;
    this.D.class = D$class;
    const X$class = class X extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "X"; }
    };
    this.X = new X$class;
    this.X.class = X$class;
    const Y$class = class Y extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "Y"; }
    };
    this.Y = new Y$class;
    this.Y.class = Y$class;
    const Z$class = class Z extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "Z"; }
    };
    this.Z = new Z$class;
    this.Z.class = Z$class;
    const U$class = class U extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "U"; }
    };
    this.U = new U$class;
    this.U.class = U$class;
    const W$class = class W extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "W"; }
    };
    this.W = new W$class;
    this.W.class = W$class;
    const ADD1$class = class ADD1 extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "ADD1"; }
    };
    this.ADD1 = new ADD1$class;
    this.ADD1.class = ADD1$class;
    const AND$class = class AND extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "AND"; }
    };
    this.AND = new AND$class;
    this.AND.class = AND$class;
    const APPEND$class = class APPEND extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "APPEND"; }
    };
    this.APPEND = new APPEND$class;
    this.APPEND.class = APPEND$class;
    const CONS$class = class CONS extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "CONS"; }
    };
    this.CONS = new CONS$class;
    this.CONS.class = CONS$class;
    const CONSP$class = class CONSP extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "CONSP"; }
    };
    this.CONSP = new CONSP$class;
    this.CONSP.class = CONSP$class;
    const DIFFERENCE$class = class DIFFERENCE extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "DIFFERENCE"; }
    };
    this.DIFFERENCE = new DIFFERENCE$class;
    this.DIFFERENCE.class = DIFFERENCE$class;
    const DIVIDES$class = class DIVIDES extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "DIVIDES"; }
    };
    this.DIVIDES = new DIVIDES$class;
    this.DIVIDES.class = DIVIDES$class;
    const EQUAL$class = class EQUAL extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "EQUAL"; }
    };
    this.EQUAL = new EQUAL$class;
    this.EQUAL.class = EQUAL$class;
    const EVEN$class = class EVEN extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "EVEN"; }
    };
    this.EVEN = new EVEN$class;
    this.EVEN.class = EVEN$class;
    const EXP$class = class EXP extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "EXP"; }
    };
    this.EXP = new EXP$class;
    this.EXP.class = EXP$class;
    const F$class = class F extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "F"; }
    };
    this.F = new F$class;
    this.F.class = F$class;
    const FALSE$class = class FALSE extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "FALSE"; }
    };
    this.FALSE = new FALSE$class;
    this.FALSE.class = FALSE$class;
    const FOUR$class = class FOUR extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "FOUR"; }
    };
    this.FOUR = new FOUR$class;
    this.FOUR.class = FOUR$class;
    const GCD$class = class GCD extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "GCD"; }
    };
    this.GCD = new GCD$class;
    this.GCD.class = GCD$class;
    const GREATEREQP$class = class GREATEREQP extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "GREATEREQP"; }
    };
    this.GREATEREQP = new GREATEREQP$class;
    this.GREATEREQP.class = GREATEREQP$class;
    const GREATERP$class = class GREATERP extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "GREATERP"; }
    };
    this.GREATERP = new GREATERP$class;
    this.GREATERP.class = GREATERP$class;
    const IF$class = class IF extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "IF"; }
    };
    this.IF = new IF$class;
    this.IF.class = IF$class;
    const IFF$class = class IFF extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "IFF"; }
    };
    this.IFF = new IFF$class;
    this.IFF.class = IFF$class;
    const IMPLIES$class = class IMPLIES extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "IMPLIES"; }
    };
    this.IMPLIES = new IMPLIES$class;
    this.IMPLIES.class = IMPLIES$class;
    const LENGTH$class = class LENGTH extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "LENGTH"; }
    };
    this.LENGTH = new LENGTH$class;
    this.LENGTH.class = LENGTH$class;
    const LESSEQP$class = class LESSEQP extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "LESSEQP"; }
    };
    this.LESSEQP = new LESSEQP$class;
    this.LESSEQP.class = LESSEQP$class;
    const LESSP$class = class LESSP extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "LESSP"; }
    };
    this.LESSP = new LESSP$class;
    this.LESSP.class = LESSP$class;
    const LISTP$class = class LISTP extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "LISTP"; }
    };
    this.LISTP = new LISTP$class;
    this.LISTP.class = LISTP$class;
    const MEMBER$class = class MEMBER extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "MEMBER"; }
    };
    this.MEMBER = new MEMBER$class;
    this.MEMBER.class = MEMBER$class;
    const NIL$class = class NIL extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "NIL"; }
    };
    this.NIL = new NIL$class;
    this.NIL.class = NIL$class;
    const NILP$class = class NILP extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "NILP"; }
    };
    this.NILP = new NILP$class;
    this.NILP.class = NILP$class;
    const NLISTP$class = class NLISTP extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "NLISTP"; }
    };
    this.NLISTP = new NLISTP$class;
    this.NLISTP.class = NLISTP$class;
    const NOT$class = class NOT extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "NOT"; }
    };
    this.NOT = new NOT$class;
    this.NOT.class = NOT$class;
    const ODD$class = class ODD extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "ODD"; }
    };
    this.ODD = new ODD$class;
    this.ODD.class = ODD$class;
    const ONE$class = class ONE extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "ONE"; }
    };
    this.ONE = new ONE$class;
    this.ONE.class = ONE$class;
    const OR$class = class OR extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "OR"; }
    };
    this.OR = new OR$class;
    this.OR.class = OR$class;
    const PLUS$class = class PLUS extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "PLUS"; }
    };
    this.PLUS = new PLUS$class;
    this.PLUS.class = PLUS$class;
    const QUOTIENT$class = class QUOTIENT extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "QUOTIENT"; }
    };
    this.QUOTIENT = new QUOTIENT$class;
    this.QUOTIENT.class = QUOTIENT$class;
    const REMAINDER$class = class REMAINDER extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "REMAINDER"; }
    };
    this.REMAINDER = new REMAINDER$class;
    this.REMAINDER.class = REMAINDER$class;
    const REVERSE$class = class REVERSE extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "REVERSE"; }
    };
    this.REVERSE = new REVERSE$class;
    this.REVERSE.class = REVERSE$class;
    const SUB1$class = class SUB1 extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "SUB1"; }
    };
    this.SUB1 = new SUB1$class;
    this.SUB1.class = SUB1$class;
    const TIMES$class = class TIMES extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "TIMES"; }
    };
    this.TIMES = new TIMES$class;
    this.TIMES.class = TIMES$class;
    const TRUE$class = class TRUE extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "TRUE"; }
    };
    this.TRUE = new TRUE$class;
    this.TRUE.class = TRUE$class;
    const TWO$class = class TWO extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "TWO"; }
    };
    this.TWO = new TWO$class;
    this.TWO.class = TWO$class;
    const ZERO$class = class ZERO extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "ZERO"; }
    };
    this.ZERO = new ZERO$class;
    this.ZERO.class = ZERO$class;
    const ZEROP$class = class ZEROP extends boyer.Id {
      constructor() {
        super();
      }
      toString() { return "ZEROP"; }
    };
    this.ZEROP = new ZEROP$class;
    this.ZEROP.class = ZEROP$class;
    this.Term = class Term {
      constructor() {}
      toString() { return "Term"; }
    };
    this.Var = function Var(i1) {
      return new Var.class(i1);
    };
    this.Var.class = class Var extends boyer.Term {
      constructor(i) {
        super();
        this.i = i;
      }
      toString() { return "Var(" + globalThis.Predef.render(this.i) + ")"; }
    };
    this.Fun = function Fun(i1, t1, l1) {
      return new Fun.class(i1, t1, l1);
    };
    this.Fun.class = class Fun extends boyer.Term {
      constructor(i, t, l) {
        super();
        this.i = i;
        this.t = t;
        this.l = l;
      }
      toString() { return "Fun(" + globalThis.Predef.render(this.i) + ", " + globalThis.Predef.render(this.t) + ", " + globalThis.Predef.render(this.l) + ")"; }
    };
    const ERROR$class = class ERROR extends boyer.Term {
      constructor() {
        super();
      }
      toString() { return "ERROR"; }
    };
    this.ERROR = new ERROR$class;
    this.ERROR.class = ERROR$class;
    lambda42 = (undefined, function () {
      return boyer.testBoyer_nofib(5)
    });
    BenchmarkPrelude.benchmark(lambda42)
  }
  static termLsEq(h1t1, h2t2) {
    let param0, param1, h1, t1, param01, param11, h2, t2, scrut;
    if (h1t1 instanceof NofibPrelude.Cons.class) {
      param0 = h1t1.head;
      param1 = h1t1.tail;
      h1 = param0;
      t1 = param1;
      if (h2t2 instanceof NofibPrelude.Cons.class) {
        param01 = h2t2.head;
        param11 = h2t2.tail;
        h2 = param01;
        t2 = param11;
        scrut = boyer.termEq(h1, h2);
        if (scrut === true) {
          return boyer.termLsEq(t1, t2)
        } else {
          return false
        }
      } else {
        return true
      }
    } else {
      return true
    }
  } 
  static termEq(t1, t2) {
    let param0, param1, param2, f1, ts1, param01, param11, param21, f2, ts2, scrut, scrut1, param02, i1, param03, i2;
    if (t1 instanceof boyer.Var.class) {
      param02 = t1.i;
      i1 = param02;
      if (t2 instanceof boyer.Var.class) {
        param03 = t2.i;
        i2 = param03;
        return i1 === i2
      } else {
        return false
      }
    } else if (t1 instanceof boyer.Fun.class) {
      param0 = t1.i;
      param1 = t1.t;
      param2 = t1.l;
      f1 = param0;
      ts1 = param1;
      if (t2 instanceof boyer.Fun.class) {
        param01 = t2.i;
        param11 = t2.t;
        param21 = t2.l;
        f2 = param01;
        ts2 = param11;
        scrut = f1 === f2;
        if (scrut === true) {
          scrut1 = boyer.termLsEq(ts1, ts2);
          if (scrut1 === true) {
            return true
          } else {
            return false
          }
        } else {
          return false
        }
      } else {
        return false
      }
    } else {
      return false
    }
  } 
  static termInList(term, ht) {
    let param0, param1, h, t, scrut;
    if (ht instanceof NofibPrelude.Cons.class) {
      param0 = ht.head;
      param1 = ht.tail;
      h = param0;
      t = param1;
      scrut = boyer.termEq(term, h);
      if (scrut === true) {
        return true
      } else {
        return boyer.termInList(term, t)
      }
    } else if (ht instanceof NofibPrelude.Nil.class) {
      return false
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static find(vid, ls) {
    let param0, param1, first1, first0, vid2, val2, bs, scrut;
    if (ls instanceof NofibPrelude.Nil.class) {
      return [
        false,
        boyer.ERROR
      ]
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        vid2 = first0;
        val2 = first1;
        bs = param1;
        scrut = vid === vid2;
        if (scrut === true) {
          return [
            true,
            val2
          ]
        } else {
          return boyer.find(vid, bs)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static one_way_unify1(term1, term2, subst) {
    let param0, param1, param2, f1, as1, param01, param11, param21, f2, as2, scrut, param02, vid2, scrut1, first1, first0, found, v2, tmp, tmp1;
    if (term2 instanceof boyer.Var.class) {
      param02 = term2.i;
      vid2 = param02;
      scrut1 = boyer.find(vid2, subst);
      if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
        first0 = scrut1[0];
        first1 = scrut1[1];
        found = first0;
        v2 = first1;
        if (found === true) {
          tmp = boyer.termEq(term1, v2);
          return [
            tmp,
            subst
          ]
        } else {
          tmp1 = NofibPrelude.Cons([
            vid2,
            term1
          ], subst);
          return [
            true,
            tmp1
          ]
        }
      } else {
        if (term1 instanceof boyer.Fun.class) {
          param0 = term1.i;
          param1 = term1.t;
          param2 = term1.l;
          f1 = param0;
          as1 = param1;
          return [
            false,
            NofibPrelude.Nil
          ]
        } else {
          return [
            false,
            NofibPrelude.Nil
          ]
        }
      }
    } else {
      if (term1 instanceof boyer.Fun.class) {
        param0 = term1.i;
        param1 = term1.t;
        param2 = term1.l;
        f1 = param0;
        as1 = param1;
        if (term2 instanceof boyer.Fun.class) {
          param01 = term2.i;
          param11 = term2.t;
          param21 = term2.l;
          f2 = param01;
          as2 = param11;
          scrut = f1 === f2;
          if (scrut === true) {
            return boyer.one_way_unify1_lst(as1, as2, subst)
          } else {
            return [
              false,
              NofibPrelude.Nil
            ]
          }
        } else {
          return [
            false,
            NofibPrelude.Nil
          ]
        }
      } else {
        return [
          false,
          NofibPrelude.Nil
        ]
      }
    }
  } 
  static one_way_unify1_lst(tts1, tts2, subst1) {
    let param0, param1, t11, ts1, param01, param11, t21, ts2, scrut, first1, first0, hd_ok, subst_, scrut1, first11, first01, tl_ok, subst__, tmp;
    if (tts1 instanceof NofibPrelude.Nil.class) {
      if (tts2 instanceof NofibPrelude.Nil.class) {
        return [
          true,
          subst1
        ]
      } else {
        return [
          false,
          NofibPrelude.Nil
        ]
      }
    } else if (tts1 instanceof NofibPrelude.Cons.class) {
      param0 = tts1.head;
      param1 = tts1.tail;
      t11 = param0;
      ts1 = param1;
      if (tts2 instanceof NofibPrelude.Cons.class) {
        param01 = tts2.head;
        param11 = tts2.tail;
        t21 = param01;
        ts2 = param11;
        scrut = boyer.one_way_unify1(t11, t21, subst1);
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first0 = scrut[0];
          first1 = scrut[1];
          hd_ok = first0;
          subst_ = first1;
          scrut1 = boyer.one_way_unify1_lst(ts1, ts2, subst_);
          if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
            first01 = scrut1[0];
            first11 = scrut1[1];
            tl_ok = first01;
            subst__ = first11;
            if (hd_ok === true) {
              if (tl_ok === true) {
                tmp = true;
              } else {
                tmp = false;
              }
            } else {
              tmp = false;
            }
            return [
              tmp,
              subst__
            ]
          } else {
            return [
              false,
              NofibPrelude.Nil
            ]
          }
        } else {
          return [
            false,
            NofibPrelude.Nil
          ]
        }
      } else {
        return [
          false,
          NofibPrelude.Nil
        ]
      }
    } else {
      return [
        false,
        NofibPrelude.Nil
      ]
    }
  } 
  static one_way_unify(term11, term21) {
    return boyer.one_way_unify1(term11, term21, NofibPrelude.Nil)
  } 
  static apply_subst(subst2, t) {
    let param0, param1, param2, f1, args, ls1, param01, vid1, scrut, first1, first0, found, value, tmp, lambda$this;
    if (t instanceof boyer.Var.class) {
      param01 = t.i;
      vid1 = param01;
      scrut = boyer.find(vid1, subst2);
      if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
        first0 = scrut[0];
        first1 = scrut[1];
        found = first0;
        value = first1;
        if (found === true) {
          return value
        } else {
          return boyer.Var(vid1)
        }
      } else {
        throw new globalThis.Error("match error");
      }
    } else if (t instanceof boyer.Fun.class) {
      param0 = t.i;
      param1 = t.t;
      param2 = t.l;
      f1 = param0;
      args = param1;
      ls1 = param2;
      lambda$this = runtime.safeCall(lambda(subst2));
      tmp = NofibPrelude.map(lambda$this, args);
      return boyer.Fun(f1, tmp, ls1)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static rewrite_with_lemmas_helper(term3, lss) {
    let param0, param1, first1, first0, lhs, rhs, ls1, scrut, first11, first01, unified, subst3, tmp;
    if (lss instanceof NofibPrelude.Nil.class) {
      return term3
    } else if (lss instanceof NofibPrelude.Cons.class) {
      param0 = lss.head;
      param1 = lss.tail;
      if (globalThis.Array.isArray(param0) && param0.length === 2) {
        first0 = param0[0];
        first1 = param0[1];
        lhs = first0;
        rhs = first1;
        ls1 = param1;
        scrut = boyer.one_way_unify(term3, lhs);
        if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
          first01 = scrut[0];
          first11 = scrut[1];
          unified = first01;
          subst3 = first11;
          if (unified === true) {
            tmp = boyer.apply_subst(subst3, rhs);
            return boyer.rewrite(tmp)
          } else {
            return boyer.rewrite_with_lemmas_helper(term3, ls1)
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
  static rewrite_with_lemmas(term4, lss1) {
    let tmp;
    tmp = NofibPrelude.force(lss1);
    return boyer.rewrite_with_lemmas_helper(term4, tmp)
  } 
  static rewrite(t3) {
    let param0, param1, param2, f1, args, lemmas, param01, v, tmp, tmp1;
    if (t3 instanceof boyer.Var.class) {
      param01 = t3.i;
      v = param01;
      return boyer.Var(v)
    } else if (t3 instanceof boyer.Fun.class) {
      param0 = t3.i;
      param1 = t3.t;
      param2 = t3.l;
      f1 = param0;
      args = param1;
      lemmas = param2;
      tmp = NofibPrelude.map(boyer.rewrite, args);
      tmp1 = boyer.Fun(f1, tmp, lemmas);
      return boyer.rewrite_with_lemmas(tmp1, lemmas)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static truep(x, l) {
    let param0, param1, param2;
    if (x instanceof boyer.Fun.class) {
      param0 = x.i;
      param1 = x.t;
      param2 = x.l;
      if (param0 instanceof boyer.TRUE.class) {
        return true
      } else {
        return boyer.termInList(x, l)
      }
    } else {
      return boyer.termInList(x, l)
    }
  } 
  static falsep(x1, l1) {
    let param0, param1, param2;
    if (x1 instanceof boyer.Fun.class) {
      param0 = x1.i;
      param1 = x1.t;
      param2 = x1.l;
      if (param0 instanceof boyer.FALSE.class) {
        return true
      } else {
        return boyer.termInList(x1, l1)
      }
    } else {
      return boyer.termInList(x1, l1)
    }
  } 
  static tautologyp(x2, true_lst, false_lst) {
    let param0, param1, param2, param01, param11, cond, param02, param12, t4, param03, param13, e, scrut, scrut1, scrut2, scrut3, scrut4, scrut5, tmp, tmp1;
    scrut5 = boyer.truep(x2, true_lst);
    if (scrut5 === true) {
      return true
    } else {
      scrut4 = boyer.falsep(x2, false_lst);
      if (scrut4 === true) {
        return false
      } else {
        if (x2 instanceof boyer.Fun.class) {
          param0 = x2.i;
          param1 = x2.t;
          param2 = x2.l;
          if (param0 instanceof boyer.IF.class) {
            if (param1 instanceof NofibPrelude.Cons.class) {
              param01 = param1.head;
              param11 = param1.tail;
              cond = param01;
              if (param11 instanceof NofibPrelude.Cons.class) {
                param02 = param11.head;
                param12 = param11.tail;
                t4 = param02;
                if (param12 instanceof NofibPrelude.Cons.class) {
                  param03 = param12.head;
                  param13 = param12.tail;
                  e = param03;
                  if (param13 instanceof NofibPrelude.Nil.class) {
                    scrut3 = boyer.truep(cond, true_lst);
                    if (scrut3 === true) {
                      return boyer.tautologyp(t4, true_lst, false_lst)
                    } else {
                      scrut2 = boyer.falsep(cond, false_lst);
                      if (scrut2 === true) {
                        return boyer.tautologyp(e, true_lst, false_lst)
                      } else {
                        tmp = NofibPrelude.Cons(cond, true_lst);
                        scrut = boyer.tautologyp(t4, tmp, false_lst);
                        if (scrut === true) {
                          tmp1 = NofibPrelude.Cons(cond, false_lst);
                          scrut1 = boyer.tautologyp(e, true_lst, tmp1);
                          if (scrut1 === true) {
                            return true
                          } else {
                            return false
                          }
                        } else {
                          return false
                        }
                      }
                    }
                  } else {
                    return false
                  }
                } else {
                  return false
                }
              } else {
                return false
              }
            } else {
              return false
            }
          } else {
            return false
          }
        } else {
          return false
        }
      }
    }
  } 
  static tautp(x3) {
    let tmp;
    tmp = boyer.rewrite(x3);
    return boyer.tautologyp(tmp, NofibPrelude.Nil, NofibPrelude.Nil)
  } 
  static test0(xxxx) {
    let a, b, c, d, u, w, x4, y, z, boyerFalse, nil, boyerTrue, zero, subst0, theorem, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50;
    tmp = boyer.Var(boyer.A);
    a = tmp;
    tmp1 = boyer.Var(boyer.B);
    b = tmp1;
    tmp2 = boyer.Var(boyer.C);
    c = tmp2;
    tmp3 = boyer.Var(boyer.D);
    d = tmp3;
    tmp4 = boyer.Var(boyer.U);
    u = tmp4;
    tmp5 = boyer.Var(boyer.W);
    w = tmp5;
    tmp6 = boyer.Var(boyer.X);
    x4 = tmp6;
    tmp7 = boyer.Var(boyer.Y);
    y = tmp7;
    tmp8 = boyer.Var(boyer.Z);
    z = tmp8;
    tmp9 = NofibPrelude.lazy(lambda38);
    tmp10 = boyer.Fun(boyer.FALSE, NofibPrelude.Nil, tmp9);
    boyerFalse = tmp10;
    tmp11 = NofibPrelude.lazy(lambda39);
    tmp12 = boyer.Fun(boyer.NIL, NofibPrelude.Nil, tmp11);
    nil = tmp12;
    tmp13 = NofibPrelude.lazy(lambda40);
    tmp14 = boyer.Fun(boyer.TRUE, NofibPrelude.Nil, tmp13);
    boyerTrue = tmp14;
    tmp15 = NofibPrelude.lazy(lambda41);
    tmp16 = boyer.Fun(boyer.ZERO, NofibPrelude.Nil, tmp15);
    zero = tmp16;
    tmp17 = plus$(u, w, x4, y, z, boyerFalse, boyerTrue, zero, a, b);
    tmp18 = plus$(u, w, x4, y, z, boyerFalse, boyerTrue, zero, c, zero);
    tmp19 = plus$(u, w, x4, y, z, boyerFalse, boyerTrue, zero, tmp17, tmp18);
    tmp20 = f(tmp19);
    tmp21 = times$(u, w, x4, y, z, boyerFalse, boyerTrue, zero, a, b);
    tmp22 = plus$(u, w, x4, y, z, boyerFalse, boyerTrue, zero, c, d);
    tmp23 = times$(u, w, x4, y, z, boyerFalse, boyerTrue, zero, tmp21, tmp22);
    tmp24 = f(tmp23);
    tmp25 = append_$(x4, y, z, a, b);
    tmp26 = append_$(x4, y, z, tmp25, nil);
    tmp27 = reverse_$(x4, y, z, tmp26);
    tmp28 = f(tmp27);
    tmp29 = plus$(u, w, x4, y, z, boyerFalse, boyerTrue, zero, a, b);
    tmp30 = difference$(u, w, x4, y, z, boyerFalse, boyerTrue, zero, x4, y);
    tmp31 = equal$(u, w, x4, y, z, boyerFalse, boyerTrue, zero, tmp29, tmp30);
    tmp32 = remainder$(u, w, x4, y, z, boyerFalse, boyerTrue, zero, a, b);
    tmp33 = length_$(u, w, x4, y, z, boyerFalse, boyerTrue, zero, b);
    tmp34 = member$(u, w, x4, y, z, boyerFalse, boyerTrue, a, tmp33);
    tmp35 = lessp$(u, w, x4, y, z, boyerFalse, boyerTrue, zero, tmp32, tmp34);
    tmp36 = NofibPrelude.Cons([
      boyer.W,
      tmp35
    ], NofibPrelude.Nil);
    tmp37 = NofibPrelude.Cons([
      boyer.U,
      tmp31
    ], tmp36);
    tmp38 = NofibPrelude.Cons([
      boyer.Z,
      tmp28
    ], tmp37);
    tmp39 = NofibPrelude.Cons([
      boyer.Y,
      tmp24
    ], tmp38);
    tmp40 = NofibPrelude.Cons([
      boyer.X,
      tmp20
    ], tmp39);
    subst0 = tmp40;
    tmp41 = implies$(u, w, x4, y, z, boyerFalse, boyerTrue, xxxx, y);
    tmp42 = implies$(u, w, x4, y, z, boyerFalse, boyerTrue, y, z);
    tmp43 = implies$(u, w, x4, y, z, boyerFalse, boyerTrue, z, u);
    tmp44 = implies$(u, w, x4, y, z, boyerFalse, boyerTrue, u, w);
    tmp45 = and_$(u, w, x4, y, z, boyerFalse, boyerTrue, tmp43, tmp44);
    tmp46 = and_$(u, w, x4, y, z, boyerFalse, boyerTrue, tmp42, tmp45);
    tmp47 = and_$(u, w, x4, y, z, boyerFalse, boyerTrue, tmp41, tmp46);
    tmp48 = implies$(u, w, x4, y, z, boyerFalse, boyerTrue, x4, w);
    tmp49 = implies$(u, w, x4, y, z, boyerFalse, boyerTrue, tmp47, tmp48);
    theorem = tmp49;
    tmp50 = boyer.apply_subst(subst0, theorem);
    return boyer.tautp(tmp50)
  } 
  static testBoyer_nofib(n) {
    let tmp, tmp1;
    tmp = boyer.Var(boyer.X);
    tmp1 = NofibPrelude.replicate(n, tmp);
    return NofibPrelude.all(boyer.test0, tmp1)
  }
  static toString() { return "boyer"; }
};
let boyer = boyer1; export default boyer;
