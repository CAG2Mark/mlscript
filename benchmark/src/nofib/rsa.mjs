import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let z_add, unlines, encrypt, testRsa_nofib, hash, string_of_z, z_of_int, power_, z_mul, z_sqr, size, and_, z_sub, z_div, z_mod, code, even, int_if_char, z_equal, collect, const0, const31, const1, const2, const128, intput, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, lambda;
z_of_int = function z_of_int(x) {
  return runtime.safeCall(globalThis.BigInt(x))
};
string_of_z = function string_of_z(x) {
  let tmp8;
  tmp8 = x + "";
  return NofibPrelude.nofibStringToList(tmp8)
};
z_add = function z_add(x, y) {
  return x + y
};
z_mul = function z_mul(x, y) {
  return x * y
};
z_sub = function z_sub(x, y) {
  return x - y
};
z_div = function z_div(x, y) {
  return x / y
};
z_mod = function z_mod(x, y) {
  return x % y
};
z_equal = function z_equal(x, y) {
  return x === y
};
z_sqr = function z_sqr(x) {
  return x * x
};
int_if_char = function int_if_char(c) {
  return runtime.safeCall(c.codePointAt(0))
};
hash = function hash(str) {
  let tmp8, lambda1;
  lambda1 = (undefined, function (acc, c) {
    let tmp9, tmp10, tmp11;
    tmp9 = int_if_char(c);
    tmp10 = z_of_int(tmp9);
    tmp11 = z_mul(acc, const31);
    return z_add(tmp10, tmp11)
  });
  tmp8 = lambda1;
  return NofibPrelude.foldl(tmp8, const0, str)
};
and_ = function and_(ls) {
  let param0, param1, h, t;
  if (ls instanceof NofibPrelude.Nil.class) {
    return true
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    if (h === true) {
      return and_(t)
    } else {
      return false
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
unlines = function unlines(ls) {
  let tmp8, lambda1;
  lambda1 = (undefined, function (l) {
    let tmp9;
    tmp9 = NofibPrelude.Cons("\n", NofibPrelude.Nil);
    return NofibPrelude.append(l, tmp9)
  });
  tmp8 = NofibPrelude.map(lambda1, ls);
  return NofibPrelude.concat(tmp8)
};
even = function even(a) {
  let tmp8;
  tmp8 = z_mod(a, const2);
  return tmp8 === const0
};
code = function code(ls) {
  let tmp8, lambda1;
  lambda1 = (undefined, function (x, y) {
    let tmp9, tmp10, tmp11;
    tmp9 = z_mul(const128, x);
    tmp10 = int_if_char(y);
    tmp11 = z_of_int(tmp10);
    return z_add(tmp9, tmp11)
  });
  tmp8 = lambda1;
  return NofibPrelude.foldl(tmp8, const0, ls)
};
collect = function collect(n, xs) {
  let scrut, tmp8, tmp9, tmp10;
  scrut = n === 0;
  if (scrut === true) {
    return NofibPrelude.Nil
  } else {
    if (xs instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else {
      tmp8 = NofibPrelude.take(n, xs);
      tmp9 = NofibPrelude.drop(n, xs);
      tmp10 = collect(n, tmp9);
      return NofibPrelude.Cons(tmp8, tmp10)
    }
  }
};
size = function size(n) {
  let tmp8, tmp9, tmp10;
  tmp8 = string_of_z(n);
  tmp9 = NofibPrelude.listLen(tmp8);
  tmp10 = tmp9 * 47;
  return NofibPrelude.intDiv(tmp10, 100)
};
encrypt = function encrypt(n, e, s) {
  let tmp8, tmp9, tmp10, tmp11, lambda1;
  lambda1 = (undefined, function (c) {
    let tmp12, tmp13;
    tmp12 = code(c);
    tmp13 = power_(e, n, tmp12);
    return string_of_z(tmp13)
  });
  tmp8 = lambda1;
  tmp9 = size(n);
  tmp10 = collect(tmp9, s);
  tmp11 = NofibPrelude.map(tmp8, tmp10);
  return unlines(tmp11)
};
power_ = function power_(n, m, x) {
  let scrut, scrut1, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13;
  scrut1 = z_equal(n, const0);
  if (scrut1 === true) {
    return const1
  } else {
    scrut = even(n);
    if (scrut === true) {
      tmp8 = z_div(n, const2);
      tmp9 = power_(tmp8, m, x);
      tmp10 = z_sqr(tmp9);
      return z_mod(tmp10, m)
    } else {
      tmp11 = z_sub(n, const1);
      tmp12 = power_(tmp11, m, x);
      tmp13 = z_mul(x, tmp12);
      return z_mod(tmp13, m)
    }
  }
};
testRsa_nofib = function testRsa_nofib(_) {
  let tmp8, tmp9, tmp10;
  tmp8 = z_of_int("2036450659413645137870851576872812267542175329986469156678671505255564383842535488743101632280716717779536712424613501441720195827856504007305662157107");
  tmp9 = z_of_int("387784473137902876992546516170169092918207676456888779623592396031349415024943784869634893342729620092877891356118467738167515879252473323905128540213");
  tmp10 = encrypt(tmp8, tmp9, intput);
  return hash(tmp10)
};
tmp = z_of_int(0);
const0 = tmp;
tmp1 = z_of_int(31);
const31 = tmp1;
tmp2 = z_of_int(1);
const1 = tmp2;
tmp3 = z_of_int(2);
const2 = tmp3;
tmp4 = z_of_int(128);
const128 = tmp4;
tmp5 = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/rsa.faststdin"));
tmp6 = runtime.safeCall(tmp5.toString());
tmp7 = NofibPrelude.nofibStringToList(tmp6);
intput = tmp7;
lambda = (undefined, function () {
  return testRsa_nofib(0)
});
BenchmarkPrelude.benchmark(lambda)