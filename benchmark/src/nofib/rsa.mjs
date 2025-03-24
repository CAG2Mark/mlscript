import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let rsa1;
rsa1 = class rsa {
  static {
    rsa1 = rsa;
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, lambda;
    tmp = rsa.z_of_int(0);
    this.const0 = tmp;
    tmp1 = rsa.z_of_int(31);
    this.const31 = tmp1;
    tmp2 = rsa.z_of_int(1);
    this.const1 = tmp2;
    tmp3 = rsa.z_of_int(2);
    this.const2 = tmp3;
    tmp4 = rsa.z_of_int(128);
    this.const128 = tmp4;
    tmp5 = runtime.safeCall(fs.readFileSync("hkmc2/shared/src/test/mlscript/nofib/input/rsa.faststdin"));
    tmp6 = runtime.safeCall(tmp5.toString());
    tmp7 = NofibPrelude.nofibStringToList(tmp6);
    this.intput = tmp7;
    lambda = (undefined, function () {
      return rsa.testRsa_nofib(0)
    });
    BenchmarkPrelude.benchmark(lambda)
  }
  static z_of_int(x) {
    return runtime.safeCall(globalThis.BigInt(x))
  } 
  static string_of_z(x1) {
    let tmp;
    tmp = x1 + "";
    return NofibPrelude.nofibStringToList(tmp)
  } 
  static z_add(x2, y) {
    return x2 + y
  } 
  static z_mul(x3, y1) {
    return x3 * y1
  } 
  static z_sub(x4, y2) {
    return x4 - y2
  } 
  static z_div(x5, y3) {
    return x5 / y3
  } 
  static z_mod(x6, y4) {
    return x6 % y4
  } 
  static z_equal(x7, y5) {
    return x7 === y5
  } 
  static z_sqr(x8) {
    return x8 * x8
  } 
  static int_if_char(c) {
    return runtime.safeCall(c.codePointAt(0))
  } 
  static hash(str) {
    let tmp, lambda;
    lambda = (undefined, function (acc, c1) {
      let tmp1, tmp2, tmp3;
      tmp1 = rsa.int_if_char(c1);
      tmp2 = rsa.z_of_int(tmp1);
      tmp3 = rsa.z_mul(acc, rsa.const31);
      return rsa.z_add(tmp2, tmp3)
    });
    tmp = lambda;
    return NofibPrelude.foldl(tmp, rsa.const0, str)
  } 
  static and_(ls) {
    let param0, param1, h, t;
    if (ls instanceof NofibPrelude.Nil.class) {
      return true
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      h = param0;
      t = param1;
      if (h === true) {
        return rsa.and_(t)
      } else {
        return false
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static unlines(ls1) {
    let tmp, lambda;
    lambda = (undefined, function (l) {
      let tmp1;
      tmp1 = NofibPrelude.Cons("\n", NofibPrelude.Nil);
      return NofibPrelude.append(l, tmp1)
    });
    tmp = NofibPrelude.map(lambda, ls1);
    return NofibPrelude.concat(tmp)
  } 
  static even(a) {
    let tmp;
    tmp = rsa.z_mod(a, rsa.const2);
    return tmp === rsa.const0
  } 
  static code(ls2) {
    let tmp, lambda;
    lambda = (undefined, function (x9, y6) {
      let tmp1, tmp2, tmp3;
      tmp1 = rsa.z_mul(rsa.const128, x9);
      tmp2 = rsa.int_if_char(y6);
      tmp3 = rsa.z_of_int(tmp2);
      return rsa.z_add(tmp1, tmp3)
    });
    tmp = lambda;
    return NofibPrelude.foldl(tmp, rsa.const0, ls2)
  } 
  static collect(n, xs) {
    let scrut, tmp, tmp1, tmp2;
    scrut = n === 0;
    if (scrut === true) {
      return NofibPrelude.Nil
    } else {
      if (xs instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else {
        tmp = NofibPrelude.take(n, xs);
        tmp1 = NofibPrelude.drop(n, xs);
        tmp2 = rsa.collect(n, tmp1);
        return NofibPrelude.Cons(tmp, tmp2)
      }
    }
  } 
  static size(n1) {
    let tmp, tmp1, tmp2;
    tmp = rsa.string_of_z(n1);
    tmp1 = NofibPrelude.listLen(tmp);
    tmp2 = tmp1 * 47;
    return NofibPrelude.intDiv(tmp2, 100)
  } 
  static encrypt(n2, e, s) {
    let tmp, tmp1, tmp2, tmp3, lambda;
    lambda = (undefined, function (c1) {
      let tmp4, tmp5;
      tmp4 = rsa.code(c1);
      tmp5 = rsa.power(e, n2, tmp4);
      return rsa.string_of_z(tmp5)
    });
    tmp = lambda;
    tmp1 = rsa.size(n2);
    tmp2 = rsa.collect(tmp1, s);
    tmp3 = NofibPrelude.map(tmp, tmp2);
    return rsa.unlines(tmp3)
  } 
  static power(n3, m, x9) {
    let scrut, scrut1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    scrut1 = rsa.z_equal(n3, rsa.const0);
    if (scrut1 === true) {
      return rsa.const1
    } else {
      scrut = rsa.even(n3);
      if (scrut === true) {
        tmp = rsa.z_div(n3, rsa.const2);
        tmp1 = rsa.power(tmp, m, x9);
        tmp2 = rsa.z_sqr(tmp1);
        return rsa.z_mod(tmp2, m)
      } else {
        tmp3 = rsa.z_sub(n3, rsa.const1);
        tmp4 = rsa.power(tmp3, m, x9);
        tmp5 = rsa.z_mul(x9, tmp4);
        return rsa.z_mod(tmp5, m)
      }
    }
  } 
  static testRsa_nofib(_) {
    let tmp, tmp1, tmp2;
    tmp = rsa.z_of_int("2036450659413645137870851576872812267542175329986469156678671505255564383842535488743101632280716717779536712424613501441720195827856504007305662157107");
    tmp1 = rsa.z_of_int("387784473137902876992546516170169092918207676456888779623592396031349415024943784869634893342729620092877891356118467738167515879252473323905128540213");
    tmp2 = rsa.encrypt(tmp, tmp1, rsa.intput);
    return rsa.hash(tmp2)
  }
  static toString() { return "rsa"; }
};
let rsa = rsa1; export default rsa;
