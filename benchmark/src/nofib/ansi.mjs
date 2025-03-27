import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let ansi1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda$, lambda$1, lambda$2, lambda$3, lambda$4;
lambda9 = (undefined, function (x) {
  return x
});
lambda8 = (undefined, function (x) {
  return ansi1.pressAnyKey(ansi1.end, x)
});
lambda7 = (undefined, function (y) {
  let tmp;
  tmp = NofibPrelude.nofibStringToList("I'm waiting...");
  return ansi1.writeString(tmp, lambda8, y)
});
lambda6 = (undefined, function (name) {
  let reply, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
  tmp = NofibPrelude.nofibStringToList("Hello ");
  tmp1 = NofibPrelude.nofibStringToList("!");
  tmp2 = NofibPrelude.append(name, tmp1);
  tmp3 = NofibPrelude.append(tmp, tmp2);
  reply = tmp3;
  tmp4 = NofibPrelude.listLen(reply);
  tmp5 = tmp4 / 2;
  tmp6 = 40 - tmp5;
  tmp7 = ansi1.moveTo([
    1,
    23
  ], lambda7);
  return ansi1.writeAt([
    tmp6,
    18
  ], reply, tmp7)
});
lambda5 = (undefined, function (x) {
  let tmp, tmp1, tmp2;
  tmp = NofibPrelude.nofibStringToList("Please enter your name: ");
  tmp1 = lambda6;
  tmp2 = ansi1.promptReadAt([
    17,
    15
  ], 18, tmp, tmp1);
  return ansi1.pressAnyKey(tmp2, x)
});
lambda$4 = function lambda$(n, s, l, consume, c, d) {
  let scrut, scrut1, scrut2, scrut3, tmp, tmp1, tmp2, tmp3;
  scrut3 = c == "B";
  if (scrut3 === true) {
    return ansi1.deletee(n, s, l, consume)
  } else {
    scrut2 = c == "D";
    if (scrut2 === true) {
      return ansi1.deletee(n, s, l, consume)
    } else {
      scrut1 = c == "`";
      if (scrut1 === true) {
        return ansi1.returnn(s, consume)
      } else {
        scrut = n < l;
        if (scrut === true) {
          tmp = n + 1;
          tmp1 = NofibPrelude.Cons(c, s);
          tmp2 = ansi1.loop(tmp, tmp1, l, consume);
          return ansi1.writeChar(c, tmp2, d)
        } else {
          tmp3 = ansi1.loop(n, s, l, consume);
          return ansi1.ringBell(tmp3, d)
        }
      }
    }
  }
};
lambda4 = (undefined, function (n, s, l, consume) {
  return (c, d) => {
    return lambda$4(n, s, l, consume, c, d)
  }
});
lambda$3 = function lambda$(n, s, l, consume, x) {
  let tmp, tmp1;
  tmp = ansi1.returnn(s, consume);
  tmp1 = runtime.safeCall(lambda4(n, s, l, consume));
  return ansi1.readChar(tmp, tmp1, x)
};
lambda3 = (undefined, function (n, s, l, consume) {
  return (x) => {
    return lambda$3(n, s, l, consume, x)
  }
});
lambda$2 = function lambda$(a, x, y, p) {
  let tmp;
  tmp = ansi1.goto(x, y);
  return ansi1.writeString(tmp, a, p)
};
lambda2 = (undefined, function (a, x, y) {
  return (p) => {
    return lambda$2(a, x, y, p)
  }
});
lambda$1 = function lambda$(s, a, x, y, p) {
  let tmp, tmp1;
  tmp = ansi1.goto(x, y);
  tmp1 = NofibPrelude.append(tmp, s);
  return ansi1.writeString(tmp1, a, p)
};
lambda1 = (undefined, function (s, a, x, y) {
  return (p) => {
    return lambda$1(s, a, x, y, p)
  }
});
lambda$ = function lambda$(prog, c, x) {
  return runtime.safeCall(prog(x))
};
lambda = (undefined, function (prog) {
  return (c, x) => {
    return lambda$(prog, c, x)
  }
});
ansi1 = class ansi {
  static {
    ansi1 = ansi;
    let tmp, lambda10;
    tmp = NofibPrelude.nofibStringToList("L");
    this.cls = tmp;
    lambda10 = (undefined, function () {
      let tmp1;
      tmp1 = ansi.testAnsi_nofib(1);
      return NofibPrelude.nofibListToString(tmp1)
    });
    BenchmarkPrelude.benchmark(lambda10)
  }
  static goto(x, y) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
    tmp = NofibPrelude.stringOfInt(y);
    tmp1 = NofibPrelude.nofibStringToList(tmp);
    tmp2 = NofibPrelude.stringOfInt(x);
    tmp3 = NofibPrelude.nofibStringToList(tmp2);
    tmp4 = NofibPrelude.nofibStringToList("H");
    tmp5 = NofibPrelude.append(tmp3, tmp4);
    tmp6 = NofibPrelude.Cons(";", tmp5);
    tmp7 = NofibPrelude.append(tmp1, tmp6);
    tmp8 = NofibPrelude.Cons("[", tmp7);
    return NofibPrelude.Cons("E", tmp8)
  } 
  static at(x_y, s) {
    let first1, first0, x1, y1, tmp;
    if (globalThis.Array.isArray(x_y) && x_y.length === 2) {
      first0 = x_y[0];
      first1 = x_y[1];
      x1 = first0;
      y1 = first1;
      tmp = ansi.goto(x1, y1);
      return NofibPrelude.append(tmp, s)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static highlight(s1) {
    let tmp, tmp1, tmp2;
    tmp = NofibPrelude.nofibStringToList("ESC[7m");
    tmp1 = NofibPrelude.nofibStringToList("ESC[0m");
    tmp2 = NofibPrelude.append(s1, tmp1);
    return NofibPrelude.append(tmp, tmp2)
  } 
  static end(xs) {
    return NofibPrelude.nofibStringToList("")
  } 
  static readChar(eof, consume, cs) {
    let param0, param1, c, cs1;
    if (cs instanceof NofibPrelude.Nil.class) {
      return runtime.safeCall(eof(NofibPrelude.Nil))
    } else if (cs instanceof NofibPrelude.Cons.class) {
      param0 = cs.head;
      param1 = cs.tail;
      c = param0;
      cs1 = param1;
      return runtime.safeCall(consume(c, cs1))
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static peekChar(eof1, consume1, cs1) {
    let param0, param1, c, cs2, tmp;
    if (cs1 instanceof NofibPrelude.Nil.class) {
      return runtime.safeCall(eof1(NofibPrelude.Nil))
    } else if (cs1 instanceof NofibPrelude.Cons.class) {
      param0 = cs1.head;
      param1 = cs1.tail;
      c = param0;
      cs2 = param1;
      tmp = NofibPrelude.Cons(c, cs2);
      return runtime.safeCall(consume1(c, tmp))
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static pressAnyKey(prog, x1) {
    let lambda$this;
    lambda$this = runtime.safeCall(lambda(prog));
    return ansi.readChar(prog, lambda$this, x1)
  } 
  static unreadChar(c, prog1, cs2) {
    let tmp;
    tmp = NofibPrelude.Cons(c, cs2);
    return runtime.safeCall(prog1(tmp))
  } 
  static writeChar(c1, prog2, cs3) {
    let tmp;
    tmp = runtime.safeCall(prog2(cs3));
    return NofibPrelude.Cons(c1, tmp)
  } 
  static writeString(s2, prog3, cs4) {
    let tmp;
    tmp = runtime.safeCall(prog3(cs4));
    return NofibPrelude.append(s2, tmp)
  } 
  static writes(ss, a, b) {
    let tmp;
    tmp = NofibPrelude.concat(ss);
    return ansi.writeString(tmp, a, b)
  } 
  static ringBell(prog4, cs5) {
    return ansi.writeChar("B", prog4, cs5)
  } 
  static clearScreen(a1, b1) {
    return ansi.writeString(ansi.cls, a1, b1)
  } 
  static writeAt(x_y1, s3, a2) {
    let first1, first0, x2, y1;
    if (globalThis.Array.isArray(x_y1) && x_y1.length === 2) {
      first0 = x_y1[0];
      first1 = x_y1[1];
      x2 = first0;
      y1 = first1;
      return runtime.safeCall(lambda1(s3, a2, x2, y1))
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static moveTo(x_y2, a3) {
    let first1, first0, x2, y1;
    if (globalThis.Array.isArray(x_y2) && x_y2.length === 2) {
      first0 = x_y2[0];
      first1 = x_y2[1];
      x2 = first0;
      y1 = first1;
      return runtime.safeCall(lambda2(a3, x2, y1))
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static returnn(s4, consume2) {
    let tmp;
    tmp = NofibPrelude.reverse(s4);
    return runtime.safeCall(consume2(tmp))
  } 
  static deletee(n, s5, l, consume3) {
    let scrut, tmp, tmp1, tmp2, tmp3, tmp4, tmp5;
    scrut = n > 0;
    if (scrut === true) {
      tmp = NofibPrelude.nofibStringToList("BS_BS");
      tmp1 = n - 1;
      tmp2 = NofibPrelude.tail(s5);
      tmp3 = ansi.loop(tmp1, tmp2, l, consume3);
      return ansi.writeString(tmp, tmp3)
    } else {
      tmp4 = NofibPrelude.nofibStringToList("");
      tmp5 = ansi.loop(0, tmp4, l, consume3);
      return ansi.ringBell(tmp5)
    }
  } 
  static loop(n1, s6, l1, consume4) {
    return runtime.safeCall(lambda3(n1, s6, l1, consume4))
  } 
  static readAt(x_y3, l2, consume5) {
    let tmp, tmp1, tmp2;
    tmp = NofibPrelude.replicate(l2, "_");
    tmp1 = ansi.loop(0, "", l2, consume5);
    tmp2 = ansi.moveTo(x_y3, tmp1);
    return ansi.writeAt(x_y3, tmp, tmp2)
  } 
  static promptReadAt(x_y4, l3, prompt, consume6) {
    let first1, first0, x2, y1, tmp, tmp1, tmp2;
    if (globalThis.Array.isArray(x_y4) && x_y4.length === 2) {
      first0 = x_y4[0];
      first1 = x_y4[1];
      x2 = first0;
      y1 = first1;
      tmp = NofibPrelude.listLen(prompt);
      tmp1 = x2 + tmp;
      tmp2 = ansi.readAt([
        tmp1,
        y1
      ], l3, consume6);
      return ansi.writeAt([
        x2,
        y1
      ], prompt, tmp2)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static program(input) {
    let tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20;
    tmp = NofibPrelude.nofibStringToList("Demonstration program");
    tmp1 = ansi.highlight(tmp);
    tmp2 = ansi.at([
      17,
      5
    ], tmp1);
    tmp3 = NofibPrelude.nofibStringToList("Version 1.0");
    tmp4 = ansi.at([
      48,
      5
    ], tmp3);
    tmp5 = NofibPrelude.nofibStringToList("This program illustrates a simple approach");
    tmp6 = ansi.at([
      17,
      7
    ], tmp5);
    tmp7 = NofibPrelude.nofibStringToList("to screen-based interactive programs using");
    tmp8 = ansi.at([
      17,
      8
    ], tmp7);
    tmp9 = NofibPrelude.nofibStringToList("the Hugs functional programming system.");
    tmp10 = ansi.at([
      17,
      9
    ], tmp9);
    tmp11 = NofibPrelude.nofibStringToList("Please press any key to continue ...");
    tmp12 = ansi.at([
      17,
      11
    ], tmp11);
    tmp13 = NofibPrelude.Cons(tmp12, NofibPrelude.Nil);
    tmp14 = NofibPrelude.Cons(tmp10, tmp13);
    tmp15 = NofibPrelude.Cons(tmp8, tmp14);
    tmp16 = NofibPrelude.Cons(tmp6, tmp15);
    tmp17 = NofibPrelude.Cons(tmp4, tmp16);
    tmp18 = NofibPrelude.Cons(tmp2, tmp17);
    tmp19 = NofibPrelude.Cons(ansi.cls, tmp18);
    tmp20 = lambda5;
    return ansi.writes(tmp19, tmp20, input)
  } 
  static testAnsi_nofib(n2) {
    let tmp, tmp1, tmp2;
    tmp = NofibPrelude.replicate(n2, ansi.program);
    tmp1 = NofibPrelude.foldr(NofibPrelude.compose, lambda9, tmp);
    tmp2 = NofibPrelude.nofibStringToList("testtesttest");
    return runtime.safeCall(tmp1(tmp2))
  }
  static toString() { return "ansi"; }
};
let ansi = ansi1; export default ansi;
