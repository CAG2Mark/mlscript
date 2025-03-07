import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let goto1, returnn, deletee, readAt, end, writes, readChar, peekChar, program, pressAnyKey, writeString, loop, promptReadAt, moveTo, ringBell, writeChar, writeAt, highlight, clearScreen, unreadChar, at, testAnsi_nofib, cls, tmp, lambda;
goto1 = function goto(x, y) {
  let tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9;
  tmp1 = NofibPrelude.stringOfInt(y);
  tmp2 = NofibPrelude.nofibStringToList(tmp1);
  tmp3 = NofibPrelude.stringOfInt(x);
  tmp4 = NofibPrelude.nofibStringToList(tmp3);
  tmp5 = NofibPrelude.nofibStringToList("H");
  tmp6 = NofibPrelude.append(tmp4, tmp5);
  tmp7 = NofibPrelude.Cons(";", tmp6);
  tmp8 = NofibPrelude.append(tmp2, tmp7);
  tmp9 = NofibPrelude.Cons("[", tmp8);
  return NofibPrelude.Cons("E", tmp9)
};
at = function at(x_y, s) {
  let first1, first0, x, y, tmp1;
  if (globalThis.Array.isArray(x_y) && x_y.length === 2) {
    first0 = x_y[0];
    first1 = x_y[1];
    x = first0;
    y = first1;
    tmp1 = goto1(x, y);
    return NofibPrelude.append(tmp1, s)
  } else {
    throw new globalThis.Error("match error");
  }
};
highlight = function highlight(s) {
  let tmp1, tmp2, tmp3;
  tmp1 = NofibPrelude.nofibStringToList("ESC[7m");
  tmp2 = NofibPrelude.nofibStringToList("ESC[0m");
  tmp3 = NofibPrelude.append(s, tmp2);
  return NofibPrelude.append(tmp1, tmp3)
};
end = function end(xs) {
  return NofibPrelude.nofibStringToList("")
};
readChar = function readChar(eof, consume, cs) {
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
};
peekChar = function peekChar(eof, consume, cs) {
  let param0, param1, c, cs1, tmp1;
  if (cs instanceof NofibPrelude.Nil.class) {
    return runtime.safeCall(eof(NofibPrelude.Nil))
  } else if (cs instanceof NofibPrelude.Cons.class) {
    param0 = cs.head;
    param1 = cs.tail;
    c = param0;
    cs1 = param1;
    tmp1 = NofibPrelude.Cons(c, cs1);
    return runtime.safeCall(consume(c, tmp1))
  } else {
    throw new globalThis.Error("match error");
  }
};
pressAnyKey = function pressAnyKey(prog, x) {
  let lambda1;
  lambda1 = (undefined, function (c, x1) {
    return runtime.safeCall(prog(x1))
  });
  return readChar(prog, lambda1, x)
};
unreadChar = function unreadChar(c, prog, cs) {
  let tmp1;
  tmp1 = NofibPrelude.Cons(c, cs);
  return runtime.safeCall(prog(tmp1))
};
writeChar = function writeChar(c, prog, cs) {
  let tmp1;
  tmp1 = runtime.safeCall(prog(cs));
  return NofibPrelude.Cons(c, tmp1)
};
writeString = function writeString(s, prog, cs) {
  let tmp1;
  tmp1 = runtime.safeCall(prog(cs));
  return NofibPrelude.append(s, tmp1)
};
writes = function writes(ss, a, b) {
  let tmp1;
  tmp1 = NofibPrelude.concat(ss);
  return writeString(tmp1, a, b)
};
ringBell = function ringBell(prog, cs) {
  return writeChar("B", prog, cs)
};
clearScreen = function clearScreen(a, b) {
  return writeString(cls, a, b)
};
writeAt = function writeAt(x_y, s, a) {
  let first1, first0, x, y, lambda1;
  if (globalThis.Array.isArray(x_y) && x_y.length === 2) {
    first0 = x_y[0];
    first1 = x_y[1];
    x = first0;
    y = first1;
    lambda1 = (undefined, function (p) {
      let tmp1, tmp2;
      tmp1 = goto1(x, y);
      tmp2 = NofibPrelude.append(tmp1, s);
      return writeString(tmp2, a, p)
    });
    return lambda1
  } else {
    throw new globalThis.Error("match error");
  }
};
moveTo = function moveTo(x_y, a) {
  let first1, first0, x, y, lambda1;
  if (globalThis.Array.isArray(x_y) && x_y.length === 2) {
    first0 = x_y[0];
    first1 = x_y[1];
    x = first0;
    y = first1;
    lambda1 = (undefined, function (p) {
      let tmp1;
      tmp1 = goto1(x, y);
      return writeString(tmp1, a, p)
    });
    return lambda1
  } else {
    throw new globalThis.Error("match error");
  }
};
returnn = function returnn(s, consume) {
  let tmp1;
  tmp1 = NofibPrelude.reverse(s);
  return runtime.safeCall(consume(tmp1))
};
deletee = function deletee(n, s, l, consume) {
  let scrut, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
  scrut = n > 0;
  if (scrut === true) {
    tmp1 = NofibPrelude.nofibStringToList("BS_BS");
    tmp2 = n - 1;
    tmp3 = NofibPrelude.tail(s);
    tmp4 = loop(tmp2, tmp3, l, consume);
    return writeString(tmp1, tmp4)
  } else {
    tmp5 = NofibPrelude.nofibStringToList("");
    tmp6 = loop(0, tmp5, l, consume);
    return ringBell(tmp6)
  }
};
loop = function loop(n, s, l, consume) {
  let lambda1;
  lambda1 = (undefined, function (x) {
    let tmp1, tmp2, lambda2;
    tmp1 = returnn(s, consume);
    lambda2 = (undefined, function (c, d) {
      let scrut, scrut1, scrut2, scrut3, tmp3, tmp4, tmp5, tmp6;
      scrut3 = c == "B";
      if (scrut3 === true) {
        return deletee(n, s, l, consume)
      } else {
        scrut2 = c == "D";
        if (scrut2 === true) {
          return deletee(n, s, l, consume)
        } else {
          scrut1 = c == "`";
          if (scrut1 === true) {
            return returnn(s, consume)
          } else {
            scrut = n < l;
            if (scrut === true) {
              tmp3 = n + 1;
              tmp4 = NofibPrelude.Cons(c, s);
              tmp5 = loop(tmp3, tmp4, l, consume);
              return writeChar(c, tmp5, d)
            } else {
              tmp6 = loop(n, s, l, consume);
              return ringBell(tmp6, d)
            }
          }
        }
      }
    });
    tmp2 = lambda2;
    return readChar(tmp1, tmp2, x)
  });
  return lambda1
};
readAt = function readAt(x_y, l, consume) {
  let tmp1, tmp2, tmp3;
  tmp1 = NofibPrelude.replicate(l, "_");
  tmp2 = loop(0, "", l, consume);
  tmp3 = moveTo(x_y, tmp2);
  return writeAt(x_y, tmp1, tmp3)
};
promptReadAt = function promptReadAt(x_y, l, prompt, consume) {
  let first1, first0, x, y, tmp1, tmp2, tmp3;
  if (globalThis.Array.isArray(x_y) && x_y.length === 2) {
    first0 = x_y[0];
    first1 = x_y[1];
    x = first0;
    y = first1;
    tmp1 = NofibPrelude.listLen(prompt);
    tmp2 = x + tmp1;
    tmp3 = readAt([
      tmp2,
      y
    ], l, consume);
    return writeAt([
      x,
      y
    ], prompt, tmp3)
  } else {
    throw new globalThis.Error("match error");
  }
};
program = function program(input) {
  let tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, lambda1;
  tmp1 = NofibPrelude.nofibStringToList("Demonstration program");
  tmp2 = highlight(tmp1);
  tmp3 = at([
    17,
    5
  ], tmp2);
  tmp4 = NofibPrelude.nofibStringToList("Version 1.0");
  tmp5 = at([
    48,
    5
  ], tmp4);
  tmp6 = NofibPrelude.nofibStringToList("This program illustrates a simple approach");
  tmp7 = at([
    17,
    7
  ], tmp6);
  tmp8 = NofibPrelude.nofibStringToList("to screen-based interactive programs using");
  tmp9 = at([
    17,
    8
  ], tmp8);
  tmp10 = NofibPrelude.nofibStringToList("the Hugs functional programming system.");
  tmp11 = at([
    17,
    9
  ], tmp10);
  tmp12 = NofibPrelude.nofibStringToList("Please press any key to continue ...");
  tmp13 = at([
    17,
    11
  ], tmp12);
  tmp14 = NofibPrelude.Cons(tmp13, NofibPrelude.Nil);
  tmp15 = NofibPrelude.Cons(tmp11, tmp14);
  tmp16 = NofibPrelude.Cons(tmp9, tmp15);
  tmp17 = NofibPrelude.Cons(tmp7, tmp16);
  tmp18 = NofibPrelude.Cons(tmp5, tmp17);
  tmp19 = NofibPrelude.Cons(tmp3, tmp18);
  tmp20 = NofibPrelude.Cons(cls, tmp19);
  lambda1 = (undefined, function (x) {
    let tmp22, tmp23, tmp24, lambda2;
    tmp22 = NofibPrelude.nofibStringToList("Please enter your name: ");
    lambda2 = (undefined, function (name) {
      let reply, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, lambda3;
      tmp25 = NofibPrelude.nofibStringToList("Hello ");
      tmp26 = NofibPrelude.nofibStringToList("!");
      tmp27 = NofibPrelude.append(name, tmp26);
      tmp28 = NofibPrelude.append(tmp25, tmp27);
      reply = tmp28;
      tmp29 = NofibPrelude.listLen(reply);
      tmp30 = tmp29 / 2;
      tmp31 = 40 - tmp30;
      lambda3 = (undefined, function (y) {
        let tmp33, lambda4;
        tmp33 = NofibPrelude.nofibStringToList("I'm waiting...");
        lambda4 = (undefined, function (x1) {
          return pressAnyKey(end, x1)
        });
        return writeString(tmp33, lambda4, y)
      });
      tmp32 = moveTo([
        1,
        23
      ], lambda3);
      return writeAt([
        tmp31,
        18
      ], reply, tmp32)
    });
    tmp23 = lambda2;
    tmp24 = promptReadAt([
      17,
      15
    ], 18, tmp22, tmp23);
    return pressAnyKey(tmp24, x)
  });
  tmp21 = lambda1;
  return writes(tmp20, tmp21, input)
};
testAnsi_nofib = function testAnsi_nofib(n) {
  let tmp1, tmp2, tmp3, lambda1;
  tmp1 = NofibPrelude.replicate(n, program);
  lambda1 = (undefined, function (x) {
    return x
  });
  tmp2 = NofibPrelude.foldr(NofibPrelude.compose, lambda1, tmp1);
  tmp3 = NofibPrelude.nofibStringToList("testtesttest");
  return runtime.safeCall(tmp2(tmp3))
};
tmp = NofibPrelude.nofibStringToList("L");
cls = tmp;
lambda = (undefined, function () {
  let tmp1;
  tmp1 = testAnsi_nofib(1);
  return NofibPrelude.nofibListToString(tmp1)
});
BenchmarkPrelude.benchmark(lambda)