import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
import fs from "fs";
let go, cons, lscomp, cons1, maybe, conj, trailingI, ans, cons2, eliza1, lambda, lambda1, lambda2, lambda3, lambda4, lambda5, lambda6, lambda7, lambda8, lambda9, lambda10, lambda11, lambda$, lambda$1, lambda$2, lambda$3, lscomp$, lambda$4, lambda$5, lambda$6;
lambda10 = (undefined, function (caseScrut) {
  let first1, first0, w, r, tmp;
  if (globalThis.Array.isArray(caseScrut) && caseScrut.length === 2) {
    first0 = caseScrut[0];
    first1 = caseScrut[1];
    w = first0;
    r = first1;
    tmp = eliza1.ucase(w);
    return [
      tmp,
      r
    ]
  } else {
    throw new globalThis.Error("match error");
  }
});
lambda11 = (undefined, function (x) {
  return NofibPrelude.nofibListToString(x)
});
lambda8 = (undefined, function (x) {
  let tmp;
  tmp = eliza1.trim(x);
  return eliza1.words(tmp)
});
lambda9 = (undefined, function (x) {
  let tmp;
  tmp = NofibPrelude.null_(x);
  return BenchmarkPrelude.not(tmp)
});
lambda$6 = function lambda$(input, i) {
  let tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.intMod(i, 20);
  tmp1 = NofibPrelude.take(tmp, input);
  tmp2 = NofibPrelude.map(lambda8, tmp1);
  tmp3 = NofibPrelude.filter(lambda9, tmp2);
  return eliza1.session(eliza1.initial, NofibPrelude.Nil, tmp3)
};
lambda7 = (undefined, function (input) {
  return (i) => {
    return lambda$6(input, i)
  }
});
cons2 = function cons(e, r_es) {
  let first1, first0, r, es, tmp;
  if (globalThis.Array.isArray(r_es) && r_es.length === 2) {
    first0 = r_es[0];
    first1 = r_es[1];
    r = first0;
    es = first1;
    tmp = NofibPrelude.Cons(e, es);
    return [
      r,
      tmp
    ]
  } else {
    throw new globalThis.Error("match error");
  }
};
ans = function ans(e_es, l) {
  let param0, param1, first1, first0, key, a_as, es, scrut, param01, param11, a, as_, rs, scrut1, tmp, tmp1, tmp2, tmp3, tmp4;
  if (e_es instanceof NofibPrelude.Cons.class) {
    param0 = e_es.head;
    param1 = e_es.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      key = first0;
      a_as = first1;
      es = param1;
      scrut = NofibPrelude.force(a_as);
      if (scrut instanceof NofibPrelude.LzCons.class) {
        param01 = scrut.head;
        param11 = scrut.tail;
        a = param01;
        as_ = param11;
        tmp = eliza1.replies(key, l);
        rs = tmp;
        scrut1 = eliza1.null_lz(rs);
        if (scrut1 === true) {
          tmp1 = ans(es, l);
          return cons2([
            key,
            a_as
          ], tmp1)
        } else {
          tmp2 = NofibPrelude.head_lz(rs);
          tmp3 = eliza1.makeResponse(a, tmp2);
          tmp4 = NofibPrelude.Cons([
            key,
            as_
          ], es);
          return [
            tmp3,
            tmp4
          ]
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
lambda$5 = function lambda$(key, l, x) {
  let tmp, tmp1;
  tmp = NofibPrelude.listLen(key);
  tmp1 = NofibPrelude.drop(tmp, x);
  return eliza1.conjug(l, tmp1)
};
lambda5 = (undefined, function (key, l) {
  return (x) => {
    return lambda$5(key, l, x)
  }
});
lambda$4 = function lambda$(key, ls) {
  let tmp;
  tmp = eliza1.lz_map(eliza1.ucase, ls);
  return eliza1.prefix(key, tmp)
};
lambda6 = (undefined, function (key) {
  return (ls) => {
    return lambda$4(key, ls)
  }
});
maybe = function maybe(d, xs) {
  let scrut;
  scrut = NofibPrelude.null_(xs);
  if (scrut === true) {
    return d
  } else {
    return xs
  }
};
lscomp$ = function lscomp$(w, ls) {
  let param0, param1, first1, first0, w_, m, t, scrut, tmp, tmp1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    if (globalThis.Array.isArray(param0) && param0.length === 2) {
      first0 = param0[0];
      first1 = param0[1];
      w_ = first0;
      m = first1;
      t = param1;
      tmp = eliza1.ucase(w);
      scrut = NofibPrelude.listEq(tmp, w_);
      if (scrut === true) {
        tmp1 = lscomp$(w, t);
        return NofibPrelude.Cons(m, tmp1)
      } else {
        return lscomp$(w, t)
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
lscomp = function lscomp(w) {
  return (ls) => {
    return lscomp$(w, ls)
  }
};
conj = function conj(w) {
  let tmp, tmp1, tmp2;
  tmp = lscomp$(w, eliza1.conjugates);
  tmp1 = NofibPrelude.Cons(w, NofibPrelude.Nil);
  tmp2 = NofibPrelude.append(tmp, tmp1);
  return NofibPrelude.head(tmp2)
};
cons1 = function cons(x, xs) {
  let scrut, tmp, tmp1, tmp2, tmp3;
  tmp = NofibPrelude.nofibStringToList("I");
  tmp1 = NofibPrelude.listEq(x, tmp);
  tmp2 = NofibPrelude.null_(xs);
  scrut = tmp1 && tmp2;
  if (scrut === true) {
    tmp3 = NofibPrelude.nofibStringToList("me");
    return NofibPrelude.Cons(tmp3, NofibPrelude.Nil)
  } else {
    return NofibPrelude.Cons(x, xs)
  }
};
trailingI = function trailingI(ls) {
  return NofibPrelude.foldr(cons1, NofibPrelude.Nil, ls)
};
lambda$3 = function lambda$(xs) {
  let xss, tmp, tmp1;
  if (xs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.LzNil
  } else {
    xss = xs;
    tmp = NofibPrelude.tail(xss);
    tmp1 = eliza1.tails(tmp);
    return NofibPrelude.LzCons(xss, tmp1)
  }
};
lambda4 = (undefined, function (xs) {
  return () => {
    return lambda$3(xs)
  }
});
cons = function cons(x, xs) {
  let scrut, scrut1, tmp;
  tmp = NofibPrelude.nofibStringToList(" .!?,");
  scrut = NofibPrelude.inList(x, tmp);
  if (scrut === true) {
    scrut1 = NofibPrelude.null_(xs);
    if (scrut1 === true) {
      return NofibPrelude.Nil
    } else {
      return NofibPrelude.Cons(x, xs)
    }
  } else {
    return NofibPrelude.Cons(x, xs)
  }
};
lambda3 = (undefined, function (x) {
  let tmp;
  tmp = NofibPrelude.nofibStringToList(" .!?,");
  return NofibPrelude.inList(x, tmp)
});
go = function go(ws) {
  let param0, param1, w, ws1, tmp, tmp1;
  if (ws instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (ws instanceof NofibPrelude.Cons.class) {
    param0 = ws.head;
    param1 = ws.tail;
    w = param0;
    ws1 = param1;
    tmp = go(ws1);
    tmp1 = NofibPrelude.append(w, tmp);
    return NofibPrelude.Cons(" ", tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda$2 = function lambda$(xs) {
  return eliza1.cycle(xs)
};
lambda2 = (undefined, function (xs) {
  return () => {
    return lambda$2(xs)
  }
});
lambda$1 = function lambda$(ys, h, t) {
  let tmp;
  tmp = eliza1.append_lz(t, ys);
  return NofibPrelude.LzCons(h, tmp)
};
lambda1 = (undefined, function (ys, h, t) {
  return () => {
    return lambda$1(ys, h, t)
  }
});
lambda$ = function lambda$(f, ls) {
  let param0, param1, h, t, tmp, tmp1;
  if (ls instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.LzNil
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    h = param0;
    t = param1;
    tmp = runtime.safeCall(f(h));
    tmp1 = eliza1.lz_map(f, t);
    return NofibPrelude.LzCons(tmp, tmp1)
  } else {
    throw new globalThis.Error("match error");
  }
};
lambda = (undefined, function (f, ls) {
  return () => {
    return lambda$(f, ls)
  }
});
eliza1 = class eliza {
  static {
    eliza1 = eliza;
    let lscomp1, prepare, lscomp2, canYou, canI, youAre, iDont, iFeel, whyDont, whyCant, areYou, iCant, iAm, you, yes, no, computer, iWant, question, name, because, sorry, dream, hello, maybe1, your, always, think, alike, friend, nokeyMsgs, oneways, bothways, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75, tmp76, tmp77, tmp78, tmp79, tmp80, tmp81, tmp82, tmp83, tmp84, tmp85, tmp86, tmp87, tmp88, tmp89, tmp90, tmp91, tmp92, tmp93, tmp94, tmp95, tmp96, tmp97, tmp98, tmp99, tmp100, tmp101, tmp102, tmp103, tmp104, tmp105, tmp106, tmp107, tmp108, tmp109, tmp110, tmp111, tmp112, tmp113, tmp114, tmp115, tmp116, tmp117, tmp118, tmp119, tmp120, tmp121, tmp122, tmp123, tmp124, tmp125, tmp126, tmp127, tmp128, tmp129, tmp130, tmp131, tmp132, tmp133, tmp134, tmp135, tmp136, tmp137, tmp138, tmp139, tmp140, tmp141, tmp142, tmp143, tmp144, tmp145, tmp146, tmp147, tmp148, tmp149, tmp150, tmp151, tmp152, tmp153, tmp154, tmp155, tmp156, tmp157, tmp158, tmp159, tmp160, tmp161, tmp162, tmp163, tmp164, tmp165, tmp166, tmp167, tmp168, tmp169, tmp170, tmp171, tmp172, tmp173, tmp174, tmp175, tmp176, tmp177, tmp178, tmp179, tmp180, tmp181, tmp182, tmp183, tmp184, tmp185, tmp186, tmp187, tmp188, tmp189, tmp190, tmp191, tmp192, tmp193, tmp194, tmp195, tmp196, tmp197, tmp198, tmp199, tmp200, tmp201, tmp202, tmp203, tmp204, tmp205, tmp206, tmp207, tmp208, tmp209, tmp210, tmp211, tmp212, tmp213, tmp214, tmp215, tmp216, tmp217, tmp218, tmp219, tmp220, tmp221, tmp222, tmp223, tmp224, tmp225, tmp226, tmp227, tmp228, tmp229, tmp230, tmp231, tmp232, tmp233, tmp234, tmp235, tmp236, tmp237, tmp238, tmp239, tmp240, tmp241, tmp242, tmp243, tmp244, tmp245, tmp246, tmp247, tmp248, tmp249, tmp250, tmp251, tmp252, tmp253, tmp254, tmp255, tmp256, tmp257, tmp258, tmp259, tmp260, tmp261, tmp262, tmp263, tmp264, tmp265, tmp266, tmp267, tmp268, tmp269, tmp270, tmp271, tmp272, tmp273, tmp274, tmp275, tmp276, tmp277, tmp278, tmp279, tmp280, tmp281, tmp282, tmp283, tmp284, tmp285, tmp286, tmp287, tmp288, tmp289, tmp290, tmp291, tmp292, tmp293, tmp294, tmp295, tmp296, tmp297, tmp298, tmp299, tmp300, tmp301, tmp302, tmp303, tmp304, tmp305, tmp306, tmp307, tmp308, tmp309, tmp310, tmp311, tmp312, tmp313, tmp314, tmp315, tmp316, tmp317, tmp318, tmp319, tmp320, tmp321, tmp322, tmp323, tmp324, tmp325, tmp326, tmp327, tmp328, tmp329, tmp330, tmp331, tmp332, tmp333, tmp334, lambda12;
    tmp = NofibPrelude.nofibStringToList("Why did you repeat yourself?");
    tmp1 = NofibPrelude.nofibStringToList("Do you expect a different answer by repeating yourself?");
    tmp2 = NofibPrelude.nofibStringToList("Come, come, elucidate your thoughts.");
    tmp3 = NofibPrelude.nofibStringToList("Please don't repeat yourself!");
    tmp4 = NofibPrelude.Cons(tmp3, NofibPrelude.Nil);
    tmp5 = NofibPrelude.Cons(tmp2, tmp4);
    tmp6 = NofibPrelude.Cons(tmp1, tmp5);
    tmp7 = NofibPrelude.Cons(tmp, tmp6);
    this.repeatMsgs = tmp7;
    tmp8 = NofibPrelude.nofibStringToList("?Don_t you believe that I can");
    tmp9 = NofibPrelude.nofibStringToList("?Perhaps you would like to be able to");
    tmp10 = NofibPrelude.nofibStringToList("?You want me to be able to");
    tmp11 = NofibPrelude.Cons(tmp10, NofibPrelude.Nil);
    tmp12 = NofibPrelude.Cons(tmp9, tmp11);
    tmp13 = NofibPrelude.Cons(tmp8, tmp12);
    canYou = tmp13;
    tmp14 = NofibPrelude.nofibStringToList("?Perhaps you don_t want to");
    tmp15 = NofibPrelude.nofibStringToList("?Do you want to be able to");
    tmp16 = NofibPrelude.Cons(tmp15, NofibPrelude.Nil);
    tmp17 = NofibPrelude.Cons(tmp14, tmp16);
    canI = tmp17;
    tmp18 = NofibPrelude.nofibStringToList("?What makes you think I am");
    tmp19 = NofibPrelude.nofibStringToList("?Does it please you to believe I am");
    tmp20 = NofibPrelude.nofibStringToList("?Perhaps you would like to be");
    tmp21 = NofibPrelude.nofibStringToList("?Do you sometimes wish you were");
    tmp22 = NofibPrelude.Cons(tmp21, NofibPrelude.Nil);
    tmp23 = NofibPrelude.Cons(tmp20, tmp22);
    tmp24 = NofibPrelude.Cons(tmp19, tmp23);
    tmp25 = NofibPrelude.Cons(tmp18, tmp24);
    youAre = tmp25;
    tmp26 = NofibPrelude.nofibStringToList("?Don_t you really");
    tmp27 = NofibPrelude.nofibStringToList("?Why don_t you");
    tmp28 = NofibPrelude.nofibStringToList("?Do you wish to be able to");
    tmp29 = NofibPrelude.nofibStringToList("Does that trouble you?");
    tmp30 = NofibPrelude.Cons(tmp29, NofibPrelude.Nil);
    tmp31 = NofibPrelude.Cons(tmp28, tmp30);
    tmp32 = NofibPrelude.Cons(tmp27, tmp31);
    tmp33 = NofibPrelude.Cons(tmp26, tmp32);
    iDont = tmp33;
    tmp34 = NofibPrelude.nofibStringToList("Tell me more about such feelings.");
    tmp35 = NofibPrelude.nofibStringToList("?Do you often feel");
    tmp36 = NofibPrelude.nofibStringToList("?Do you enjoy feeling");
    tmp37 = NofibPrelude.Cons(tmp36, NofibPrelude.Nil);
    tmp38 = NofibPrelude.Cons(tmp35, tmp37);
    tmp39 = NofibPrelude.Cons(tmp34, tmp38);
    iFeel = tmp39;
    tmp40 = NofibPrelude.nofibStringToList("?Do you really believe I don't");
    tmp41 = NofibPrelude.nofibStringToList(".Perhaps in good time I will");
    tmp42 = NofibPrelude.nofibStringToList("?Do you want me to");
    tmp43 = NofibPrelude.Cons(tmp42, NofibPrelude.Nil);
    tmp44 = NofibPrelude.Cons(tmp41, tmp43);
    tmp45 = NofibPrelude.Cons(tmp40, tmp44);
    whyDont = tmp45;
    tmp46 = NofibPrelude.nofibStringToList("?Do you think you should be able to");
    tmp47 = NofibPrelude.nofibStringToList("?Why can't you");
    tmp48 = NofibPrelude.Cons(tmp47, NofibPrelude.Nil);
    tmp49 = NofibPrelude.Cons(tmp46, tmp48);
    whyCant = tmp49;
    tmp50 = NofibPrelude.nofibStringToList("?Why are you interested in whether or not I am");
    tmp51 = NofibPrelude.nofibStringToList("?Would you prefer if I were not");
    tmp52 = NofibPrelude.nofibStringToList("?Perhaps in your fantasies I am");
    tmp53 = NofibPrelude.Cons(tmp52, NofibPrelude.Nil);
    tmp54 = NofibPrelude.Cons(tmp51, tmp53);
    tmp55 = NofibPrelude.Cons(tmp50, tmp54);
    areYou = tmp55;
    tmp56 = NofibPrelude.nofibStringToList("?How do you know you can't");
    tmp57 = NofibPrelude.nofibStringToList("Have you tried?");
    tmp58 = NofibPrelude.nofibStringToList("?Perhaps you can now");
    tmp59 = NofibPrelude.Cons(tmp58, NofibPrelude.Nil);
    tmp60 = NofibPrelude.Cons(tmp57, tmp59);
    tmp61 = NofibPrelude.Cons(tmp56, tmp60);
    iCant = tmp61;
    tmp62 = NofibPrelude.nofibStringToList("?Did you come to me because you are");
    tmp63 = NofibPrelude.nofibStringToList("?How long have you been");
    tmp64 = NofibPrelude.nofibStringToList("?Do you believe it is normal to be");
    tmp65 = NofibPrelude.nofibStringToList("?Do you enjoy being");
    tmp66 = NofibPrelude.Cons(tmp65, NofibPrelude.Nil);
    tmp67 = NofibPrelude.Cons(tmp64, tmp66);
    tmp68 = NofibPrelude.Cons(tmp63, tmp67);
    tmp69 = NofibPrelude.Cons(tmp62, tmp68);
    iAm = tmp69;
    tmp70 = NofibPrelude.nofibStringToList("We were discussing you --not me.");
    tmp71 = NofibPrelude.nofibStringToList("?Oh,");
    tmp72 = NofibPrelude.nofibStringToList("You're not really talking about me, are you?");
    tmp73 = NofibPrelude.Cons(tmp72, NofibPrelude.Nil);
    tmp74 = NofibPrelude.Cons(tmp71, tmp73);
    tmp75 = NofibPrelude.Cons(tmp70, tmp74);
    you = tmp75;
    tmp76 = NofibPrelude.nofibStringToList("You seem quite positive.");
    tmp77 = NofibPrelude.nofibStringToList("Are you Sure?");
    tmp78 = NofibPrelude.nofibStringToList("I see.");
    tmp79 = NofibPrelude.nofibStringToList("I understand.");
    tmp80 = NofibPrelude.Cons(tmp79, NofibPrelude.Nil);
    tmp81 = NofibPrelude.Cons(tmp78, tmp80);
    tmp82 = NofibPrelude.Cons(tmp77, tmp81);
    tmp83 = NofibPrelude.Cons(tmp76, tmp82);
    yes = tmp83;
    tmp84 = NofibPrelude.nofibStringToList("Are you saying no just to be negative?");
    tmp85 = NofibPrelude.nofibStringToList("You are being a bit negative.");
    tmp86 = NofibPrelude.nofibStringToList("Why not?");
    tmp87 = NofibPrelude.nofibStringToList("Are you sure?");
    tmp88 = NofibPrelude.nofibStringToList("Why no?");
    tmp89 = NofibPrelude.Cons(tmp88, NofibPrelude.Nil);
    tmp90 = NofibPrelude.Cons(tmp87, tmp89);
    tmp91 = NofibPrelude.Cons(tmp86, tmp90);
    tmp92 = NofibPrelude.Cons(tmp85, tmp91);
    tmp93 = NofibPrelude.Cons(tmp84, tmp92);
    no = tmp93;
    tmp94 = NofibPrelude.nofibStringToList("Do computers worry you?");
    tmp95 = NofibPrelude.nofibStringToList("Are you talking about me in particular?");
    tmp96 = NofibPrelude.nofibStringToList("Are you frightened by machines?");
    tmp97 = NofibPrelude.nofibStringToList("Why do you mention computers?");
    tmp98 = NofibPrelude.nofibStringToList("What do you think machines have to do with your problems?");
    tmp99 = NofibPrelude.nofibStringToList("Don't you think computers can help people?");
    tmp100 = NofibPrelude.nofibStringToList("What is it about machines that worries you?");
    tmp101 = NofibPrelude.Cons(tmp100, NofibPrelude.Nil);
    tmp102 = NofibPrelude.Cons(tmp99, tmp101);
    tmp103 = NofibPrelude.Cons(tmp98, tmp102);
    tmp104 = NofibPrelude.Cons(tmp97, tmp103);
    tmp105 = NofibPrelude.Cons(tmp96, tmp104);
    tmp106 = NofibPrelude.Cons(tmp95, tmp105);
    tmp107 = NofibPrelude.Cons(tmp94, tmp106);
    computer = tmp107;
    tmp108 = NofibPrelude.nofibStringToList("?Why do you want");
    tmp109 = NofibPrelude.nofibStringToList("?What would it mean to you if you got");
    tmp110 = NofibPrelude.nofibStringToList("?Suppose you got");
    tmp111 = NofibPrelude.nofibStringToList("?What if you never got");
    tmp112 = NofibPrelude.nofibStringToList(".I sometimes also want");
    tmp113 = NofibPrelude.Cons(tmp112, NofibPrelude.Nil);
    tmp114 = NofibPrelude.Cons(tmp111, tmp113);
    tmp115 = NofibPrelude.Cons(tmp110, tmp114);
    tmp116 = NofibPrelude.Cons(tmp109, tmp115);
    tmp117 = NofibPrelude.Cons(tmp108, tmp116);
    iWant = tmp117;
    tmp118 = NofibPrelude.nofibStringToList("Why do you ask?");
    tmp119 = NofibPrelude.nofibStringToList("Does that question interest you?");
    tmp120 = NofibPrelude.nofibStringToList("What answer would please you the most?");
    tmp121 = NofibPrelude.nofibStringToList("What do you think?");
    tmp122 = NofibPrelude.nofibStringToList("Are such questions on your mind often?");
    tmp123 = NofibPrelude.nofibStringToList("What is it that you really want to know?");
    tmp124 = NofibPrelude.nofibStringToList("Have you asked anyone else?");
    tmp125 = NofibPrelude.nofibStringToList("Have you asked such questions before?");
    tmp126 = NofibPrelude.nofibStringToList("What else comes to mind when you ask that?");
    tmp127 = NofibPrelude.Cons(tmp126, NofibPrelude.Nil);
    tmp128 = NofibPrelude.Cons(tmp125, tmp127);
    tmp129 = NofibPrelude.Cons(tmp124, tmp128);
    tmp130 = NofibPrelude.Cons(tmp123, tmp129);
    tmp131 = NofibPrelude.Cons(tmp122, tmp130);
    tmp132 = NofibPrelude.Cons(tmp121, tmp131);
    tmp133 = NofibPrelude.Cons(tmp120, tmp132);
    tmp134 = NofibPrelude.Cons(tmp119, tmp133);
    tmp135 = NofibPrelude.Cons(tmp118, tmp134);
    question = tmp135;
    tmp136 = NofibPrelude.nofibStringToList("Names don't interest me.");
    tmp137 = NofibPrelude.nofibStringToList("I don't care about names --please go on.");
    tmp138 = NofibPrelude.Cons(tmp137, NofibPrelude.Nil);
    tmp139 = NofibPrelude.Cons(tmp136, tmp138);
    name = tmp139;
    tmp140 = NofibPrelude.nofibStringToList("Is that the real reason?");
    tmp141 = NofibPrelude.nofibStringToList("Don't any other reasons come to mind?");
    tmp142 = NofibPrelude.nofibStringToList("Does that reason explain anything else?");
    tmp143 = NofibPrelude.nofibStringToList("What other reasons might there be?");
    tmp144 = NofibPrelude.Cons(tmp143, NofibPrelude.Nil);
    tmp145 = NofibPrelude.Cons(tmp142, tmp144);
    tmp146 = NofibPrelude.Cons(tmp141, tmp145);
    tmp147 = NofibPrelude.Cons(tmp140, tmp146);
    because = tmp147;
    tmp148 = NofibPrelude.nofibStringToList("Please don't apologise!");
    tmp149 = NofibPrelude.nofibStringToList("Apologies are not necessary.");
    tmp150 = NofibPrelude.nofibStringToList("What feelings do you have when you apologise?");
    tmp151 = NofibPrelude.nofibStringToList("Don't be so defensive!");
    tmp152 = NofibPrelude.Cons(tmp151, NofibPrelude.Nil);
    tmp153 = NofibPrelude.Cons(tmp150, tmp152);
    tmp154 = NofibPrelude.Cons(tmp149, tmp153);
    tmp155 = NofibPrelude.Cons(tmp148, tmp154);
    sorry = tmp155;
    tmp156 = NofibPrelude.nofibStringToList("What does that dream suggest to you?");
    tmp157 = NofibPrelude.nofibStringToList("Do you dream often?");
    tmp158 = NofibPrelude.nofibStringToList("What persons appear in your dreams?");
    tmp159 = NofibPrelude.nofibStringToList("Are you disturbed by your dreams?");
    tmp160 = NofibPrelude.Cons(tmp159, NofibPrelude.Nil);
    tmp161 = NofibPrelude.Cons(tmp158, tmp160);
    tmp162 = NofibPrelude.Cons(tmp157, tmp161);
    tmp163 = NofibPrelude.Cons(tmp156, tmp162);
    dream = tmp163;
    tmp164 = NofibPrelude.nofibStringToList("How do you...please state your problem.");
    tmp165 = NofibPrelude.Cons(tmp164, NofibPrelude.Nil);
    hello = tmp165;
    tmp166 = NofibPrelude.nofibStringToList("You don't seem quite certain.");
    tmp167 = NofibPrelude.nofibStringToList("Why the uncertain tone?");
    tmp168 = NofibPrelude.nofibStringToList("Can't you be more positive?");
    tmp169 = NofibPrelude.nofibStringToList("You aren't sure?");
    tmp170 = NofibPrelude.nofibStringToList("Don't you know?");
    tmp171 = NofibPrelude.Cons(tmp170, NofibPrelude.Nil);
    tmp172 = NofibPrelude.Cons(tmp169, tmp171);
    tmp173 = NofibPrelude.Cons(tmp168, tmp172);
    tmp174 = NofibPrelude.Cons(tmp167, tmp173);
    tmp175 = NofibPrelude.Cons(tmp166, tmp174);
    maybe1 = tmp175;
    tmp176 = NofibPrelude.nofibStringToList("?Why are you concerned about my");
    tmp177 = NofibPrelude.nofibStringToList("?What about your own");
    tmp178 = NofibPrelude.Cons(tmp177, NofibPrelude.Nil);
    tmp179 = NofibPrelude.Cons(tmp176, tmp178);
    your = tmp179;
    tmp180 = NofibPrelude.nofibStringToList("Can you think of a specific example?");
    tmp181 = NofibPrelude.nofibStringToList("When?");
    tmp182 = NofibPrelude.nofibStringToList("What are you thinking of?");
    tmp183 = NofibPrelude.nofibStringToList("Really, always?");
    tmp184 = NofibPrelude.Cons(tmp183, NofibPrelude.Nil);
    tmp185 = NofibPrelude.Cons(tmp182, tmp184);
    tmp186 = NofibPrelude.Cons(tmp181, tmp185);
    tmp187 = NofibPrelude.Cons(tmp180, tmp186);
    always = tmp187;
    tmp188 = NofibPrelude.nofibStringToList("Do you really think so?");
    tmp189 = NofibPrelude.nofibStringToList("?But you are not sure you");
    tmp190 = NofibPrelude.nofibStringToList("?Do you doubt you");
    tmp191 = NofibPrelude.Cons(tmp190, NofibPrelude.Nil);
    tmp192 = NofibPrelude.Cons(tmp189, tmp191);
    tmp193 = NofibPrelude.Cons(tmp188, tmp192);
    think = tmp193;
    tmp194 = NofibPrelude.nofibStringToList("In what way?");
    tmp195 = NofibPrelude.nofibStringToList("What resemblence do you see?");
    tmp196 = NofibPrelude.nofibStringToList("What does the similarity suggest to you?");
    tmp197 = NofibPrelude.nofibStringToList("What other connections do you see?");
    tmp198 = NofibPrelude.nofibStringToList("Cound there really be some connection?");
    tmp199 = NofibPrelude.nofibStringToList("How?");
    tmp200 = NofibPrelude.Cons(tmp199, NofibPrelude.Nil);
    tmp201 = NofibPrelude.Cons(tmp198, tmp200);
    tmp202 = NofibPrelude.Cons(tmp197, tmp201);
    tmp203 = NofibPrelude.Cons(tmp196, tmp202);
    tmp204 = NofibPrelude.Cons(tmp195, tmp203);
    tmp205 = NofibPrelude.Cons(tmp194, tmp204);
    alike = tmp205;
    tmp206 = NofibPrelude.nofibStringToList("Why do you bring up the topic of friends?");
    tmp207 = NofibPrelude.nofibStringToList("Do your friends worry you?");
    tmp208 = NofibPrelude.nofibStringToList("Do your friends pick on you?");
    tmp209 = NofibPrelude.nofibStringToList("Are you sure you have any friends?");
    tmp210 = NofibPrelude.nofibStringToList("Do you impose on your friends?");
    tmp211 = NofibPrelude.nofibStringToList("Perhaps your love for friends worries you.");
    tmp212 = NofibPrelude.Cons(tmp211, NofibPrelude.Nil);
    tmp213 = NofibPrelude.Cons(tmp210, tmp212);
    tmp214 = NofibPrelude.Cons(tmp209, tmp213);
    tmp215 = NofibPrelude.Cons(tmp208, tmp214);
    tmp216 = NofibPrelude.Cons(tmp207, tmp215);
    tmp217 = NofibPrelude.Cons(tmp206, tmp216);
    friend = tmp217;
    tmp218 = NofibPrelude.nofibStringToList("I'm not sure I understand you fully.");
    tmp219 = NofibPrelude.nofibStringToList("What does that suggest to you?");
    tmp220 = NofibPrelude.nofibStringToList("I see.");
    tmp221 = NofibPrelude.nofibStringToList("Can you elaborate on that?");
    tmp222 = NofibPrelude.nofibStringToList("Say, do you have any psychological problems?");
    tmp223 = NofibPrelude.Cons(tmp222, NofibPrelude.Nil);
    tmp224 = NofibPrelude.Cons(tmp221, tmp223);
    tmp225 = NofibPrelude.Cons(tmp220, tmp224);
    tmp226 = NofibPrelude.Cons(tmp219, tmp225);
    tmp227 = NofibPrelude.Cons(tmp218, tmp226);
    nokeyMsgs = tmp227;
    tmp228 = NofibPrelude.nofibStringToList("CAN YOU");
    tmp229 = NofibPrelude.nofibStringToList("CAN I");
    tmp230 = NofibPrelude.nofibStringToList("YOU ARE");
    tmp231 = NofibPrelude.nofibStringToList("YOU'RE");
    tmp232 = NofibPrelude.nofibStringToList("I DON'T");
    tmp233 = NofibPrelude.nofibStringToList("I FEEL");
    tmp234 = NofibPrelude.nofibStringToList("WHY DON'T YOU");
    tmp235 = NofibPrelude.nofibStringToList("WHY CAN'T I");
    tmp236 = NofibPrelude.nofibStringToList("ARE YOU");
    tmp237 = NofibPrelude.nofibStringToList("I CAN'T");
    tmp238 = NofibPrelude.nofibStringToList("I AM");
    tmp239 = NofibPrelude.nofibStringToList("I'M");
    tmp240 = NofibPrelude.nofibStringToList("YOU");
    tmp241 = NofibPrelude.nofibStringToList("YES");
    tmp242 = NofibPrelude.nofibStringToList("NO");
    tmp243 = NofibPrelude.nofibStringToList("COMPUTER");
    tmp244 = NofibPrelude.nofibStringToList("COMPUTERS");
    tmp245 = NofibPrelude.nofibStringToList("I WANT");
    tmp246 = NofibPrelude.nofibStringToList("WHAT");
    tmp247 = NofibPrelude.nofibStringToList("HOW");
    tmp248 = NofibPrelude.nofibStringToList("WHO");
    tmp249 = NofibPrelude.nofibStringToList("WHERE");
    tmp250 = NofibPrelude.nofibStringToList("WHEN");
    tmp251 = NofibPrelude.nofibStringToList("NAME");
    tmp252 = NofibPrelude.nofibStringToList("WHY");
    tmp253 = NofibPrelude.nofibStringToList("CAUSE");
    tmp254 = NofibPrelude.nofibStringToList("BECAUSE");
    tmp255 = NofibPrelude.nofibStringToList("DREAM");
    tmp256 = NofibPrelude.nofibStringToList("SORRY");
    tmp257 = NofibPrelude.nofibStringToList("HI");
    tmp258 = NofibPrelude.nofibStringToList("DREAMS");
    tmp259 = NofibPrelude.nofibStringToList("MAYBE");
    tmp260 = NofibPrelude.nofibStringToList("HELLO");
    tmp261 = NofibPrelude.nofibStringToList("ALWAYS");
    tmp262 = NofibPrelude.nofibStringToList("YOUR");
    tmp263 = NofibPrelude.nofibStringToList("ALIKE");
    tmp264 = NofibPrelude.nofibStringToList("THINK");
    tmp265 = NofibPrelude.nofibStringToList("FRIENDS");
    tmp266 = NofibPrelude.nofibStringToList("FRIEND");
    tmp267 = NofibPrelude.Cons([
      NofibPrelude.Nil,
      nokeyMsgs
    ], NofibPrelude.Nil);
    tmp268 = NofibPrelude.Cons([
      tmp266,
      friend
    ], tmp267);
    tmp269 = NofibPrelude.Cons([
      tmp265,
      friend
    ], tmp268);
    tmp270 = NofibPrelude.Cons([
      tmp264,
      think
    ], tmp269);
    tmp271 = NofibPrelude.Cons([
      tmp263,
      alike
    ], tmp270);
    tmp272 = NofibPrelude.Cons([
      tmp262,
      your
    ], tmp271);
    tmp273 = NofibPrelude.Cons([
      tmp261,
      always
    ], tmp272);
    tmp274 = NofibPrelude.Cons([
      tmp260,
      hello
    ], tmp273);
    tmp275 = NofibPrelude.Cons([
      tmp259,
      maybe1
    ], tmp274);
    tmp276 = NofibPrelude.Cons([
      tmp258,
      dream
    ], tmp275);
    tmp277 = NofibPrelude.Cons([
      tmp257,
      hello
    ], tmp276);
    tmp278 = NofibPrelude.Cons([
      tmp256,
      sorry
    ], tmp277);
    tmp279 = NofibPrelude.Cons([
      tmp255,
      dream
    ], tmp278);
    tmp280 = NofibPrelude.Cons([
      tmp254,
      because
    ], tmp279);
    tmp281 = NofibPrelude.Cons([
      tmp253,
      because
    ], tmp280);
    tmp282 = NofibPrelude.Cons([
      tmp252,
      question
    ], tmp281);
    tmp283 = NofibPrelude.Cons([
      tmp251,
      name
    ], tmp282);
    tmp284 = NofibPrelude.Cons([
      tmp250,
      question
    ], tmp283);
    tmp285 = NofibPrelude.Cons([
      tmp249,
      question
    ], tmp284);
    tmp286 = NofibPrelude.Cons([
      tmp248,
      question
    ], tmp285);
    tmp287 = NofibPrelude.Cons([
      tmp247,
      question
    ], tmp286);
    tmp288 = NofibPrelude.Cons([
      tmp246,
      question
    ], tmp287);
    tmp289 = NofibPrelude.Cons([
      tmp245,
      iWant
    ], tmp288);
    tmp290 = NofibPrelude.Cons([
      tmp244,
      computer
    ], tmp289);
    tmp291 = NofibPrelude.Cons([
      tmp243,
      computer
    ], tmp290);
    tmp292 = NofibPrelude.Cons([
      tmp242,
      no
    ], tmp291);
    tmp293 = NofibPrelude.Cons([
      tmp241,
      yes
    ], tmp292);
    tmp294 = NofibPrelude.Cons([
      tmp240,
      you
    ], tmp293);
    tmp295 = NofibPrelude.Cons([
      tmp239,
      iAm
    ], tmp294);
    tmp296 = NofibPrelude.Cons([
      tmp238,
      iAm
    ], tmp295);
    tmp297 = NofibPrelude.Cons([
      tmp237,
      iCant
    ], tmp296);
    tmp298 = NofibPrelude.Cons([
      tmp236,
      areYou
    ], tmp297);
    tmp299 = NofibPrelude.Cons([
      tmp235,
      whyCant
    ], tmp298);
    tmp300 = NofibPrelude.Cons([
      tmp234,
      whyDont
    ], tmp299);
    tmp301 = NofibPrelude.Cons([
      tmp233,
      iFeel
    ], tmp300);
    tmp302 = NofibPrelude.Cons([
      tmp232,
      iDont
    ], tmp301);
    tmp303 = NofibPrelude.Cons([
      tmp231,
      youAre
    ], tmp302);
    tmp304 = NofibPrelude.Cons([
      tmp230,
      youAre
    ], tmp303);
    tmp305 = NofibPrelude.Cons([
      tmp229,
      canI
    ], tmp304);
    tmp306 = NofibPrelude.Cons([
      tmp228,
      canYou
    ], tmp305);
    this.respMsgs = tmp306;
    lscomp1 = function lscomp(ls) {
      let param0, param1, first1, first0, k, rs, t, tmp335, tmp336, tmp337;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        if (globalThis.Array.isArray(param0) && param0.length === 2) {
          first0 = param0[0];
          first1 = param0[1];
          k = first0;
          rs = first1;
          t = param1;
          tmp335 = eliza.words(k);
          tmp336 = eliza.cycle(rs);
          tmp337 = lscomp1(t);
          return NofibPrelude.Cons([
            tmp335,
            tmp336
          ], tmp337)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp307 = lscomp1(eliza.respMsgs);
    tmp308 = eliza.cycle(eliza.repeatMsgs);
    this.initial = [
      tmp307,
      tmp308
    ];
    prepare = function prepare(ls) {
      let tmp335;
      tmp335 = lambda10;
      return NofibPrelude.map(tmp335, ls)
    };
    lscomp2 = function lscomp(ls) {
      let param0, param1, first1, first0, x, y, t, tmp335, tmp336, tmp337;
      if (ls instanceof NofibPrelude.Nil.class) {
        return NofibPrelude.Nil
      } else if (ls instanceof NofibPrelude.Cons.class) {
        param0 = ls.head;
        param1 = ls.tail;
        if (globalThis.Array.isArray(param0) && param0.length === 2) {
          first0 = param0[0];
          first1 = param0[1];
          x = first0;
          y = first1;
          t = param1;
          tmp335 = NofibPrelude.Cons([
            y,
            x
          ], NofibPrelude.Nil);
          tmp336 = NofibPrelude.Cons([
            x,
            y
          ], tmp335);
          tmp337 = lscomp2(t);
          return NofibPrelude.Cons(tmp336, tmp337)
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    };
    tmp309 = NofibPrelude.nofibStringToList("me");
    tmp310 = NofibPrelude.nofibStringToList("you");
    tmp311 = NofibPrelude.Cons([
      tmp309,
      tmp310
    ], NofibPrelude.Nil);
    oneways = tmp311;
    tmp312 = NofibPrelude.nofibStringToList("are");
    tmp313 = NofibPrelude.nofibStringToList("am");
    tmp314 = NofibPrelude.nofibStringToList("we're");
    tmp315 = NofibPrelude.nofibStringToList("was");
    tmp316 = NofibPrelude.nofibStringToList("you");
    tmp317 = NofibPrelude.nofibStringToList("I");
    tmp318 = NofibPrelude.nofibStringToList("your");
    tmp319 = NofibPrelude.nofibStringToList("my");
    tmp320 = NofibPrelude.nofibStringToList("I've");
    tmp321 = NofibPrelude.nofibStringToList("you've");
    tmp322 = NofibPrelude.nofibStringToList("I'm");
    tmp323 = NofibPrelude.nofibStringToList("you're");
    tmp324 = NofibPrelude.Cons([
      tmp322,
      tmp323
    ], NofibPrelude.Nil);
    tmp325 = NofibPrelude.Cons([
      tmp320,
      tmp321
    ], tmp324);
    tmp326 = NofibPrelude.Cons([
      tmp318,
      tmp319
    ], tmp325);
    tmp327 = NofibPrelude.Cons([
      tmp316,
      tmp317
    ], tmp326);
    tmp328 = NofibPrelude.Cons([
      tmp314,
      tmp315
    ], tmp327);
    tmp329 = NofibPrelude.Cons([
      tmp312,
      tmp313
    ], tmp328);
    bothways = tmp329;
    tmp330 = lscomp2(bothways);
    tmp331 = NofibPrelude.concat(tmp330);
    tmp332 = NofibPrelude.append(oneways, tmp331);
    tmp333 = prepare(tmp332);
    this.conjugates = tmp333;
    lambda12 = (undefined, function () {
      let tmp335, tmp336;
      tmp335 = eliza.testEliza_nofib(20);
      tmp336 = NofibPrelude.map(lambda11, tmp335);
      return runtime.safeCall(tmp336.toString())
    });
    tmp334 = lambda12;
    BenchmarkPrelude.benchmark(tmp334)
  }
  static toUpper(c) {
    return runtime.safeCall(c.toUpperCase())
  } 
  static lz_map(f, ls) {
    let tmp;
    tmp = runtime.safeCall(lambda(f, ls));
    return NofibPrelude.lazy(tmp)
  } 
  static append_lz(xs, ys) {
    let param0, param1, h, t, lambda$this;
    if (xs instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.force(ys)
    } else if (xs instanceof NofibPrelude.Cons.class) {
      param0 = xs.head;
      param1 = xs.tail;
      h = param0;
      t = param1;
      lambda$this = runtime.safeCall(lambda1(ys, h, t));
      return NofibPrelude.lazy(lambda$this)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static cycle(xs1) {
    let tmp, lambda$this;
    lambda$this = runtime.safeCall(lambda2(xs1));
    tmp = NofibPrelude.lazy(lambda$this);
    return eliza.append_lz(xs1, tmp)
  } 
  static isSpace(c1) {
    return c1 === " "
  } 
  static words(s) {
    let scrut, param0, param1, h, t, scrut1, first1, first0, w, s_, tmp, tmp1;
    scrut = NofibPrelude.dropWhile(eliza.isSpace, s);
    if (scrut instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (scrut instanceof NofibPrelude.Cons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      h = param0;
      t = param1;
      tmp = NofibPrelude.Cons(h, t);
      scrut1 = NofibPrelude.break_(eliza.isSpace, tmp);
      if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
        first0 = scrut1[0];
        first1 = scrut1[1];
        w = first0;
        s_ = first1;
        tmp1 = eliza.words(s_);
        return NofibPrelude.Cons(w, tmp1)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static unwords(ws) {
    let param0, param1, w, ws1, tmp;
    if (ws instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ws instanceof NofibPrelude.Cons.class) {
      param0 = ws.head;
      param1 = ws.tail;
      w = param0;
      ws1 = param1;
      tmp = go(ws1);
      return NofibPrelude.append(w, tmp)
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static null_lz(ls1) {
    let scrut, param0, param1, h, t;
    scrut = NofibPrelude.force(ls1);
    if (scrut instanceof NofibPrelude.LzNil.class) {
      return true
    } else if (scrut instanceof NofibPrelude.LzCons.class) {
      param0 = scrut.head;
      param1 = scrut.tail;
      h = param0;
      t = param1;
      return false
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static trim(ls2) {
    let tmp;
    tmp = NofibPrelude.dropWhile(lambda3, ls2);
    return NofibPrelude.foldr(cons, NofibPrelude.Nil, tmp)
  } 
  static repeated(kt_rp) {
    let first1, first0, kt, param0, param1, r, rp;
    if (globalThis.Array.isArray(kt_rp) && kt_rp.length === 2) {
      first0 = kt_rp[0];
      first1 = kt_rp[1];
      kt = first0;
      if (first1 instanceof NofibPrelude.Cons.class) {
        param0 = first1.head;
        param1 = first1.tail;
        r = param0;
        rp = param1;
        return [
          r,
          [
            kt,
            rp
          ]
        ]
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static newKeyTab(kt_, kt_rp1) {
    let first1, first0, kt, rp;
    if (globalThis.Array.isArray(kt_rp1) && kt_rp1.length === 2) {
      first0 = kt_rp1[0];
      first1 = kt_rp1[1];
      kt = first0;
      rp = first1;
      return [
        kt_,
        rp
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static keyTabOf(kt_rp2) {
    let first1, first0, kt, rp;
    if (globalThis.Array.isArray(kt_rp2) && kt_rp2.length === 2) {
      first0 = kt_rp2[0];
      first1 = kt_rp2[1];
      kt = first0;
      rp = first1;
      return kt
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static makeResponse(cs, us) {
    let param0, param1, cs_, cs_1, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
    if (cs instanceof NofibPrelude.Cons.class) {
      param0 = cs.head;
      param1 = cs.tail;
      if (param0 === "?") {
        cs_1 = param1;
        tmp = NofibPrelude.nofibStringToList(" ");
        tmp1 = NofibPrelude.nofibStringToList("?");
        tmp2 = NofibPrelude.append(us, tmp1);
        tmp3 = NofibPrelude.append(tmp, tmp2);
        return NofibPrelude.append(cs_1, tmp3)
      } else if (param0 === ".") {
        cs_ = param1;
        tmp4 = NofibPrelude.nofibStringToList(" ");
        tmp5 = NofibPrelude.nofibStringToList(".");
        tmp6 = NofibPrelude.append(us, tmp5);
        tmp7 = NofibPrelude.append(tmp4, tmp6);
        return NofibPrelude.append(cs_, tmp7)
      } else {
        return cs
      }
    } else {
      return cs
    }
  } 
  static prefix(xxs, yys) {
    let param0, param1, x, xs2, scrut, param01, param11, y, ys1, tmp, tmp1;
    if (xxs instanceof NofibPrelude.Nil.class) {
      return true
    } else if (xxs instanceof NofibPrelude.Cons.class) {
      param0 = xxs.head;
      param1 = xxs.tail;
      x = param0;
      xs2 = param1;
      scrut = NofibPrelude.force(yys);
      if (scrut instanceof NofibPrelude.LzNil.class) {
        return false
      } else if (scrut instanceof NofibPrelude.LzCons.class) {
        param01 = scrut.head;
        param11 = scrut.tail;
        y = param01;
        ys1 = param11;
        tmp = NofibPrelude.listEq(x, y);
        tmp1 = eliza.prefix(xs2, ys1);
        return tmp && tmp1
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static tails(xs2) {
    let tmp;
    tmp = runtime.safeCall(lambda4(xs2));
    return NofibPrelude.lazy(tmp)
  } 
  static ucase(ls3) {
    return NofibPrelude.map(eliza.toUpper, ls3)
  } 
  static conjug(d, w) {
    let tmp, tmp1, tmp2;
    tmp = maybe(d, w);
    tmp1 = NofibPrelude.map(conj, tmp);
    tmp2 = trailingI(tmp1);
    return eliza.unwords(tmp2)
  } 
  static replies(key, l) {
    let tmp, tmp1, tmp2, lambda$this;
    tmp = runtime.safeCall(lambda5(key, l));
    tmp1 = eliza.tails(l);
    lambda$this = runtime.safeCall(lambda6(key));
    tmp2 = NofibPrelude.filter_lz(lambda$this, tmp1);
    return NofibPrelude.map_lz(tmp, tmp2)
  } 
  static answer(st, l1) {
    let scrut, first1, first0, response, kt, tmp, tmp1;
    tmp = eliza.keyTabOf(st);
    scrut = ans(tmp, l1);
    if (globalThis.Array.isArray(scrut) && scrut.length === 2) {
      first0 = scrut[0];
      first1 = scrut[1];
      response = first0;
      kt = first1;
      tmp1 = eliza.newKeyTab(kt, st);
      return [
        response,
        tmp1
      ]
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static session(rs, prev, ls4) {
    let param0, param1, l2, ls5, scrut, scrut1, first1, first0, response, rs_, tmp, tmp1, tmp2, tmp3;
    if (ls4 instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls4 instanceof NofibPrelude.Cons.class) {
      param0 = ls4.head;
      param1 = ls4.tail;
      l2 = param0;
      ls5 = param1;
      scrut = NofibPrelude.listEqBy(NofibPrelude.listEq, prev, l2);
      if (scrut === true) {
        tmp = eliza.repeated(rs);
      } else {
        tmp = eliza.answer(rs, l2);
      }
      scrut1 = tmp;
      if (globalThis.Array.isArray(scrut1) && scrut1.length === 2) {
        first0 = scrut1[0];
        first1 = scrut1[1];
        response = first0;
        rs_ = first1;
        tmp1 = NofibPrelude.nofibStringToList("\n\n");
        tmp2 = eliza.session(rs_, l2, ls5);
        tmp3 = NofibPrelude.append(tmp1, tmp2);
        return NofibPrelude.append(response, tmp3)
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  } 
  static testEliza_nofib(n) {
    let input, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29;
    tmp = NofibPrelude.nofibStringToList("Are we alone?");
    tmp1 = NofibPrelude.nofibStringToList("That the Roswell event was actually an alien encounter. Do you agreed?");
    tmp2 = NofibPrelude.nofibStringToList("But why not talk about you, its more fun.");
    tmp3 = NofibPrelude.nofibStringToList("I dont ask, you do");
    tmp4 = NofibPrelude.nofibStringToList("do ray me");
    tmp5 = NofibPrelude.nofibStringToList("Nop, thats because your a computer");
    tmp6 = NofibPrelude.nofibStringToList("you dont");
    tmp7 = NofibPrelude.nofibStringToList("Oh, a paranoid computer, ehh?");
    tmp8 = NofibPrelude.nofibStringToList("Tell me about *your* mother");
    tmp9 = NofibPrelude.nofibStringToList("No, what what was she like?");
    tmp10 = NofibPrelude.nofibStringToList("I'm asking questions, not you");
    tmp11 = NofibPrelude.nofibStringToList("no");
    tmp12 = NofibPrelude.nofibStringToList("yes");
    tmp13 = NofibPrelude.nofibStringToList("but I'm not");
    tmp14 = NofibPrelude.Cons(tmp13, NofibPrelude.Nil);
    tmp15 = NofibPrelude.Cons(tmp12, tmp14);
    tmp16 = NofibPrelude.Cons(tmp11, tmp15);
    tmp17 = NofibPrelude.Cons(tmp10, tmp16);
    tmp18 = NofibPrelude.Cons(tmp9, tmp17);
    tmp19 = NofibPrelude.Cons(tmp8, tmp18);
    tmp20 = NofibPrelude.Cons(tmp7, tmp19);
    tmp21 = NofibPrelude.Cons(tmp6, tmp20);
    tmp22 = NofibPrelude.Cons(tmp5, tmp21);
    tmp23 = NofibPrelude.Cons(tmp4, tmp22);
    tmp24 = NofibPrelude.Cons(tmp3, tmp23);
    tmp25 = NofibPrelude.Cons(tmp2, tmp24);
    tmp26 = NofibPrelude.Cons(tmp1, tmp25);
    tmp27 = NofibPrelude.Cons(tmp, tmp26);
    input = tmp27;
    tmp28 = runtime.safeCall(lambda7(input));
    tmp29 = NofibPrelude.enumFromTo(1, n);
    return NofibPrelude.map(tmp28, tmp29)
  }
  static toString() { return "eliza"; }
};
let eliza = eliza1; export default eliza;
