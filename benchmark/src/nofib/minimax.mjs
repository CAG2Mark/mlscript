import runtime from "./../../../hkmc2/shared/src/test/mlscript-compile/Runtime.mjs";
import NofibPrelude from "./../precompiled/NofibPrelude.mjs";
import BenchmarkPrelude from "./../precompiled/BenchmarkPrelude.mjs";
let scorePiece, max_, opposite, alternate, showPiece, min_, searchTree, showBoard, O1, Piece1, mise, bestMove, X1, placePiece, eqPiece, showEvaluation, andd, empty, Evaluation1, insert, best, eval_, cropTree, XWin1, score, fullBoard, static_, prog, newPositions, empty_, prune, OWin1, Empty1, Score1, Branch1, evaluationEq, showMove, repTree, map2, mapTree, showRow, interpret, win1, win2, win3, win4, win5, win6, win7, win8, wins, initialBoard, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14, tmp15, tmp16, tmp17, tmp18, tmp19, tmp20, tmp21, tmp22, tmp23, tmp24, tmp25, tmp26, tmp27, tmp28, tmp29, tmp30, tmp31, tmp32, tmp33, tmp34, tmp35, tmp36, tmp37, tmp38, tmp39, tmp40, tmp41, tmp42, tmp43, tmp44, tmp45, tmp46, tmp47, tmp48, tmp49, tmp50, tmp51, tmp52, tmp53, tmp54, tmp55, tmp56, tmp57, tmp58, tmp59, tmp60, tmp61, tmp62, tmp63, tmp64, tmp65, tmp66, tmp67, tmp68, tmp69, tmp70, tmp71, tmp72, tmp73, tmp74, tmp75, tmp76, tmp77, tmp78, tmp79, tmp80, tmp81, tmp82, tmp83, tmp84, tmp85, tmp86, tmp87, tmp88, tmp89, tmp90, tmp91, tmp92, tmp93, tmp94, tmp95, tmp96, tmp97, tmp98, tmp99, tmp100, tmp101, tmp102, tmp103, tmp104, tmp105, tmp106, lambda;
andd = function andd(ls) {
  let param0, param1, b, bs, tmp107;
  if (ls instanceof NofibPrelude.Nil.class) {
    return true
  } else if (ls instanceof NofibPrelude.Cons.class) {
    param0 = ls.head;
    param1 = ls.tail;
    b = param0;
    bs = param1;
    tmp107 = andd(bs);
    return b && tmp107
  } else {
    throw new globalThis.Error("match error");
  }
};
eqPiece = function eqPiece(p1, p2) {
  if (p1 instanceof X1.class) {
    if (p2 instanceof X1.class) {
      return true
    } else {
      return false
    }
  } else if (p1 instanceof O1.class) {
    if (p2 instanceof O1.class) {
      return true
    } else {
      return false
    }
  } else if (p1 instanceof Empty1.class) {
    if (p2 instanceof Empty1.class) {
      return true
    } else {
      return false
    }
  } else {
    return false
  }
};
evaluationEq = function evaluationEq(x, y) {
  let param0, i, param01, j, scrut;
  if (x instanceof XWin1.class) {
    if (y instanceof XWin1.class) {
      return true
    } else {
      return false
    }
  } else if (x instanceof OWin1.class) {
    if (y instanceof OWin1.class) {
      return true
    } else {
      return false
    }
  } else if (x instanceof Score1.class) {
    param0 = x.i;
    i = param0;
    if (y instanceof Score1.class) {
      param01 = y.i;
      j = param01;
      scrut = i === j;
      if (scrut === true) {
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
};
showEvaluation = function showEvaluation(e) {
  let param0, i, tmp107, tmp108, tmp109;
  if (e instanceof XWin1.class) {
    return NofibPrelude.nofibStringToList("XWin")
  } else if (e instanceof OWin1.class) {
    return NofibPrelude.nofibStringToList("OWin")
  } else if (e instanceof Score1.class) {
    param0 = e.i;
    i = param0;
    tmp107 = NofibPrelude.nofibStringToList("Score ");
    tmp108 = NofibPrelude.stringOfInt(i);
    tmp109 = NofibPrelude.nofibStringToList(tmp108);
    return NofibPrelude.append(tmp107, tmp109)
  } else {
    throw new globalThis.Error("match error");
  }
};
showPiece = function showPiece(p) {
  if (p instanceof X1.class) {
    return NofibPrelude.nofibStringToList("X")
  } else if (p instanceof O1.class) {
    return NofibPrelude.nofibStringToList("O")
  } else if (p instanceof Empty1.class) {
    return NofibPrelude.nofibStringToList(" ")
  } else {
    throw new globalThis.Error("match error");
  }
};
showRow = function showRow(ps) {
  let param0, param1, p1, param01, param11, p2, param02, param12, p3, tmp107, tmp108, tmp109, tmp110, tmp111, tmp112, tmp113, tmp114;
  if (ps instanceof NofibPrelude.Cons.class) {
    param0 = ps.head;
    param1 = ps.tail;
    p1 = param0;
    if (param1 instanceof NofibPrelude.Cons.class) {
      param01 = param1.head;
      param11 = param1.tail;
      p2 = param01;
      if (param11 instanceof NofibPrelude.Cons.class) {
        param02 = param11.head;
        param12 = param11.tail;
        p3 = param02;
        if (param12 instanceof NofibPrelude.Nil.class) {
          tmp107 = showPiece(p1);
          tmp108 = NofibPrelude.nofibStringToList("|");
          tmp109 = showPiece(p2);
          tmp110 = NofibPrelude.nofibStringToList("|");
          tmp111 = showPiece(p3);
          tmp112 = NofibPrelude.append(tmp110, tmp111);
          tmp113 = NofibPrelude.append(tmp109, tmp112);
          tmp114 = NofibPrelude.append(tmp108, tmp113);
          return NofibPrelude.append(tmp107, tmp114)
        } else {
          throw new globalThis.Error("match error");
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
showBoard = function showBoard(rs) {
  let param0, param1, r1, param01, param11, r2, param02, param12, r3, tmp107, tmp108, tmp109, tmp110, tmp111, tmp112, tmp113, tmp114, tmp115, tmp116;
  if (rs instanceof NofibPrelude.Cons.class) {
    param0 = rs.head;
    param1 = rs.tail;
    r1 = param0;
    if (param1 instanceof NofibPrelude.Cons.class) {
      param01 = param1.head;
      param11 = param1.tail;
      r2 = param01;
      if (param11 instanceof NofibPrelude.Cons.class) {
        param02 = param11.head;
        param12 = param11.tail;
        r3 = param02;
        if (param12 instanceof NofibPrelude.Nil.class) {
          tmp107 = showRow(r1);
          tmp108 = NofibPrelude.nofibStringToList("\n------\n");
          tmp109 = showRow(r2);
          tmp110 = NofibPrelude.nofibStringToList("\n------\n");
          tmp111 = showRow(r3);
          tmp112 = NofibPrelude.nofibStringToList("\n\n");
          tmp113 = NofibPrelude.append(tmp111, tmp112);
          tmp114 = NofibPrelude.append(tmp110, tmp113);
          tmp115 = NofibPrelude.append(tmp109, tmp114);
          tmp116 = NofibPrelude.append(tmp108, tmp115);
          return NofibPrelude.append(tmp107, tmp116)
        } else {
          throw new globalThis.Error("match error");
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
insert = function insert(p, ps, i) {
  let param0, param1, p1, param01, param11, p2, param02, param12, p3, scrut, scrut1, scrut2, tmp107, tmp108, tmp109, tmp110, tmp111, tmp112;
  if (ps instanceof NofibPrelude.Cons.class) {
    param0 = ps.head;
    param1 = ps.tail;
    p1 = param0;
    if (param1 instanceof NofibPrelude.Cons.class) {
      param01 = param1.head;
      param11 = param1.tail;
      p2 = param01;
      if (param11 instanceof NofibPrelude.Cons.class) {
        param02 = param11.head;
        param12 = param11.tail;
        p3 = param02;
        if (param12 instanceof NofibPrelude.Nil.class) {
          scrut2 = i === 1;
          if (scrut2 === true) {
            tmp107 = NofibPrelude.Cons(p3, NofibPrelude.Nil);
            tmp108 = NofibPrelude.Cons(p2, tmp107);
            return NofibPrelude.Cons(p, tmp108)
          } else {
            scrut1 = i === 2;
            if (scrut1 === true) {
              tmp109 = NofibPrelude.Cons(p3, NofibPrelude.Nil);
              tmp110 = NofibPrelude.Cons(p, tmp109);
              return NofibPrelude.Cons(p1, tmp110)
            } else {
              scrut = i === 3;
              if (scrut === true) {
                tmp111 = NofibPrelude.Cons(p, NofibPrelude.Nil);
                tmp112 = NofibPrelude.Cons(p2, tmp111);
                return NofibPrelude.Cons(p1, tmp112)
              } else {
                throw new globalThis.Error("match error");
              }
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
  } else {
    throw new globalThis.Error("match error");
  }
};
empty_ = function empty_(x, r) {
  let scrut, param0, param1, param01, param11, param02, param12, scrut1, scrut2;
  scrut2 = x === 1;
  if (scrut2 === true) {
    if (r instanceof NofibPrelude.Cons.class) {
      param0 = r.head;
      param1 = r.tail;
      if (param0 instanceof Empty1.class) {
        if (param1 instanceof NofibPrelude.Cons.class) {
          param01 = param1.head;
          param11 = param1.tail;
          if (param11 instanceof NofibPrelude.Cons.class) {
            param02 = param11.head;
            param12 = param11.tail;
            if (param12 instanceof NofibPrelude.Nil.class) {
              return true
            } else {
              scrut1 = x === 2;
              if (scrut1 === true) {
                if (param01 instanceof Empty1.class) {
                  scrut = x === 3;
                  if (scrut === true) {
                    if (param02 instanceof Empty1.class) {
                      return false
                    } else {
                      return false
                    }
                  } else {
                    return false
                  }
                } else {
                  scrut = x === 3;
                  if (scrut === true) {
                    if (param02 instanceof Empty1.class) {
                      return false
                    } else {
                      return false
                    }
                  } else {
                    return false
                  }
                }
              } else {
                scrut = x === 3;
                if (scrut === true) {
                  if (param02 instanceof Empty1.class) {
                    return false
                  } else {
                    return false
                  }
                } else {
                  return false
                }
              }
            }
          } else {
            scrut1 = x === 2;
            if (scrut1 === true) {
              if (param01 instanceof Empty1.class) {
                scrut = x === 3;
                if (scrut === true) {
                  return false
                } else {
                  return false
                }
              } else {
                scrut = x === 3;
                if (scrut === true) {
                  return false
                } else {
                  return false
                }
              }
            } else {
              scrut = x === 3;
              if (scrut === true) {
                return false
              } else {
                return false
              }
            }
          }
        } else {
          scrut1 = x === 2;
          if (scrut1 === true) {
            scrut = x === 3;
            if (scrut === true) {
              return false
            } else {
              return false
            }
          } else {
            scrut = x === 3;
            if (scrut === true) {
              return false
            } else {
              return false
            }
          }
        }
      } else {
        scrut1 = x === 2;
        if (scrut1 === true) {
          if (param1 instanceof NofibPrelude.Cons.class) {
            param01 = param1.head;
            param11 = param1.tail;
            if (param01 instanceof Empty1.class) {
              if (param11 instanceof NofibPrelude.Cons.class) {
                param02 = param11.head;
                param12 = param11.tail;
                if (param12 instanceof NofibPrelude.Nil.class) {
                  return true
                } else {
                  scrut = x === 3;
                  if (scrut === true) {
                    if (param02 instanceof Empty1.class) {
                      return false
                    } else {
                      return false
                    }
                  } else {
                    return false
                  }
                }
              } else {
                scrut = x === 3;
                if (scrut === true) {
                  return false
                } else {
                  return false
                }
              }
            } else {
              scrut = x === 3;
              if (scrut === true) {
                if (param11 instanceof NofibPrelude.Cons.class) {
                  param02 = param11.head;
                  param12 = param11.tail;
                  if (param02 instanceof Empty1.class) {
                    if (param12 instanceof NofibPrelude.Nil.class) {
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
          } else {
            scrut = x === 3;
            if (scrut === true) {
              return false
            } else {
              return false
            }
          }
        } else {
          scrut = x === 3;
          if (scrut === true) {
            if (param1 instanceof NofibPrelude.Cons.class) {
              param01 = param1.head;
              param11 = param1.tail;
              if (param11 instanceof NofibPrelude.Cons.class) {
                param02 = param11.head;
                param12 = param11.tail;
                if (param02 instanceof Empty1.class) {
                  if (param12 instanceof NofibPrelude.Nil.class) {
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
          } else {
            return false
          }
        }
      }
    } else {
      scrut1 = x === 2;
      if (scrut1 === true) {
        scrut = x === 3;
        if (scrut === true) {
          return false
        } else {
          return false
        }
      } else {
        scrut = x === 3;
        if (scrut === true) {
          return false
        } else {
          return false
        }
      }
    }
  } else {
    scrut1 = x === 2;
    if (scrut1 === true) {
      if (r instanceof NofibPrelude.Cons.class) {
        param0 = r.head;
        param1 = r.tail;
        if (param1 instanceof NofibPrelude.Cons.class) {
          param01 = param1.head;
          param11 = param1.tail;
          if (param01 instanceof Empty1.class) {
            if (param11 instanceof NofibPrelude.Cons.class) {
              param02 = param11.head;
              param12 = param11.tail;
              if (param12 instanceof NofibPrelude.Nil.class) {
                return true
              } else {
                scrut = x === 3;
                if (scrut === true) {
                  if (param02 instanceof Empty1.class) {
                    return false
                  } else {
                    return false
                  }
                } else {
                  return false
                }
              }
            } else {
              scrut = x === 3;
              if (scrut === true) {
                return false
              } else {
                return false
              }
            }
          } else {
            scrut = x === 3;
            if (scrut === true) {
              if (param11 instanceof NofibPrelude.Cons.class) {
                param02 = param11.head;
                param12 = param11.tail;
                if (param02 instanceof Empty1.class) {
                  if (param12 instanceof NofibPrelude.Nil.class) {
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
        } else {
          scrut = x === 3;
          if (scrut === true) {
            return false
          } else {
            return false
          }
        }
      } else {
        scrut = x === 3;
        if (scrut === true) {
          return false
        } else {
          return false
        }
      }
    } else {
      scrut = x === 3;
      if (scrut === true) {
        if (r instanceof NofibPrelude.Cons.class) {
          param0 = r.head;
          param1 = r.tail;
          if (param1 instanceof NofibPrelude.Cons.class) {
            param01 = param1.head;
            param11 = param1.tail;
            if (param11 instanceof NofibPrelude.Cons.class) {
              param02 = param11.head;
              param12 = param11.tail;
              if (param02 instanceof Empty1.class) {
                if (param12 instanceof NofibPrelude.Nil.class) {
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
        } else {
          return false
        }
      } else {
        return false
      }
    }
  }
};
empty = function empty(pos, board) {
  let param0, param1, r1, param01, param11, r2, param02, param12, r3, first1, first0, x, x1, x2;
  if (board instanceof NofibPrelude.Cons.class) {
    param0 = board.head;
    param1 = board.tail;
    r1 = param0;
    if (param1 instanceof NofibPrelude.Cons.class) {
      param01 = param1.head;
      param11 = param1.tail;
      r2 = param01;
      if (param11 instanceof NofibPrelude.Cons.class) {
        param02 = param11.head;
        param12 = param11.tail;
        r3 = param02;
        if (param12 instanceof NofibPrelude.Nil.class) {
          if (globalThis.Array.isArray(pos) && pos.length === 2) {
            first0 = pos[0];
            first1 = pos[1];
            if (first0 === 1) {
              x2 = first1;
              return empty_(x2, r1)
            } else if (first0 === 2) {
              x1 = first1;
              return empty_(x1, r2)
            } else if (first0 === 3) {
              x = first1;
              return empty_(x, r3)
            } else {
              throw new globalThis.Error("match error");
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
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
placePiece = function placePiece(p, board, pos) {
  let param0, param1, r1, param01, param11, r2, param02, param12, r3, first1, first0, x, x1, x2, scrut, tmp107, tmp108, tmp109, tmp110, tmp111, tmp112, tmp113, tmp114, tmp115, tmp116, tmp117, tmp118, tmp119;
  tmp107 = empty(pos, board);
  scrut = BenchmarkPrelude.not(tmp107);
  if (scrut === true) {
    return NofibPrelude.Nil
  } else {
    if (board instanceof NofibPrelude.Cons.class) {
      param0 = board.head;
      param1 = board.tail;
      r1 = param0;
      if (param1 instanceof NofibPrelude.Cons.class) {
        param01 = param1.head;
        param11 = param1.tail;
        r2 = param01;
        if (param11 instanceof NofibPrelude.Cons.class) {
          param02 = param11.head;
          param12 = param11.tail;
          r3 = param02;
          if (param12 instanceof NofibPrelude.Nil.class) {
            if (globalThis.Array.isArray(pos) && pos.length === 2) {
              first0 = pos[0];
              first1 = pos[1];
              if (first0 === 1) {
                x2 = first1;
                tmp108 = insert(p, r1, x2);
                tmp109 = NofibPrelude.Cons(r3, NofibPrelude.Nil);
                tmp110 = NofibPrelude.Cons(r2, tmp109);
                tmp111 = NofibPrelude.Cons(tmp108, tmp110);
                return NofibPrelude.Cons(tmp111, NofibPrelude.Nil)
              } else if (first0 === 2) {
                x1 = first1;
                tmp112 = insert(p, r2, x1);
                tmp113 = NofibPrelude.Cons(r3, NofibPrelude.Nil);
                tmp114 = NofibPrelude.Cons(tmp112, tmp113);
                tmp115 = NofibPrelude.Cons(r1, tmp114);
                return NofibPrelude.Cons(tmp115, NofibPrelude.Nil)
              } else if (first0 === 3) {
                x = first1;
                tmp116 = insert(p, r3, x);
                tmp117 = NofibPrelude.Cons(tmp116, NofibPrelude.Nil);
                tmp118 = NofibPrelude.Cons(r2, tmp117);
                tmp119 = NofibPrelude.Cons(r1, tmp118);
                return NofibPrelude.Cons(tmp119, NofibPrelude.Nil)
              } else {
                throw new globalThis.Error("match error");
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
      } else {
        throw new globalThis.Error("match error");
      }
    } else {
      throw new globalThis.Error("match error");
    }
  }
};
fullBoard = function fullBoard(b) {
  let tmp107, tmp108, lambda1;
  tmp107 = NofibPrelude.concat(b);
  lambda1 = (undefined, function (x) {
    let tmp109;
    tmp109 = eqPiece(x, Empty1);
    return BenchmarkPrelude.not(tmp109)
  });
  tmp108 = NofibPrelude.map(lambda1, tmp107);
  return andd(tmp108)
};
newPositions = function newPositions(piece, board) {
  let lscomp1, tmp107, tmp108, tmp109, tmp110, tmp111, lambda1;
  lscomp1 = function lscomp1(ls) {
    let lscomp2, param0, param1, x, xs, tmp112, tmp113, tmp114;
    if (ls instanceof NofibPrelude.Nil.class) {
      return NofibPrelude.Nil
    } else if (ls instanceof NofibPrelude.Cons.class) {
      param0 = ls.head;
      param1 = ls.tail;
      x = param0;
      xs = param1;
      lscomp2 = function lscomp2(ls1) {
        let param01, param11, y, ys, tmp115;
        if (ls1 instanceof NofibPrelude.Nil.class) {
          return lscomp1(xs)
        } else if (ls1 instanceof NofibPrelude.Cons.class) {
          param01 = ls1.head;
          param11 = ls1.tail;
          y = param01;
          ys = param11;
          tmp115 = lscomp2(ys);
          return NofibPrelude.Cons([
            x,
            y
          ], tmp115)
        } else {
          throw new globalThis.Error("match error");
        }
      };
      tmp112 = NofibPrelude.Cons(3, NofibPrelude.Nil);
      tmp113 = NofibPrelude.Cons(2, tmp112);
      tmp114 = NofibPrelude.Cons(1, tmp113);
      return lscomp2(tmp114)
    } else {
      throw new globalThis.Error("match error");
    }
  };
  tmp107 = NofibPrelude.Cons(3, NofibPrelude.Nil);
  tmp108 = NofibPrelude.Cons(2, tmp107);
  tmp109 = NofibPrelude.Cons(1, tmp108);
  tmp110 = lscomp1(tmp109);
  lambda1 = (undefined, function (pos) {
    return placePiece(piece, board, pos)
  });
  tmp111 = NofibPrelude.map(lambda1, tmp110);
  return NofibPrelude.concat(tmp111)
};
eval_ = function eval_(x) {
  let scrut, scrut1, tmp107;
  scrut1 = x === 3;
  if (scrut1 === true) {
    return XWin1
  } else {
    tmp107 = - 3;
    scrut = x === tmp107;
    if (scrut === true) {
      return OWin1
    } else {
      return Score1(x)
    }
  }
};
interpret = function interpret(x, l) {
  let param0, param1, param01, y, ls, tmp107;
  if (l instanceof NofibPrelude.Nil.class) {
    return Score1(x)
  } else if (l instanceof NofibPrelude.Cons.class) {
    param0 = l.head;
    param1 = l.tail;
    if (param0 instanceof Score1.class) {
      param01 = param0.i;
      y = param01;
      ls = param1;
      tmp107 = x + y;
      return interpret(tmp107, ls)
    } else if (param0 instanceof XWin1.class) {
      return XWin1
    } else if (param0 instanceof OWin1.class) {
      return OWin1
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
scorePiece = function scorePiece(p, score1) {
  if (p instanceof X1.class) {
    return score1
  } else if (p instanceof Empty1.class) {
    return 0
  } else if (p instanceof O1.class) {
    return - score1
  } else {
    throw new globalThis.Error("match error");
  }
};
map2 = function map2(f, xs, ys) {
  let param0, param1, x, xs1, scrut, param01, param11, y, ys1, tmp107, tmp108;
  if (xs instanceof NofibPrelude.Nil.class) {
    return NofibPrelude.Nil
  } else if (xs instanceof NofibPrelude.Cons.class) {
    param0 = xs.head;
    param1 = xs.tail;
    x = param0;
    xs1 = param1;
    if (ys instanceof NofibPrelude.Cons.class) {
      param01 = ys.head;
      param11 = ys.tail;
      y = param01;
      ys1 = param11;
      tmp107 = runtime.safeCall(f(x, y));
      tmp108 = map2(f, xs1, ys1);
      return NofibPrelude.Cons(tmp107, tmp108)
    } else {
      scrut = NofibPrelude.Nil;
      if (scrut === true) {
        return NofibPrelude.Nil
      } else {
        throw new globalThis.Error("match error");
      }
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
score = function score(board, win) {
  let tmp107, tmp108, tmp109, lambda1;
  lambda1 = (undefined, function (x, y) {
    return map2(scorePiece, x, y)
  });
  tmp107 = map2(lambda1, board, win);
  tmp108 = NofibPrelude.map(NofibPrelude.sum, tmp107);
  tmp109 = NofibPrelude.sum(tmp108);
  return eval_(tmp109)
};
static_ = function static_(board) {
  let tmp107, lambda1;
  lambda1 = (undefined, function (x) {
    return score(board, x)
  });
  tmp107 = NofibPrelude.map(lambda1, wins);
  return interpret(0, tmp107)
};
repTree = function repTree(f, g, a) {
  let tmp107, tmp108, lambda1;
  tmp107 = runtime.safeCall(f(a));
  lambda1 = (undefined, function (x) {
    return repTree(g, f, x)
  });
  tmp108 = NofibPrelude.map(lambda1, tmp107);
  return Branch1(a, tmp108)
};
mapTree = function mapTree(f, t) {
  let param0, param1, a, l, tmp107, tmp108, lambda1;
  if (t instanceof Branch1.class) {
    param0 = t.a;
    param1 = t.cs;
    a = param0;
    l = param1;
    tmp107 = runtime.safeCall(f(a));
    lambda1 = (undefined, function (x) {
      return mapTree(f, x)
    });
    tmp108 = NofibPrelude.map(lambda1, l);
    return Branch1(tmp107, tmp108)
  } else {
    throw new globalThis.Error("match error");
  }
};
prune = function prune(n, t) {
  let param0, param1, a, l, scrut, scrut1, tmp107, lambda1;
  if (t instanceof Branch1.class) {
    param0 = t.a;
    param1 = t.cs;
    a = param0;
    l = param1;
    scrut1 = n === 0;
    if (scrut1 === true) {
      return Branch1(a, NofibPrelude.Nil)
    } else {
      scrut = n < 0;
      if (scrut === true) {
        throw globalThis.Error("Tree.prune: < 0");
      } else {
        lambda1 = (undefined, function (x) {
          let tmp108;
          tmp108 = n - 1;
          return prune(tmp108, x)
        });
        tmp107 = NofibPrelude.map(lambda1, l);
        return Branch1(a, tmp107)
      }
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
opposite = function opposite(p) {
  if (p instanceof X1.class) {
    return O1
  } else if (p instanceof O1.class) {
    return X1
  } else {
    throw globalThis.Error("opposite");
  }
};
best = function best(f, bs, ss) {
  let best_, param0, param1, b, bs1, param01, param11, s, ss1;
  if (bs instanceof NofibPrelude.Cons.class) {
    param0 = bs.head;
    param1 = bs.tail;
    b = param0;
    bs1 = param1;
    if (ss instanceof NofibPrelude.Cons.class) {
      param01 = ss.head;
      param11 = ss.tail;
      s = param01;
      ss1 = param11;
      best_ = function best_(b1, s1, ls1, ls2) {
        let param02, param12, b_, bs2, param03, param13, s_, ss2, scrut, tmp107;
        if (ls1 instanceof NofibPrelude.Nil.class) {
          if (ls2 instanceof NofibPrelude.Nil.class) {
            return [
              b1,
              s1
            ]
          } else {
            throw new globalThis.Error("match error");
          }
        } else if (ls1 instanceof NofibPrelude.Cons.class) {
          param02 = ls1.head;
          param12 = ls1.tail;
          b_ = param02;
          bs2 = param12;
          if (ls2 instanceof NofibPrelude.Cons.class) {
            param03 = ls2.head;
            param13 = ls2.tail;
            s_ = param03;
            ss2 = param13;
            tmp107 = runtime.safeCall(f(s1, s_));
            scrut = evaluationEq(s1, tmp107);
            if (scrut === true) {
              return best_(b1, s1, bs2, ss2)
            } else {
              return best_(b_, s_, bs2, ss2)
            }
          } else {
            throw new globalThis.Error("match error");
          }
        } else {
          throw new globalThis.Error("match error");
        }
      };
      return best_(b, s, bs1, ss1)
    } else {
      throw new globalThis.Error("match error");
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
showMove = function showMove(m) {
  let first1, first0, b, e, tmp107, tmp108, tmp109, tmp110;
  if (globalThis.Array.isArray(m) && m.length === 2) {
    first0 = m[0];
    first1 = m[1];
    b = first0;
    e = first1;
    tmp107 = showEvaluation(e);
    tmp108 = NofibPrelude.nofibStringToList("\n");
    tmp109 = showBoard(b);
    tmp110 = NofibPrelude.append(tmp108, tmp109);
    return NofibPrelude.append(tmp107, tmp110)
  } else {
    throw new globalThis.Error("match error");
  }
};
max_ = function max_(e1, e2) {
  let param0, x, param01, y, scrut;
  if (e1 instanceof XWin1.class) {
    return XWin1
  } else {
    if (e2 instanceof XWin1.class) {
      return XWin1
    } else if (e2 instanceof OWin1.class) {
      return e1
    } else {
      if (e1 instanceof OWin1.class) {
        return e2
      } else if (e1 instanceof Score1.class) {
        param0 = e1.i;
        x = param0;
        if (e2 instanceof Score1.class) {
          param01 = e2.i;
          y = param01;
          scrut = x > y;
          if (scrut === true) {
            return Score1(x)
          } else {
            return Score1(y)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    }
  }
};
min_ = function min_(e1, e2) {
  let param0, x, param01, y, scrut;
  if (e1 instanceof OWin1.class) {
    return OWin1
  } else {
    if (e2 instanceof OWin1.class) {
      return OWin1
    } else if (e2 instanceof XWin1.class) {
      return e1
    } else {
      if (e1 instanceof XWin1.class) {
        return e2
      } else if (e1 instanceof Score1.class) {
        param0 = e1.i;
        x = param0;
        if (e2 instanceof Score1.class) {
          param01 = e2.i;
          y = param01;
          scrut = x < y;
          if (scrut === true) {
            return Score1(x)
          } else {
            return Score1(y)
          }
        } else {
          throw new globalThis.Error("match error");
        }
      } else {
        throw new globalThis.Error("match error");
      }
    }
  }
};
mise = function mise(f, g, t) {
  let param0, param1, l, a, tmp107, tmp108, lambda1;
  if (t instanceof Branch1.class) {
    param0 = t.a;
    param1 = t.cs;
    a = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return a
    } else {
      l = param1;
      tmp107 = runtime.safeCall(g(OWin1, XWin1));
      lambda1 = (undefined, function (x) {
        return mise(g, f, x)
      });
      tmp108 = NofibPrelude.map(lambda1, l);
      return NofibPrelude.foldr(f, tmp107, tmp108)
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
searchTree = function searchTree(p, board) {
  let tmp107, lambda1, lambda2;
  lambda1 = (undefined, function (x) {
    return newPositions(p, x)
  });
  lambda2 = (undefined, function (x) {
    let tmp108;
    tmp108 = opposite(p);
    return newPositions(tmp108, x)
  });
  tmp107 = repTree(lambda1, lambda2, board);
  return prune(5, tmp107)
};
cropTree = function cropTree(t) {
  let param0, param1, x, l, param01, x1, l1, a, tmp107, tmp108;
  if (t instanceof Branch1.class) {
    param0 = t.a;
    param1 = t.cs;
    a = param0;
    if (param1 instanceof NofibPrelude.Nil.class) {
      return Branch1(a, NofibPrelude.Nil)
    } else {
      if (param0 instanceof Score1.class) {
        param01 = param0.i;
        x1 = param01;
        l1 = param1;
        tmp107 = Score1(x1);
        tmp108 = NofibPrelude.map(cropTree, l1);
        return Branch1(tmp107, tmp108)
      } else {
        x = param0;
        l = param1;
        return Branch1(x, NofibPrelude.Nil)
      }
    }
  } else {
    throw new globalThis.Error("match error");
  }
};
bestMove = function bestMove(p, f, g, b) {
  let tmp107, tmp108, tmp109;
  tmp107 = searchTree(p, b);
  tmp108 = mapTree(static_, tmp107);
  tmp109 = cropTree(tmp108);
  return mise(f, g, tmp109)
};
alternate = function alternate(player, f, g, board) {
  let opposition, possibles, scores, boardd_eval, first1, first0, boardd, eval_1, scrut, scrut1, scrut2, tmp107, tmp108, tmp109, lambda1;
  scrut2 = fullBoard(board);
  if (scrut2 === true) {
    return NofibPrelude.Nil
  } else {
    tmp107 = static_(board);
    scrut1 = evaluationEq(tmp107, XWin1);
    if (scrut1 === true) {
      return NofibPrelude.Nil
    } else {
      tmp108 = static_(board);
      scrut = evaluationEq(tmp108, OWin1);
      if (scrut === true) {
        return NofibPrelude.Nil
      } else {
        opposition = opposite(player);
        possibles = newPositions(player, board);
        lambda1 = (undefined, function (x) {
          return bestMove(opposition, g, f, x)
        });
        scores = NofibPrelude.map(lambda1, possibles);
        boardd_eval = best(f, possibles, scores);
        if (globalThis.Array.isArray(boardd_eval) && boardd_eval.length === 2) {
          first0 = boardd_eval[0];
          first1 = boardd_eval[1];
          boardd = first0;
          eval_1 = first1;
          tmp109 = alternate(opposition, g, f, boardd);
          return NofibPrelude.Cons([
            boardd,
            eval_1
          ], tmp109)
        } else {
          throw new globalThis.Error("match error");
        }
      }
    }
  }
};
prog = function prog(input) {
  let board, testBoard, game, tmp107, tmp108, tmp109, tmp110, tmp111, tmp112, tmp113, tmp114, tmp115, tmp116, tmp117, tmp118, tmp119, tmp120, tmp121, tmp122, tmp123;
  board = function board(x) {
    let scrut;
    scrut = x === "doesn't happen";
    if (scrut === true) {
      return NofibPrelude.append(testBoard, testBoard)
    } else {
      return testBoard
    }
  };
  tmp107 = NofibPrelude.Cons(Empty1, NofibPrelude.Nil);
  tmp108 = NofibPrelude.Cons(O1, tmp107);
  tmp109 = NofibPrelude.Cons(Empty1, tmp108);
  tmp110 = NofibPrelude.Cons(Empty1, NofibPrelude.Nil);
  tmp111 = NofibPrelude.Cons(X1, tmp110);
  tmp112 = NofibPrelude.Cons(Empty1, tmp111);
  tmp113 = NofibPrelude.Cons(Empty1, NofibPrelude.Nil);
  tmp114 = NofibPrelude.Cons(Empty1, tmp113);
  tmp115 = NofibPrelude.Cons(Empty1, tmp114);
  tmp116 = NofibPrelude.Cons(tmp115, NofibPrelude.Nil);
  tmp117 = NofibPrelude.Cons(tmp112, tmp116);
  tmp118 = NofibPrelude.Cons(tmp109, tmp117);
  testBoard = tmp118;
  tmp119 = board(input);
  tmp120 = alternate(X1, max_, min_, tmp119);
  game = tmp120;
  tmp121 = NofibPrelude.nofibStringToList("OXO\n");
  tmp122 = NofibPrelude.map(showMove, game);
  tmp123 = NofibPrelude.concat(tmp122);
  return NofibPrelude.append(tmp121, tmp123)
};
Piece1 = class Piece {
  constructor() {}
  toString() { return "Piece"; }
};
const X$class = class X extends Piece1 {
  constructor() {
    super();
  }
  toString() { return "X"; }
}; X1 = new X$class;
X1.class = X$class;
const O$class = class O extends Piece1 {
  constructor() {
    super();
  }
  toString() { return "O"; }
}; O1 = new O$class;
O1.class = O$class;
const Empty$class = class Empty extends Piece1 {
  constructor() {
    super();
  }
  toString() { return "Empty"; }
}; Empty1 = new Empty$class;
Empty1.class = Empty$class;
Evaluation1 = class Evaluation {
  constructor() {}
  toString() { return "Evaluation"; }
};
const XWin$class = class XWin extends Evaluation1 {
  constructor() {
    super();
  }
  toString() { return "XWin"; }
}; XWin1 = new XWin$class;
XWin1.class = XWin$class;
const OWin$class = class OWin extends Evaluation1 {
  constructor() {
    super();
  }
  toString() { return "OWin"; }
}; OWin1 = new OWin$class;
OWin1.class = OWin$class;
Score1 = function Score(i1) {
  return new Score.class(i1);
};
Score1.class = class Score extends Evaluation1 {
  constructor(i) {
    super();
    this.i = i;
  }
  toString() { return "Score(" + globalThis.Predef.render(this.i) + ")"; }
};
Branch1 = function Branch(a1, cs1) {
  return new Branch.class(a1, cs1);
};
Branch1.class = class Branch {
  constructor(a, cs) {
    this.a = a;
    this.cs = cs;
  }
  toString() { return "Branch(" + globalThis.Predef.render(this.a) + ", " + globalThis.Predef.render(this.cs) + ")"; }
};
tmp = NofibPrelude.Cons(1, NofibPrelude.Nil);
tmp1 = NofibPrelude.Cons(1, tmp);
tmp2 = NofibPrelude.Cons(1, tmp1);
tmp3 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp4 = NofibPrelude.Cons(0, tmp3);
tmp5 = NofibPrelude.Cons(0, tmp4);
tmp6 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp7 = NofibPrelude.Cons(0, tmp6);
tmp8 = NofibPrelude.Cons(0, tmp7);
tmp9 = NofibPrelude.Cons(tmp8, NofibPrelude.Nil);
tmp10 = NofibPrelude.Cons(tmp5, tmp9);
tmp11 = NofibPrelude.Cons(tmp2, tmp10);
win1 = tmp11;
tmp12 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp13 = NofibPrelude.Cons(0, tmp12);
tmp14 = NofibPrelude.Cons(0, tmp13);
tmp15 = NofibPrelude.Cons(1, NofibPrelude.Nil);
tmp16 = NofibPrelude.Cons(1, tmp15);
tmp17 = NofibPrelude.Cons(1, tmp16);
tmp18 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp19 = NofibPrelude.Cons(0, tmp18);
tmp20 = NofibPrelude.Cons(0, tmp19);
tmp21 = NofibPrelude.Cons(tmp20, NofibPrelude.Nil);
tmp22 = NofibPrelude.Cons(tmp17, tmp21);
tmp23 = NofibPrelude.Cons(tmp14, tmp22);
win2 = tmp23;
tmp24 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp25 = NofibPrelude.Cons(0, tmp24);
tmp26 = NofibPrelude.Cons(0, tmp25);
tmp27 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp28 = NofibPrelude.Cons(0, tmp27);
tmp29 = NofibPrelude.Cons(0, tmp28);
tmp30 = NofibPrelude.Cons(1, NofibPrelude.Nil);
tmp31 = NofibPrelude.Cons(1, tmp30);
tmp32 = NofibPrelude.Cons(1, tmp31);
tmp33 = NofibPrelude.Cons(tmp32, NofibPrelude.Nil);
tmp34 = NofibPrelude.Cons(tmp29, tmp33);
tmp35 = NofibPrelude.Cons(tmp26, tmp34);
win3 = tmp35;
tmp36 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp37 = NofibPrelude.Cons(0, tmp36);
tmp38 = NofibPrelude.Cons(1, tmp37);
tmp39 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp40 = NofibPrelude.Cons(0, tmp39);
tmp41 = NofibPrelude.Cons(1, tmp40);
tmp42 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp43 = NofibPrelude.Cons(0, tmp42);
tmp44 = NofibPrelude.Cons(1, tmp43);
tmp45 = NofibPrelude.Cons(tmp44, NofibPrelude.Nil);
tmp46 = NofibPrelude.Cons(tmp41, tmp45);
tmp47 = NofibPrelude.Cons(tmp38, tmp46);
win4 = tmp47;
tmp48 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp49 = NofibPrelude.Cons(1, tmp48);
tmp50 = NofibPrelude.Cons(0, tmp49);
tmp51 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp52 = NofibPrelude.Cons(1, tmp51);
tmp53 = NofibPrelude.Cons(0, tmp52);
tmp54 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp55 = NofibPrelude.Cons(1, tmp54);
tmp56 = NofibPrelude.Cons(0, tmp55);
tmp57 = NofibPrelude.Cons(tmp56, NofibPrelude.Nil);
tmp58 = NofibPrelude.Cons(tmp53, tmp57);
tmp59 = NofibPrelude.Cons(tmp50, tmp58);
win5 = tmp59;
tmp60 = NofibPrelude.Cons(1, NofibPrelude.Nil);
tmp61 = NofibPrelude.Cons(0, tmp60);
tmp62 = NofibPrelude.Cons(0, tmp61);
tmp63 = NofibPrelude.Cons(1, NofibPrelude.Nil);
tmp64 = NofibPrelude.Cons(0, tmp63);
tmp65 = NofibPrelude.Cons(0, tmp64);
tmp66 = NofibPrelude.Cons(1, NofibPrelude.Nil);
tmp67 = NofibPrelude.Cons(0, tmp66);
tmp68 = NofibPrelude.Cons(0, tmp67);
tmp69 = NofibPrelude.Cons(tmp68, NofibPrelude.Nil);
tmp70 = NofibPrelude.Cons(tmp65, tmp69);
tmp71 = NofibPrelude.Cons(tmp62, tmp70);
win6 = tmp71;
tmp72 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp73 = NofibPrelude.Cons(0, tmp72);
tmp74 = NofibPrelude.Cons(1, tmp73);
tmp75 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp76 = NofibPrelude.Cons(1, tmp75);
tmp77 = NofibPrelude.Cons(0, tmp76);
tmp78 = NofibPrelude.Cons(1, NofibPrelude.Nil);
tmp79 = NofibPrelude.Cons(0, tmp78);
tmp80 = NofibPrelude.Cons(0, tmp79);
tmp81 = NofibPrelude.Cons(tmp80, NofibPrelude.Nil);
tmp82 = NofibPrelude.Cons(tmp77, tmp81);
tmp83 = NofibPrelude.Cons(tmp74, tmp82);
win7 = tmp83;
tmp84 = NofibPrelude.Cons(1, NofibPrelude.Nil);
tmp85 = NofibPrelude.Cons(0, tmp84);
tmp86 = NofibPrelude.Cons(0, tmp85);
tmp87 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp88 = NofibPrelude.Cons(1, tmp87);
tmp89 = NofibPrelude.Cons(0, tmp88);
tmp90 = NofibPrelude.Cons(0, NofibPrelude.Nil);
tmp91 = NofibPrelude.Cons(0, tmp90);
tmp92 = NofibPrelude.Cons(1, tmp91);
tmp93 = NofibPrelude.Cons(tmp92, NofibPrelude.Nil);
tmp94 = NofibPrelude.Cons(tmp89, tmp93);
tmp95 = NofibPrelude.Cons(tmp86, tmp94);
win8 = tmp95;
tmp96 = NofibPrelude.Cons(win8, NofibPrelude.Nil);
tmp97 = NofibPrelude.Cons(win7, tmp96);
tmp98 = NofibPrelude.Cons(win6, tmp97);
tmp99 = NofibPrelude.Cons(win5, tmp98);
tmp100 = NofibPrelude.Cons(win4, tmp99);
tmp101 = NofibPrelude.Cons(win3, tmp100);
tmp102 = NofibPrelude.Cons(win2, tmp101);
tmp103 = NofibPrelude.Cons(win1, tmp102);
wins = tmp103;
tmp104 = NofibPrelude.replicate(3, Empty1);
tmp105 = NofibPrelude.replicate(3, tmp104);
initialBoard = tmp105;
lambda = (undefined, function () {
  let tmp107, tmp108;
  tmp107 = prog("180000");
  tmp108 = NofibPrelude.nofibListToString(tmp107);
  return BenchmarkPrelude.print(tmp108)
});
tmp106 = lambda;
BenchmarkPrelude.benchmark(tmp106)