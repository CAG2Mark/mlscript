const RuntimeJS = {
  bitand(lhs, rhs) {
    return lhs & rhs;
  },
  bitnot(v) {
    return ~v;
  },
  bitor(lhs, rhs) {
    return lhs | rhs;
  },
  shl(v, sh) {
    return v << sh;
  },
  try_catch(computation, onError) {
    try { return computation() }
    catch (error) { return onError(error) }
  },
  is_stackoverflow(err) {
    return err instanceof RangeErrorreturn && err.message === "Maximum call stack size exceeded"
  },
  symbols: {
    definitionMetadata: Symbol.for("mlscript.definitionMetadata"),
    prettyPrint: Symbol.for("mlscript.prettyPrint")
  },
  short_and(lhs, rhs) {
    return lhs && rhs();
  },
  short_or(lhs, rhs) {
    return lhs || rhs();
  }
}

export default RuntimeJS;

