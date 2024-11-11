package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import hkmc2.{semantics => sem}
import hkmc2.semantics.{Term => st}

import syntax.{Literal, Tree}
import semantics.*
import semantics.Term.*

import Subst.subst

class InstrLowering(using TL, Raise, Elaborator.State) extends Lowering:
  override def term(t: st)(k: Result => Block)(using Subst): Block =
    t match
      case st.Handle(lhs, rhs, defs) =>
        tl.log(s"Lowering.term ${t.showDbg.truncate(30, "[...]")}")
        ???
      case _ => super.term(t)(k)
    