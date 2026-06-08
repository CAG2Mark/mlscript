package hkmc2

import hkmc2.utils.*, shorthands.*
import utils.*

import hkmc2.codegen.*
import hkmc2.semantics.Elaborator.State
import hkmc2.semantics.*
import hkmc2.syntax.Tree
import hkmc2.codegen.HandlerLowering.FnOrCls

class StackSafeTransform(depthLimit: Int, paths: HandlerPaths, stackSafetyMap: StackSafetyMap)(using State, Config):

  def transformTopLevel(b: Block) = b
