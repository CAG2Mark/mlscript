package hkmc2.codegen

import hkmc2.codegen.*
import hkmc2.semantics.Elaborator.State

class StackSafeTransform(depthLimit: Int)(using State):
  def transformTopLevel(b: Block) = b