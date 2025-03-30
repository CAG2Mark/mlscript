package hkmc2

import mlscript.utils._, shorthands._
import hkmc2.syntax.Tree
import hkmc2.syntax.Keyword

class NofibDiffMaker(val rootPath: Str, val file: os.Path, val preludeFile: os.Path, val predefFile: os.Path, val relativeName: Str)
  extends LlirDiffMaker
:
  val nofib = Command[Str]("nofib", false)(x => x.stripLeading())

  override def processOrigin(origin: Origin)(using Raise): Unit =
    given Config = mkConfig
    nofib.get.fold(super.processOrigin(origin)): nofibFile =>
      ("noInstr" :: "effectOnly" :: "stackSafe" :: Nil).foreach: config =>
        output(s"Processing $config:")
        val nofibPath = os.pwd/"benchmark"/"target"/config/"nofib"/(nofibFile+".mjs")
        val benchmarkPrelude = os.pwd/"benchmark"/"target"/config/"precompiled"/"BenchmarkPrelude.mjs"
        super.processTrees(
          Tree.Modified(Keyword.`import`, N, Tree.StrLit(nofibPath.toString)) ::
          Tree.Modified(Keyword.`import`, N, Tree.StrLit(benchmarkPrelude.toString)) :: Nil)
        super.processOrigin(origin)
