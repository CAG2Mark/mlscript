package hkmc2

import mlscript.utils.*, shorthands.*

import hkmc2.Config.EffectHandlers
import hkmc2.Config.StackSafety

object Benchmark {
  val testDir = os.pwd/"hkmc2"/"shared"/"src"/"test"
  val compileTestDir = testDir/"mlscript-compile"
  val preludePath = testDir/"mlscript"/"decls"/"Prelude.mls"
  val nofibPath = os.pwd/"benchmark"/"src"/"nofib"

  def precompileModules =
    val rtCompiler = MLsCompiler(preludePath, _(println))(using Config(N, N))
    rtCompiler.compileModule(compileTestDir/"Runtime.mls")
    rtCompiler.compileModule(compileTestDir/"Predef.mls")
    val compiler = MLsCompiler(preludePath, _(println))(using Config(N, S(EffectHandlers(S(StackSafety.default)))))
    compiler.compileModule(nofibPath/"NofibPrelude.mls")

  def main(args: Array[String]) =

    println("Precompiling modules")
    precompileModules
    lazy val nofibFiles = os.list(os.pwd/"benchmark"/"src"/"nofib").filter(_.ext == "mls").filterNot(_.baseName == "NofibPrelude").filterNot(_.baseName == "cryptarithm1")
    // val nofibFiles = List(nofibPath/"gcd.mls", nofibPath/"lambda.mls", nofibPath/"cryptarithm1.mls") // JS OOM
    // val nofibFiles = List(nofibPath/"treejoin.mls")

    given Config = Config(N, S(EffectHandlers(S(StackSafety.default))))
    // given Config = Config(N, N)

    nofibFiles.foreach: path =>
      val compiler = MLsCompiler(preludePath, _(println))
      println(s"Compiling $path")
      compiler.compileModule(path)
      val resultPath = path / os.up / (path.baseName + ".mjs")
      println(s"Running $resultPath")
      os.proc("node", resultPath.toString).call(stdout = os.Inherit, stderr = os.Inherit)
      // println(os.proc("node", resultPath.toString).call().out.text())
}
