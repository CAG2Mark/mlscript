package hkmc2

import mlscript.utils.*, shorthands.*

import hkmc2.Config.EffectHandlers
import hkmc2.Config.StackSafety
import hkmc2.Config.LiftDefns

object Benchmark {
  val testDir = os.pwd/"hkmc2"/"shared"/"src"/"test"
  val compileTestDir = testDir/"mlscript-compile"
  val preludePath = testDir/"mlscript"/"decls"/"Prelude.mls"
  val nofibPath = os.pwd/"benchmark"/"src"/"nofib"
  val nofibPrecompilePath = os.pwd/"benchmark"/"src"/"precompiled"
  
  val compilerNoInstr = MLsCompiler(preludePath, _(println))(using Config(N, N, N))
  val compilerInstr = MLsCompiler(preludePath, _(println))(using Config(N, S(EffectHandlers(N)), N))
  val compilerStackSafe = MLsCompiler(preludePath, _(println))(using Config(N, S(EffectHandlers(S(StackSafety.default))), N))
  val compilerStackSafeLifted = MLsCompiler(preludePath, _(println))(using Config(N, S(EffectHandlers(S(StackSafety.default))), S(LiftDefns())))

  def precompileModules =
    compilerNoInstr.compileModule(compileTestDir/"Runtime.mls")

    def compileBoth(file: os.Path) =
      val origName = file / os.up / (file.baseName + ".mjs")
      val noinstrName = os.SubPath(file.baseName + ".noinstr.mjs")
      val instrName = os.SubPath(file.baseName + ".instr.mjs")
      println(file)
      compilerStackSafe.compileModule(file)
      os.copy(origName, nofibPrecompilePath/instrName, replaceExisting = true)
      compilerNoInstr.compileModule(file)
      os.copy(origName, nofibPrecompilePath/noinstrName, replaceExisting = true)

    compileBoth(compileTestDir/"Predef.mls")
    compileBoth(nofibPrecompilePath/"NofibPrelude.mls")

    os.copy(nofibPrecompilePath/"BenchmarkPrelude.instr.mls", nofibPrecompilePath/"BenchmarkPrelude.mls", replaceExisting = true)
    compilerInstr.compileModule(nofibPrecompilePath/"BenchmarkPrelude.mls")
    os.copy(nofibPrecompilePath/"BenchmarkPrelude.mjs", nofibPrecompilePath/"BenchmarkPrelude.instr.mjs", replaceExisting = true)

    os.copy(nofibPrecompilePath/"BenchmarkPrelude.noinstr.mls", nofibPrecompilePath/"BenchmarkPrelude.mls", replaceExisting = true)
    compilerNoInstr.compileModule(nofibPrecompilePath/"BenchmarkPrelude.mls")
    os.copy(nofibPrecompilePath/"BenchmarkPrelude.mjs", nofibPrecompilePath/"BenchmarkPrelude.noinstr.mjs", replaceExisting = true)


  def useStackSafe =
    os.copy(nofibPrecompilePath/"Predef.instr.mjs", compileTestDir/"Predef.mjs", replaceExisting = true)
    os.copy(nofibPrecompilePath/"NofibPrelude.instr.mjs", nofibPrecompilePath/"NofibPrelude.mjs", replaceExisting = true)
    os.copy(nofibPrecompilePath/"BenchmarkPrelude.instr.mjs", nofibPrecompilePath/"BenchmarkPrelude.mjs", replaceExisting = true)

  def useNoInstr =
    os.copy(nofibPrecompilePath/"Predef.noinstr.mjs", compileTestDir/"Predef.mjs", replaceExisting = true)
    os.copy(nofibPrecompilePath/"NofibPrelude.noinstr.mjs", nofibPrecompilePath/"NofibPrelude.mjs", replaceExisting = true)
    os.copy(nofibPrecompilePath/"BenchmarkPrelude.noinstr.mjs", nofibPrecompilePath/"BenchmarkPrelude.mjs", replaceExisting = true)

  def main(args: Array[String]) =

    println("Precompiling modules")
    precompileModules
    val blacklist = "cryptarithm1" :: Nil
    // val blacklist = Nil
    lazy val nofibFiles = os.list(os.pwd/"benchmark"/"src"/"nofib").filter(_.ext == "mls").filterNot(p => blacklist.exists(_ == p.baseName))
    // lazy val nofibFiles = List(os.pwd/"benchmark"/"src"/"nofib"/"cryptarithm1.mls")
    // lazy val nofibFiles = List(os.pwd/"benchmark"/"src"/"examples"/"StackSafety.mls")

    nofibFiles.foreach: path =>
      def run(compiler: MLsCompiler) =
        println(s"Compiling $path")
        compiler.compileModule(path)
        val resultPath = path / os.up / (path.baseName + ".mjs")
        println(s"Running $resultPath")
        os.proc("node", resultPath.toString).call(stdout = os.Inherit, stderr = os.Inherit)
      useStackSafe
      println("Stack safety: on")
      run(compilerStackSafeLifted)
      useNoInstr
      println("Stack safety: off")
      run(compilerNoInstr)

}
