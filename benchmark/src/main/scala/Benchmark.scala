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
  
  val compilerNoInstr = MLsCompiler(preludePath, _(println))(using Config(N, N, S(LiftDefns())))
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
      compilerStackSafeLifted.compileModule(file)
      os.copy(origName, nofibPrecompilePath/instrName, replaceExisting = true)
      compilerNoInstr.compileModule(file)
      os.copy(origName, nofibPrecompilePath/noinstrName, replaceExisting = true)

    compileBoth(compileTestDir/"Predef.mls")
    compileBoth(nofibPrecompilePath/"NofibPrelude.mls")

    os.copy(nofibPrecompilePath/"BenchmarkPrelude.instr.mls", nofibPrecompilePath/"BenchmarkPrelude.mls", replaceExisting = true)
    compilerStackSafeLifted.compileModule(nofibPrecompilePath/"BenchmarkPrelude.mls")
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
    println()
    // Import nofib
//     val nofibSources = os.list(os.pwd/"hkmc2"/"shared"/"src"/"test"/"mlscript"/"nofib").filter(_.last != "NofibPrelude.mls").filter(_.last != "input")
//     nofibSources.foreach: path =>
//       println(s"Importing ${path.last}")
//       val preludeStr = f"""import "../precompiled/NofibPrelude.mls"
// import "../precompiled/BenchmarkPrelude.mls"
// import "fs"
// open NofibPrelude
// open BenchmarkPrelude

// module ${path.baseName.replace("-", "")} with ...
// """
//       val result = os.read(path).split("\n").map: line =>
//           if line.startsWith(":") || line.startsWith("import ") then
//             f"// $line"
//           else if line.startsWith("prog(6).toStr") || line.startsWith("test") || line.startsWith("nofib") ||
//             line.startsWith("print(test") || line.startsWith("print(nofib") || line.startsWith("print of") ||
//             line.startsWith("map(x => nofib") then
//             f"benchmark of () => $line"
//           else if line.startsWith("let ls = testFish") then
//             "let ls = benchmark of () => testFish_nofib(1)"
//           else if line.startsWith("let ") then
//             // convert private variables away
//             "val " + line.drop(4)
//           else
//             line
//         .mkString(preludeStr, "\n", "\n")
//       os.write.over(os.pwd/"benchmark"/"src"/"nofib"/path.last, result)
    val failing = Set()
    lazy val nofibFiles = os.list(os.pwd/"benchmark"/"src"/"nofib").filter(_.ext == "mls").filterNot(p => failing.exists(_ == p.baseName))
      .dropWhile(_.last != "cryptarithm1.mls")
    // lazy val nofibFiles = List(os.pwd/"benchmark"/"src"/"examples"/"StackSafety.mls")

    val results = nofibFiles.map: path =>
      def run(compiler: MLsCompiler): Option[Double] =
        // println(s"Compiling $path")
        compiler.compileModule(path)
        val resultPath = path / os.up / (path.baseName + ".mjs")
        println(s"Running $resultPath")
        val result = os.proc("node", resultPath.toString).call(stderr = os.Inherit)
        val resultStr = result.out.bytes.map(_.toChar).mkString
        if resultStr.startsWith("Time: ") then
          val time = resultStr.substring(6, resultStr.length - 3).toDouble
          println(f"Time: $time%.3f")
          S(time)
        else
          println(resultStr)
          N
      // if path.last != "cryptarithm1.mls" then
      //   useStackSafe
      //   println("Stack safety: on")
      //   run(compilerStackSafe)
      // else
      //   print("Skipping cryptarithm1 as it OOM without lifter")
      useStackSafe
      println("Stack safety: on, Lift: on")
      val t1 = run(compilerStackSafeLifted)
      useNoInstr
      println("Stack safety: off")
      val t2 = run(compilerNoInstr)
      (t1, t2) match
        case (S(t1), S(t2)) =>
          val s1 = 1 / t1
          val s2 = 1 / t2
          println(f"Speed compared with stack safety off: ${s1 / s2 * 100}%.3f%%")
          path.last -> S(s1 / s2)
        case _ =>
          path.last -> N
    results.foreach: (path, result) =>
      result match
        case S(speed) =>
          println(f"$path: ${speed * 100}%.3f%%")
        case N =>
          println(s"$path: One of the test failed")
    val speeds = results.collect { case (_, S(speed)) => speed }
    val avg = speeds.sum / speeds.length
    println(f"Average speed ratio: ${avg * 100}%.3f%%")
    val std = math.sqrt(speeds.map(s => (s - avg) * (s - avg)).sum / speeds.length)
    println(f"Standard deviation: ${std * 100}%.3f%%")
    println(f"Min speed ratio: ${speeds.min * 100}%.3f%%")
    println(f"Max speed ratio: ${speeds.max * 100}%.3f%%")
}
