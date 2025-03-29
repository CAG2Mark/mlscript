package hkmc2

import mlscript.utils.*, shorthands.*

import hkmc2.Config.EffectHandlers
import hkmc2.Config.StackSafety
import hkmc2.Config.LiftDefns

object Benchmark {
  val targetBaseDir = os.pwd/"benchmark"/"target"
  val benchmarkBaseDir = os.pwd/"benchmark"/"src"
  val runtimeRelPath = os.rel/"precompiled"/"Runtime.mjs"
  val noInstrDir = targetBaseDir/"noInstr"
  val effectOnlyDir = targetBaseDir/"effectOnly"
  val stackSafeDir = targetBaseDir/"stackSafe"
  
  val preludePath = os.pwd/"hkmc2"/"shared"/"src"/"test"/"mlscript"/"decls"/"Prelude.mls"
  val compilerNoInstr = MLsCompiler(preludePath, _(println))(using Config(N, N, S(LiftDefns())))
  val compilerInstr = MLsCompiler(preludePath, _(println))(using Config(N, S(EffectHandlers(N)), S(LiftDefns())))
  val compilerStackSafe = MLsCompiler(preludePath, _(println))(using Config(N, S(EffectHandlers(S(StackSafety.default))), N))
  val compilerStackSafeLifted = MLsCompiler(preludePath, _(println))(using Config(N, S(EffectHandlers(S(StackSafety.default))), S(LiftDefns())))
  
  val configsLst =
      (noInstrDir, compilerNoInstr, "only lifting") ::
      (effectOnlyDir, compilerInstr, "lifting and effect") ::
      (stackSafeDir, compilerStackSafeLifted, "lifting, effect, and stack safety") :: Nil
  
  val configs = configsLst.map((p, c, _) => (p, c))

  def compileFile(file: os.RelPath, targetDir: os.Path, compiler: MLsCompiler, exportName: Option[Str] = N, outFileOpt: Option[os.RelPath] = N) =
    val outFile = outFileOpt.getOrElse(file/os.up/(file.baseName + ".mjs"))
    compiler.compileModule(benchmarkBaseDir/file, S(targetDir/outFile), exportName, S(benchmarkBaseDir/runtimeRelPath))

  def compileVersions(file: os.RelPath, configs: List[(os.Path, MLsCompiler)]) =
    configs.foreach: (targetDir, compiler) =>
      compileFile(file, targetDir, compiler)

  def precompileModules =
    
    compileVersions(os.rel/"precompiled"/"Runtime.mls", configs.map((targetDir, _) => (targetDir, compilerNoInstr)))
    
    configs.foreach: (targetDir, _) =>
      os.copy.over(benchmarkBaseDir/"precompiled"/"RuntimeJS.mjs", targetDir/"precompiled"/"RuntimeJS.mjs")
    
    compileVersions(os.rel/"precompiled"/"Predef.mls", configs)
    compileVersions(os.rel/"precompiled"/"NofibPrelude.mls", configs)
    
    configs.foreach: (targetDir, compiler) =>
      val inFile = if compiler is compilerStackSafeLifted then
        os.rel/"precompiled"/"BenchmarkPrelude.instr.mls"
      else
        os.rel/"precompiled"/"BenchmarkPrelude.noinstr.mls"
      compileFile(inFile, targetDir, compiler, S("BenchmarkPrelude"), S(os.rel/"precompiled"/"BenchmarkPrelude.mjs"))

  def main(args: Array[String]) =

    println("Compiling dependencies")
    precompileModules
    val testDir = os.pwd/"hkmc2"/"shared"/"src"/"test"
    // Import nofib
    val nofibSources = os.list(os.pwd/"hkmc2"/"shared"/"src"/"test"/"mlscript"/"nofib").filter(_.last != "NofibPrelude.mls").filter(_.last != "input")
    nofibSources.foreach: path =>
      println(s"Importing ${path.last}")
      val preludeStr = f"""import "../precompiled/NofibPrelude.mls"
import "../precompiled/BenchmarkPrelude.mls"
import "fs"
open NofibPrelude
open BenchmarkPrelude

module ${path.baseName.replace("-", "")} with ...
"""
      val result = os.read(path).split("\n").map: line =>
          if line.startsWith(":") || line.startsWith("import ") then
            f"// $line"
          else if line.startsWith("prog(6).toStr") || line.startsWith("test") || line.startsWith("nofib") ||
            line.startsWith("map(x => nofib") then
            f"fun main() = $line"
          else if line.startsWith("print(test") || line.startsWith("print(nofib") then
            assert(line.endsWith(")"))
            f"fun main() = ${line.drop(6).dropRight(1)}"
          else if line == "print of" then
            "fun main() ="
          else if line.startsWith("let ls = testFish") then
            "fun main() = testFish_nofib(1)"
          else if line == "ls" && path.baseName == "fish" then
            ""
          else if line.startsWith("let ") then
            // convert private variables away
            "val " + line.drop(4)
          else
            line
        .mkString(preludeStr, "\n", "\n")
      os.write.over(os.pwd/"benchmark"/"src"/"nofib"/path.last.replace("-", ""), result)
    println("Compiling nofib")
    val nofibPaths = os.list(benchmarkBaseDir/"nofib")
    nofibPaths.foreach: path =>
      println(s"=> Compiling ${path.last}")
      compileVersions(os.rel/"nofib"/path.last, configs)
    
    val results = nofibPaths.map: path =>
      println(s"=> Running ${path.last}")
      val result = configsLst.map: (targetDir, _, nme) =>
        println(s"=> => Running ${path.last} with $nme")
        val targetImport = s"import Target from \"${targetDir/"nofib"/(path.baseName + ".mjs")}\";\n"
        val benchmarkImport = s"import Benchmark from \"${targetDir/"precompiled"/"BenchmarkPrelude.mjs"}\";\n"
        val benchmarkJS = targetImport + benchmarkImport + "Benchmark.benchmark(Target.main)"
        val result = os.proc("node").call(stdin = benchmarkJS, stderr = os.Inherit)
        val resultStr = result.out.bytes.map(_.toChar).mkString
        var time: Opt[Double] = N
        resultStr.linesIterator.foreach: line =>
          if line.startsWith("Time: ") then
            val t = line.substring(6, line.length - 2).toDouble
            println(f"Time: $t%.3f")
            time = S(t)
          else if line.startsWith("stackSafeCounter: ") then
            println(line)
          else
            println(line)
        time
      val folded = result.foldRight(S(List.empty): Opt[List[Double]]): (r, acc) =>
        (r, acc) match
          case (S(t), S(lst)) => S(t :: lst)
          case _ => N
      folded.foreach: lst =>
        println(f"Effect compared with baseline: ${lst.head / lst(1) * 100}%.3f%%")
        println(f"Stack safety compared with effect: ${lst(1) / lst(2) * 100}%.3f%%")
        println(f"Stack safety compared with baseline: ${lst.head / lst(2) * 100}%.3f%%")
      (path, folded)

    results.foreach: (path, result) =>
      result match
        case S(baseline :: effect :: stackSafe :: Nil) =>
          println(f"$path: ${(baseline / effect) * 100}%.3f%%, ${(baseline / stackSafe) * 100}%.3f%%")
        case _ =>
          println(s"$path: One of the test failed")
    // lazy val nofibFiles = List(os.pwd/"benchmark"/"src"/"examples"/"StackSafety.mls")

    // val results = nofibFiles.map: path =>
    //   def run(compiler: MLsCompiler): Option[Double] =
    //     // println(s"Compiling $path")
    //     compiler.compileModule(path)
    //     val resultPath = path / os.up / (path.baseName + ".mjs")
    //     println(s"Running $resultPath")
    //     val result = os.proc("node", resultPath.toString).call(stderr = os.Inherit)
    //     val resultStr = result.out.bytes.map(_.toChar).mkString
    //     var time: Opt[Double] = N
    //     resultStr.linesIterator.foreach: line =>
    //       if line.startsWith("Time: ") then
    //         val t = line.substring(6, line.length - 2).toDouble
    //         println(f"Time: $t%.3f")
    //         time = S(t)
    //       else if line.startsWith("stackSafeCounter: ") then
    //         println(line)
    //       else
    //         println(line)
    //     time
    //   // if path.last != "cryptarithm1.mls" then
    //   //   useStackSafe
    //   //   println("Stack safety: on")
    //   //   run(compilerStackSafe)
    //   // else
    //   //   print("Skipping cryptarithm1 as it OOM without lifter")
    //   useStackSafe
    //   println("Stack safety: on, Lift: on")
    //   val t1 = run(compilerStackSafeLifted)
    //   useNoInstr
    //   println("Stack safety: off")
    //   val t2 = run(compilerNoInstr)
    //   (t1, t2) match
    //     case (S(t1), S(t2)) =>
    //       val s1 = 1 / t1
    //       val s2 = 1 / t2
    //       println(f"Speed compared with stack safety off: ${s1 / s2 * 100}%.3f%%")
    //       path.last -> S(s1 / s2)
    //     case (S(_), N) =>
    //       path.last -> N
    //     case _ =>
    //       println("Stack safe version failed")
    //       path.last -> N
    // results.foreach: (path, result) =>
    //   result match
    //     case S(speed) =>
    //       println(f"$path: ${speed * 100}%.3f%%")
    //     case N =>
    //       println(s"$path: One of the test failed")
    // val speeds = results.collect { case (_, S(speed)) => speed }
    // val avg = speeds.sum / speeds.length
    // println(f"Average speed ratio: ${avg * 100}%.3f%%")
    // val std = math.sqrt(speeds.map(s => (s - avg) * (s - avg)).sum / speeds.length)
    // println(f"Standard deviation: ${std * 100}%.3f%%")
    // println(f"Min speed ratio: ${speeds.min * 100}%.3f%%")
    // println(f"Max speed ratio: ${speeds.max * 100}%.3f%%")
}
