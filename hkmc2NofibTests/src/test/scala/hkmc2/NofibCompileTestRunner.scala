package hkmc2

import hkmc2.utils.*, shorthands.*
import hkmc2.Config.EffectHandlers
import hkmc2.Config.StackSafety


class NofibCompileTestRunner extends CompileTestRunnerBase(
  compileDirs = TestFolders.nofibCompileDirs(os.pwd),
):
  protected def cctx: CompilerCtx = NofibCompileTestRunner.cctx

end NofibCompileTestRunner


object NofibCompileTestRunner:
  import io.PlatformPath.given
  val newConfig = Config.default(TestFolders.mainTestDir(os.pwd)).copy(effectHandlers = S(EffectHandlers(false, S(StackSafety(100)), doNotInstrumentTopLevelModCtor = false)))
  given cctx: CompilerCtx = CompilerCtx.fresh(io.FileSystem.default, TestFolders.compilerPaths(os.pwd), newConfig)

end NofibCompileTestRunner
