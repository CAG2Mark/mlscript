package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._

import mlscript.utils._

class NofibTestRunner
  extends DiffTestRunnerBase(DiffTestRunner.State)
  with ParallelTestExecution
:
  override protected lazy val diffTestFiles = os.list(os.pwd/"benchmark"/"src"/"test"/"nofib")

