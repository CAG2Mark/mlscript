package hkmc2

import org.scalatest.{funsuite, ParallelTestExecution}
import org.scalatest.time._

import mlscript.utils._
import os.Path

class NofibTestRunner
  extends DiffTestRunnerBase(DiffTestRunner.State)
  with ParallelTestExecution
:
  override protected lazy val diffTestFiles = os.list(os.pwd/"benchmark"/"src"/"test"/"nofib")

  override protected def createDiffMaker(file: Path, preludePath: Path, predefPath: Path, relativeName: String): DiffMaker =
    new NofibDiffMaker((os.pwd/"benchmark").toString, file, preludePath, predefPath, relativeName)

