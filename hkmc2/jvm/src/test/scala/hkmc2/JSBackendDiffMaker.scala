package hkmc2

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import utils.*

import semantics.*
import codegen.*
import codegen.js.{JSBuilder, JSBuilderArgNumSanityChecks}
import document.*
import codegen.Block
import codegen.js.Scope
import hkmc2.syntax.Tree.Ident
import hkmc2.codegen.Path

abstract class JSBackendDiffMaker extends MLsDiffMaker:
  
  val instrLowering = NullaryCommand("il")
  val debugLowering = NullaryCommand("dl")
  val js = NullaryCommand("js")
  val sjs = NullaryCommand("sjs")
  val showRepl = NullaryCommand("showRepl")
  val silent = NullaryCommand("silent")
  val noSanityCheck = NullaryCommand("noSanityCheck")
  val traceJS = NullaryCommand("traceJS")
  val expect = Command("expect"): ln =>
    ln.trim
  
  private val baseScp: codegen.js.Scope =
    codegen.js.Scope.empty
  
  val ltl = new TraceLogger:
    override def doTrace = debugLowering.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  val replTL = new TraceLogger:
    override def doTrace = showRepl.isSet
    override def emitDbg(str: String): Unit = output(str)
  
  lazy val host =
    hostCreated = true
    given TL = replTL
    val h = ReplHost(rootPath)
    h
  
  private var hostCreated = false
  override def run(): Unit =
    try super.run() finally if hostCreated then host.terminate()
  
  override def processTerm(blk: semantics.Term.Blk, inImport: Bool)(using Raise): Unit =
    super.processTerm(blk, inImport)
    if js.isSet then
      val low = ltl.givenIn:
        if instrLowering.isSet then
          new codegen.InstrLowering
          with codegen.LoweringSelSanityChecks(noSanityCheck.isUnset)
          with codegen.LoweringTraceLog(traceJS.isSet)
        else
          new codegen.Lowering
          with codegen.LoweringSelSanityChecks(noSanityCheck.isUnset)
          with codegen.LoweringTraceLog(traceJS.isSet)
      given Elaborator.Ctx = curCtx
      val jsb = new JSBuilder
        with JSBuilderArgNumSanityChecks(noSanityCheck.isUnset)
      val le = low.program(blk)
      if showLoweredTree.isSet then
        output(s"Lowered:")
        output(le.showAsTree)
      
      // * Note that the codegen scope is not in sync with curCtx in terms of its `this` symbol.
      // * We do not nest TopLevelSymbol in codegen `Scope`s
      // * to avoid needlessly generating new variable names in separate blocks.
      val nestedScp = baseScp.nest
      // val nestedScp = codegen.js.Scope(S(baseScp), curCtx.outer, collection.mutable.Map.empty) // * not needed
      
      val je = nestedScp.givenIn:
        jsb.program(le, N, wd)
      val jsStr = je.stripBreaks.mkString(100)
      if sjs.isSet then
        output(s"JS:")
        output(jsStr)
      def mkQuery(prefix: Str, jsStr: Str) =
        import hkmc2.Message.MessageContext
        val queryStr = jsStr.replaceAll("\n", " ")
        val (reply, stderr) = host.query(queryStr, !expectRuntimeOrCodeGenErrors && fixme.isUnset && todo.isUnset)
        reply match
          case ReplHost.Result(content, stdout) =>
            if silent.isUnset then
              stdout match
                case None | Some("") =>
                case Some(str) =>
                  str.splitSane('\n').foreach: line =>
                    output(s"> ${line}")
              content match
              case "undefined" =>
              case "null" =>
              case _ =>
                expect.get match
                  case S(expected) if content != expected => raise:
                    ErrorReport(msg"Expected: ${expected}, got: ${content}" -> N :: Nil,
                      source = Diagnostic.Source.Runtime)
                  case _ => output(s"$prefix= ${content}")
          case ReplHost.Empty =>
          case ReplHost.Unexecuted(message) => ???
          case ReplHost.Error(isSyntaxError, message, otherOutputs) =>
            if otherOutputs.nonEmpty then
              otherOutputs.splitSane('\n').foreach: line =>
                output(s"> ${line}")
            
            if (isSyntaxError) then
              // If there is a syntax error in the generated code,
              // it should be a code generation error.
              raise(ErrorReport(msg"[Uncaught SyntaxError] ${message}" -> N :: Nil,
                source = Diagnostic.Source.Compilation))
            else
              // Otherwise, it is considered a simple runtime error.
              raise(ErrorReport(msg"${message}" -> N :: Nil,
                source = Diagnostic.Source.Runtime))
        if stderr.nonEmpty then output(s"// Standard Error:\n${stderr}")
      
      
      if traceJS.isSet then
        host.execute(
          "globalThis.Predef.TraceLogger.enabled = true; " +
          "globalThis.Predef.TraceLogger.resetIndent(0)")
      
      mkQuery("", jsStr)
      
      if traceJS.isSet then
        host.execute("globalThis.Predef.TraceLogger.enabled = false")
      
      import Elaborator.Ctx.*
      def definedValues = curCtx.env.iterator.flatMap:
        case (nme, e @ (_: RefElem | SelElem(RefElem(_: InnerSymbol), _, _))) =>
          e.symbol match
          case S(ts: TermSymbol) if ts.k.isInstanceOf[syntax.ValLike] => S((nme, ts))
          case S(ts: BlockMemberSymbol)
            if ts.trmImplTree.exists(_.k.isInstanceOf[syntax.ValLike]) => S((nme, ts))
          case _ => N
        case _ => N
      definedValues.toSeq.sortBy(_._1).foreach: (nme, sym) =>
        val le = codegen.Return(codegen.Value.Ref(sym), implct = true)
        val je = nestedScp.givenIn:
          jsb.block(le)
        val jsStr = je.stripBreaks.mkString(100)
        mkQuery(s"$nme ", jsStr)
      
      

