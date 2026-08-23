package hkmc2
package codegen

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.boundary
import sourcecode.{ Line, FileName, Name }

import hkmc2.utils.*, shorthands.*
import hkmc2.utils.*
import hkmc2.utils.SymbolSubst
import hkmc2.Message.MessageContext

import syntax.{Literal, Tree}
import semantics.*
import semantics.Elaborator.ctx
import semantics.Elaborator.State
import hkmc2.Config.EffectHandlers
import scala.collection.mutable.ListBuffer


object HandlerLowering:

  private val pcIdent: Tree.Ident = Tree.Ident("pc")
  private val nextIdent: Tree.Ident = Tree.Ident("next")
  private val lastIdent: Tree.Ident = Tree.Ident("last")
  private val contTraceIdent: Tree.Ident = Tree.Ident("contTrace")
  private def unit = Value.Lit(Tree.UnitLit(true))
  private def intLit(i: BigInt) = Value.Lit(Tree.IntLit(i))

  private def locToStr(loc: Loc) =
    val (line, _, col) = loc.origin.fph.getLineColAt(loc.spanStart)
    Value.Lit(Tree.StrLit(s"${loc.origin.fileName.last}:${line + loc.origin.startLineNum - 1}:$col"))
  
  extension (p: Path)
    def pc = p.selN(pcIdent)
    def value = p.selN(Tree.Ident("value"))
    def next = p.selN(nextIdent)
    def last = p.selN(lastIdent)
    def contTrace = p.selN(contTraceIdent)
  
  type FnOrCls = Either[BlockMemberSymbol, DefinitionSymbol[? <: ClassLikeDef] & InnerSymbol]

  private enum HandlerCtx:
    case FunctionLike(ctx: FunctionCtx)
    case Ctor
    case ModCtor(trulyNested: Bool)
    case TopLevel

    // Since constructors are not named, they cannot be resumed
    def inCtor = this === Ctor || this.isInstanceOf[ModCtor]
    def currentBlockIsTrulyNested = this match
      case FunctionLike(_) => true
      case Ctor => true
      case ModCtor(trulyNested) => trulyNested
      case TopLevel => false
    
  
  // currentFun: path to the current function for resumption
  // thisPath: path to `this` binding if the function is a method, `this` will be rebinded on resumption
  private case class FunctionCtx(currentFun: Path, thisPath: Option[Path], resumeInfo: ResumeInfo, debugInfo: DebugInfo, inGetter: Bool)
  
  // argLists: length-encoded argument list used for resumption.
  // currentLocals: All locals to be saved and reloaded, this cannot include any variables in outer scopes
  // currentStackSafetySym: The symbol to be used for stack safety
  private case class ResumeInfo(
    argLists: List[Path],
    currentLocals: List[LocalVarSymbol],
    currentStackSafetySym: FnOrCls,
  )
  
  private case class DebugInfo(
    debugNme: Str,
    debugInfoPath: Path,
  )

  object EffectfulResult:
    def unapply(r: Result)(using Config): Bool = r match
      case c: Call if c.metadata.mayRaiseEffects => true
      case _: Instantiate if config.checkInstantiateEffect => true
      case _ => false
  
  type StateId = BigInt

import HandlerLowering.*

// maps function symbol -> num param lists
case class HandlerAnalysisRes(results: Map[DefinitionSymbol[?], Int])

class HandlerPaths(using Elaborator.State):
  val runtimePath: Path = State.runtimeSymbol.asSimpleRef
  val contClsPath: Path = runtimePath.selSN("FunctionContFrame").selSN("class")
  val mkEffectPath: Path = runtimePath.selSN("mkEffect")
  val handleBlockImplPath: Path = runtimePath.selSN("handleBlockImpl")
  val stackDelayClsPath: Path = runtimePath.selSN("StackDelay")
  val topLevelEffectPath: Path = runtimePath.selSN("topLevelEffect")
  val illegalEffectPath: Path = runtimePath.selSN("illegalEffect")
  val enterHandleBlockPath: Path = runtimePath.selSN("enterHandleBlock")
  val stackDepthIdent = new Tree.Ident("stackDepth")
  val stackDepthPath: Path = runtimePath.selN(stackDepthIdent)
  val checkDepthPath: Path = runtimePath.selN(Tree.Ident("checkDepth"))
  val runStackSafePath: Path = runtimePath.selN(Tree.Ident("runStackSafe"))
  val trampolinePath: Path = runtimePath.selN(Tree.Ident("topLevelTrampoline"))
  val fnLocalsPath: Path = runtimePath.selSN("FnLocalsInfo").selSN("class")
  val localVarInfoPath: Path = runtimePath.selSN("LocalVarInfo").selSN("class")
  val curEffect: Path = runtimePath.selSN("curEffect")
  val pushFramePath: Path = runtimePath.selSN("pushFrame")
  val popFramePath: Path = runtimePath.selSN("popFrame")
  val resetEffects: Path = runtimePath.selSN("resetEffects")
  val resumePc: Path = runtimePath.selSN("resumePc")
  val resumeIdx: Path = runtimePath.selSN("resumeIdx")
  val resumeValueIdent = new Tree.Ident("resumeValue")
  val resumeValue: Path = runtimePath.selN(resumeValueIdent)
  val oldPcIdent = new Tree.Ident("oldPc")
  val oldPcValue: Path = runtimePath.selN(oldPcIdent)
  val contTraceIdent = new Tree.Ident("curContTrace")
  val contTraceValue: Path = runtimePath.selN(contTraceIdent)

class HandlerLowering(paths: HandlerPaths, opt: EffectHandlers)(using TL, Raise, Elaborator.State, Elaborator.Ctx, Config):
  
  private def freshTmp(dbgNme: Str = "tmp") = new TempSymbol(N, dbgNme)
  private def freshLabel(nme: Str) = new LabelSymbol(N, nme)
  
  // inlined versions of the runtime functions for stack safety
  
  private def pushFrame(fnPath: Path, varsClsPath: Path, rest: Block): Block =
    if config.stackSafety.isDefined then
      val newFrameSym = TempSymbol(N, "newFrame")
      val predSym = TempSymbol(N)
      val pred = Call(
          State.builtinOpsMap("===").asSimpleRef, 
          (paths.contTraceValue.selN(lastIdent).asArg :: paths.contTraceValue.asArg :: Nil) ne_:: Nil
        )(CallMetadata.defaultMlsFun)
      val inst = Instantiate(
          true,
          paths.contClsPath,
          (paths.contTraceValue.next.asArg :: fnPath.asArg :: varsClsPath.asArg :: Nil) :: Nil
        )(InstantiateMetadata.empty)
      blockBuilder
        .assignScoped(newFrameSym, inst)
        .assignScoped(predSym, pred)
        .ifthen(predSym.asSimpleRef, Case.Lit(Tree.BoolLit(true)), AssignField(paths.contTraceValue, lastIdent, newFrameSym.asSimpleRef, End())(N))
        .assignFieldN(paths.contTraceValue, nextIdent, newFrameSym.asSimpleRef)
        .rest(rest)
    else
      Assign(
        NoSymbol, 
        Call(
          paths.pushFramePath,
          (fnPath.asArg :: varsClsPath.asArg :: Nil) ne_:: Nil
        )(CallMetadata.defaultMlsFun),
        rest
      )
        
  private def popFrame(rest: Block): Block =
    if config.stackSafety.isDefined then
      val predSym = TempSymbol(N)
      val pred = Call(
          State.builtinOpsMap("===").asSimpleRef, 
          (paths.contTraceValue.selN(nextIdent).asArg :: paths.contTraceValue.selN(lastIdent).asArg :: Nil) ne_:: Nil
        )(CallMetadata.defaultMlsFun)
      blockBuilder
        .assignScoped(predSym, pred)
        .ifthen(predSym.asSimpleRef, Case.Lit(Tree.BoolLit(true)), AssignField(paths.contTraceValue, lastIdent, paths.contTraceValue, End())(N), N)
        .assignFieldN(paths.contTraceValue, nextIdent, paths.contTraceValue.selN(nextIdent).selN(nextIdent))
        .rest(rest)
    else
      Assign(NoSymbol, Call(paths.popFramePath, Nil ne_:: Nil)(CallMetadata.defaultMlsFun), rest)
  
  private def rtThrowMsg(msg: Str) = Throw(
    Instantiate(mut = false, State.globalThisSymbol.asThis.selN(Tree.Ident("Error")),
    (Value.Lit(Tree.StrLit(msg)).asArg :: Nil) :: Nil)(InstantiateMetadata.empty)
  )
  
  object PureCall:
    def apply(fun: Path, args: List[Path]) = Call(fun, args.map(Arg(N, _)) ne_:: Nil)(CallMetadata.defaultMlsFun)
    def unapply(res: Result) = res match
      case Call(fun, args :: Nil) => args.foldRight[Opt[List[Path]]](S(Nil)): (arg, acc) =>
          acc.flatMap: acc =>
            arg match
              case Arg(N, p) => S(p :: acc)
              case _ => N
        .map((fun, _))
      case _ => N
  
  object CombinedStateTransition:
    def apply(uid: StateId) = PreStateTransition(uid, N, StateTransition(uid, false))
  
  object PreStateTransition:
    private val transitionSymbol = freshTmp("preTransition")
    def apply(uid: StateId, oldUid: Opt[StateId], rest: Block) = 
      val args = oldUid match
        case Some(value) => List(Value.Lit(Tree.IntLit(uid)), Value.Lit(Tree.IntLit(value)))
        case None => List(Value.Lit(Tree.IntLit(uid)))
      Assign(NoSymbol, PureCall(transitionSymbol.asSimpleRef, args), rest)
    def unapply(blk: Block): Option[(StateId, Opt[StateId], Block)] = blk match
      case Assign(NoSymbol, PureCall(Value.SimpleRef(`transitionSymbol`), args), rest) => args match
        case Value.Lit(Tree.IntLit(uid)) :: Value.Lit(Tree.IntLit(oldUid)) :: Nil => S(uid, S(oldUid), rest)
        case Value.Lit(Tree.IntLit(uid)) :: Nil => S(uid, N, rest)
        case _ => N
      case _ => N
  
  extension (k: Block => Block)
    def preStateTransition(uid: StateId, oldUid: Opt[StateId]) = k.chain(PreStateTransition(uid, oldUid, _))
  
  object StateTransition:
    private val transitionSymbol = freshTmp("transition")
    def apply(uid: StateId, resetOld: Bool) =
      Return(PureCall(transitionSymbol.asSimpleRef, List(Value.Lit(Tree.IntLit(uid)), Value.Lit(Tree.BoolLit(resetOld)))))
    def unapply(blk: Block) = blk match
      case Return(PureCall(Value.SimpleRef(`transitionSymbol`), List(Value.Lit(Tree.IntLit(uid)), Value.Lit(Tree.BoolLit(resetOld))))) =>
        S(uid, resetOld)
      case _ => N

  object Unwind:
    private val unwindSymbol = freshTmp("unwind")
    def apply(uid: StateId, loc: Value) =
      Return(PureCall(unwindSymbol.asSimpleRef, List(Value.Lit(Tree.IntLit(uid)), loc)))
    def unapply(blk: Block) = blk match
      case Return(PureCall(Value.SimpleRef(`unwindSymbol`), List(Value.Lit(Tree.IntLit(uid)), loc: Value))) =>
        S(uid, loc)
      case _ => N

  abstract class LazyId extends Lazy[StateId]:
    def isUsed: Bool = !isEmpty
    def transitionOrBlk(blk: => Block) =
      if isEmpty then blk else CombinedStateTransition(force_!)
  
  private class IdAllocator:
    var id: Int = 0
    def apply() =
      val tmp = id
      id += 1
      tmp
    def peek() = id
  
  // blk: the block of code within this state
  private case class BlockPartition(blk: Block, resumable: Bool)
  private case class PartitionedBlock(
    entry: StateId,
    states: Map[StateId, BlockPartition],
    allocId: IdAllocator,
    needsStackSafety: Bool,
    containsError: Bool
  )
  
  private def partitionBlock(blk: Block)(using hRes: HandlerAnalysisRes): PartitionedBlock =
    val result = mutable.HashMap.empty[StateId, BlockPartition]
    val labelIds = mutable.HashMap.empty[LabelSymbol, (LazyId, LazyId)]
    val allocId = new IdAllocator()
    var needsStackSafety = false
    var containsError = false

    // * blk: The block to transform
    // * partitioned: whether we are already in a partitioned state
    // *              if we are not partitioned, we do not need to jump to afterEnd,
    // *              this is because we are still in the original block, which shares
    // *              the same code path.
    // * labelIds: maps label IDs to the state at the start of the label and the state after the label
    // * afterEnd: The block that follows End, None if the function ends.
    def go(blk: Block)(using afterEnd: Option[LazyId], partitioned: Bool): Block = boundary:
      // First check if the current block contain any non trivial call, if so we need a partition

      def forceId(blk: Block, resumable: Bool, forceAlloc: Bool): StateId = blk match
        // TODO: is this correct with the two kinds of state transitions?
        case StateTransition(uid, _) if result.contains(uid) && !forceAlloc =>
          if !result(uid).resumable && resumable then
            result(uid) = BlockPartition(result(uid).blk, true)
          uid
        case PreStateTransition(uid, _, StateTransition(uid1, _)) if uid === uid1 && result.contains(uid) && !forceAlloc =>
          if !result(uid).resumable && resumable then
            result(uid) = BlockPartition(result(uid).blk, true)
          uid
        case _ =>
          val id = allocId()
          result(id) = BlockPartition(blk, resumable)
          id
      
      def doNewRetryablePartition(res: Result, rst: Block): Nothing =
        // return doNewEffectPartition(res: Result, rst: Block)
        // TODO: stack safety global vars
        val stateId = forceId(go(rst)(using partitioned = true), true, false)
        val retryBlock = blockBuilder
          .preStateTransition(stateId, S(allocId.peek()))
          .assignFieldN(paths.runtimePath, paths.resumeValueIdent, res)
          .rest(StateTransition(stateId, true))
        val retryId = forceId(retryBlock, true, true)
        val newBlock = CombinedStateTransition(retryId)
        boundary.break(newBlock)
      def doNewEffectPartition(res: Result, rst: Block) =
        val stateId = forceId(go(rst)(using partitioned = true), true, false)
        val newBlock = blockBuilder
          .preStateTransition(stateId, N)
          .assignFieldN(paths.runtimePath, paths.resumeValueIdent, res)
          .rest(StateTransition(stateId, false))
        boundary.break(newBlock)
      class RestLazyId(rst: Block) extends LazyId:
        def compute: StateId = forceId(go(rst)(using partitioned = true), false, false)
        def transitionSoft: Block = transitionOrBlk(go(rst))
      
      def isKnownCall(sym: DefinitionSymbol[?], args: List[List[Arg]]) =
        hRes.results.get(sym) match
          case Some(argsLen) if args.size === argsLen => true
          case _ => false
      val nonTrivialBlockChecker = new BlockDataTransformer(SymbolSubst.Id):
        override def applyBlock(b: Block) = b match
          // Special handling for tail calls.
          // For tail calls to a non-inlined function, we put the current frame in a global variable.
          // This global variable is cleared after returning from a non-tail-call.
          // If the non-inlined function stack overflows, then we append that frame to the continuation trace
          // in the runtime. This way, we can preserve this tail call.
          case Return(c @ Call(fun, args)) =>
            needsStackSafety = true
            if !config.stackSafety.isDefined then b else
            fun match
              // TODO: do not preserve the tail call for now
              case Value.MemberRef(_, dsym) => if isKnownCall(dsym, args) then b else applyResult(c)(Return(_)) // Prevents the recursion into applyResult
              case _ => applyResult(c)(Return(_))
          case _ => super.applyBlock(b)
        override def applyResult(r: Result)(k: Result => Block) =
          def fallback = doNewRetryablePartition(r, k(paths.resumeValue))
          // check if the call is fully applied
          def doCall(sym: DefinitionSymbol[?], args: List[List[Arg]]) =
            if isKnownCall(sym, args) then doNewEffectPartition(r, k(paths.resumeValue))
            else fallback
          val enterHandleBlockPath = paths.enterHandleBlockPath
          r match
          case Call(`enterHandleBlockPath`, _) => // explicitly handle this case
            needsStackSafety = true
            fallback
          case r @ EffectfulResult() =>
            needsStackSafety = true
            if !config.stackSafety.isDefined then doNewEffectPartition(r, k(paths.resumeValue)) else r match
              case Call(Value.MemberRef(_, dsym), args) => doCall(dsym, args)
              case Call(s: Select, args) => s.symbol match
                case Some(sym) => doCall(sym, args)
                case None => fallback
              case _ => fallback
          case Call(Value.SimpleRef(_: BuiltinSymbol), _) => super.applyResult(r)(k)
          case _: Call =>
            needsStackSafety = true
            fallback
          case _ => super.applyResult(r)(k)
      
      // If current block contains direct effectful result the following call will early exit.
      nonTrivialBlockChecker.applyBlock(blk)

      blk match

      case Match(scrut, arms, dflt, rest) =>
        val restId = RestLazyId(rest)
        val newArms = arms.map((cse, blkk) => (cse, go(blkk)(using afterEnd = S(restId))))
        val newDflt = dflt.map(blkk => go(blkk)(using afterEnd = S(restId)))
        Match(scrut, newArms, newDflt, restId.transitionSoft)

      case Label(label, loop, body, rest) =>
        val restId = RestLazyId(rest)
        val startId = new LazyId:
          def compute = allocId()
        labelIds(label) = (startId, restId)
        val newBody = go(body)(using S(restId))
        if startId.isUsed then
          // We break down the label, and force the usage of rest so that all Break will be rewritten later
          result(startId.force_!) = BlockPartition(Begin(newBody, CombinedStateTransition(restId.force_!)), false)
          CombinedStateTransition(startId.force_!)
        else
          Label(label, loop, newBody, restId.transitionSoft)

      case Break(label) =>
        val (start, end) = labelIds.get(label) match
          case N => raise(InternalError(
            msg"Could not find label '${label.nme}'" ->
            label.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
            return blk
          case S(value) => value
        if partitioned then
          CombinedStateTransition(end.force_!)
        else
          // We might still need to do a StateTransition if the label is broken down.
          // This is done afterwards in a replacement pass.
          Break(label)

      case Continue(label) =>
        val (start, end) = labelIds.get(label) match
          case N => raise(InternalError(
            msg"Could not find label '${label.nme}'" ->
            label.toLoc :: Nil,
            source = Diagnostic.Source.Compilation))
            return blk
          case S(value) => value
        if partitioned then
          CombinedStateTransition(start.force_!)
        else
          // Same as above.
          Continue(label)

      case Begin(sub, rest) =>
        val restId = RestLazyId(rest)
        val newSub = go(sub)(using afterEnd = S(restId))
        Begin(newSub, restId.transitionSoft)

      case u: Unreachable => u
      
      case End(_) =>
        if partitioned then
          afterEnd.fold(blk)(id => CombinedStateTransition(id.force_!))
        else
          blk

      // identity cases

      case Define(defn, rest) => Define(defn, go(rest))
      case Assign(lhs, rhs, rest) => Assign(lhs, rhs, go(rest))
      case blk @ AssignField(lhs, nme, rhs, rest) => AssignField(lhs, nme, rhs, go(rest))(blk.symbol)
      case AssignDynField(lhs, fld, arrayIdx, rhs, rest) => AssignDynField(lhs, fld, arrayIdx, rhs, go(rest))
      case _: Return => blk

      // ignored cases
      case TryBlock(sub, finallyDo, rest) =>
        containsError = true
        Lowering.fail(ErrorReport(
          msg"`try`-`finally` blocks are not currently supported with effect handlers enabled." ->
          N :: Nil,
          source = Diagnostic.Source.Compilation))
      case Throw(_) => blk
      case Scoped(_, body) => go(body) // PreHandlerLowering

    val initId = allocId()
    // Note: initial part will only be resumed if stack safety is on.
    val initPart = BlockPartition(go(blk)(using N, false), opt.stackSafety.isDefined)
    result(initId) = initPart

    val replaceStaleLabels = new BlockTransformerShallow(SymbolSubst.Id):
      override def applyBlock(b: Block): Block = b match
        case Break(label) if labelIds(label)._2.isUsed => CombinedStateTransition(labelIds(label)._2.force_!)
        case Continue(label) if labelIds(label)._1.isUsed => CombinedStateTransition(labelIds(label)._1.force_!)
        case _ => super.applyBlock(b)
    val newMap = Map.from(result.map: (id, part) =>
      id -> BlockPartition(replaceStaleLabels.applyBlock(part.blk), part.resumable))
    PartitionedBlock(initId, newMap, allocId, needsStackSafety, containsError)

  private def computeRestoreList(parts: PartitionedBlock)(using ctx: FunctionCtx): List[LocalVarSymbol] =
    // We compute the restore list by taking the union of live variables at each resumption point
    // The live variable analysis uses a classic work list approach
    val locals = ctx.resumeInfo.currentLocals

    val localSetMap = locals.zipWithIndex.toMap
    val allocId = parts.allocId

    type PartitionVarInfo = (used: mutable.BitSet, assigned: mutable.BitSet, outgoing: List[StateId])
    val states = mutable.HashMap.from(parts.states)
    val labelMap = mutable.HashMap.empty[LabelSymbol, (StateId, StateId)]

    def createState(blk: Block): StateId =
      val newId = allocId()
      states(newId) = BlockPartition(blk, false)
      newId

    def computeVarInfo(blk: Block): PartitionVarInfo =
      // Variables that are assigned in the block
      val assigned = mutable.BitSet.empty
      // Variables that are used before any assignment in the block, which means they must be live
      val used = mutable.BitSet.empty
      val outgoing = mutable.HashSet.empty[StateId]

      def assignToSym(l: LocalVarSymbol) =
        localSetMap.get(l).foreach: idx =>
          assigned += idx

      new BlockTraverserShallow():
        applyBlock(blk)
        override def applyBlock(b: Block): Unit = b match
          case Unwind(uid, loc) => ()
          case StateTransition(uid, _) =>
            outgoing += uid
          case Match(scrut, arms, dflt, rest) =>
            applyPath(scrut)
            val restId = createState(rest)
            arms.foreach: arm =>
              val newId = createState(Begin(arm._2, StateTransition(restId, false)))
              outgoing += newId
            dflt match
              case N => outgoing += restId
              case S(blk) =>
                outgoing += createState(Begin(blk, StateTransition(restId, false)))
          case Label(label, loop, body, rest) =>
            val restId = createState(rest)
            val bodyId = createState(Begin(body, StateTransition(restId, false)))
            labelMap(label) = (bodyId, restId)
            outgoing += bodyId
          case Break(label) =>
            outgoing += labelMap(label)._2
          case Continue(label) =>
            outgoing += labelMap(label)._1
          case Assign(lhs, rhs, rest) =>
            applyResult(rhs)
            lhs match
            case lhs: LocalVarSymbol => assignToSym(lhs)
            case NoSymbol =>
            applyBlock(rest)
          case Define(defn: ValDefn, rest) =>
            applyPath(defn.rhs)
            applyBlock(rest)
          case Define(defn, rest) =>
            applyBlock(rest)
          case _ => super.applyBlock(b)
        override def applySymbol(sym: Symbol): Unit =
          sym match
          case sym: LocalVarSymbol =>
            localSetMap.get(sym).foreach: idx =>
              if !assigned.contains(idx) then
                used += idx
          case _ =>

      (used, assigned, outgoing.toList)

    val worklist = mutable.Queue.empty[StateId]
    val worklistSet = mutable.Set.empty[StateId]
    val stateInfo = mutable.HashMap.empty[StateId, (live: mutable.BitSet, varInfo: PartitionVarInfo, incoming: mutable.ArrayBuffer[StateId])]

    def traverse(id: StateId): Unit =
      if stateInfo.contains(id) then return ()
      val info = computeVarInfo(states(id).blk)
      stateInfo(id) = (mutable.BitSet.empty, info, mutable.ArrayBuffer.empty)
      info.outgoing.foreach: entry =>
        traverse(entry)
        stateInfo(entry).incoming += id
      worklist.enqueue(id)
      worklistSet += id

    traverse(parts.entry)

    while worklist.nonEmpty do
      val cur = worklist.dequeue()
      worklistSet -= cur
      val info = stateInfo(cur)
      val newLive = info.varInfo.outgoing
        .map: entry =>
          stateInfo(entry).live
        .fold(mutable.BitSet.empty)(_ | _).diff(info.varInfo.assigned) | info.varInfo.used
      if newLive != info.live then
        stateInfo(cur).live |= newLive
        stateInfo(cur).incoming.foreach: id =>
          if !worklistSet.contains(id) then
            worklist.enqueue(id)
            worklistSet += id

    parts.states
      .flatMap: (id, part) =>
        if !part.resumable then N
        else
          S(stateInfo.get(id).fold(mutable.BitSet.empty)(_.live))
      .fold(mutable.BitSet.empty)(_ | _)
      .toList
      .map(locals(_))

  private def computeEdges(parts: PartitionedBlock): Map[StateId, List[StateId]] =
    val edges = mutable.ListBuffer.empty[(StateId, StateId)]
    def findEdges(uid: StateId, b: Block) =
      new BlockTraverser:
        override def applyBlock(b: Block): Unit = b match
          case StateTransition(uid2, _) => edges.addOne((uid, uid2))
          case _ => super.applyBlock(b)
        applyBlock(b)
    for (uid, blk) <- parts.states do
      findEdges(uid, blk.blk)
    edges.groupBy(_._1).map:
      case uid -> ids => uid -> ids.map:
          case (a, b) => b
        .toList
        .distinct
  
  // Denotes whether a block transitions to another state only on the outer level,
  // i.e. should return false iff there is a state transition within an if, label, etc.
  // A precondition is that the state corresponding to the input block has an out-degree
  // of 1. This means if a state transition cannot be found on the outer level, there
  // must be a state transition within another construct and should return false.
  @tailrec
  private def isSimpleTransition(b: Block): Bool = b match
    case StateTransition(uid) => true
    case b: NonBlockTail => isSimpleTransition(b.rest)
    case _: BlockTail => false

  // Given a directed graph, computes the "straight line" segments of the graph, i.e. partitions it
  // into segments such that the out-degree of all elements in each segment is 1, except
  // for the last element. Note that the partitioning is not necessarily unique and this does
  // not necessarily produce a "maximal" partitioning. (I actually suspect that producing a
  // maximal partitioning is NP-hard...)
  //
  // I do have some ideas to improve this though, but those can be done later.
  private def computeStraightLines(entry: StateId, edges: Map[StateId, List[StateId]]): List[List[StateId]] =
    val visited = mutable.HashSet.empty[StateId]
    val ret = mutable.ListBuffer.empty[List[StateId]]
    // Algorithm: Perform a DFS and accumulate the current straight-line segment as we visit nodes.
    // Once we reach a node that has an out degree of != 1, we end the current straight line segment.
    def dfs(state: StateId, acc: List[StateId]): Unit =
      var curAcc = acc
      def concludeSegment =
        ret.addOne(curAcc)
        curAcc = List.empty
      if !visited.contains(state) then
        // Not yet visited: Add this node to the current segment.
        curAcc = state :: curAcc
        visited.add(state)
        edges.get(state) match
        case Some(nexts) =>
          // If this state has an out degree of != 1, then end the current segment.
          if nexts.size != 1 then
            concludeSegment
          for n <- nexts do dfs(n, curAcc)
        case None => concludeSegment
      // If this state was visited from a node u with an out-degree of 1, but this state
      // has already been previously visited, then we must conclude the current segment,
      // ending at the node u.
      else if !curAcc.isEmpty then
        concludeSegment
    dfs(entry, List.empty)
    ret.sortBy(x => x.headOption.getOrElse(BigInt(-1))).toList

  private def lifterReport(using Line, FileName)(msgs: Ls[Message -> Opt[Loc]])(using Name) =
    if opt.softLifterError then
      WarningReport(msgs, source = Diagnostic.Source.Compilation)
    else
      InternalError(msgs, source = Diagnostic.Source.Compilation)

  /**
   * The actual translation:
   * 1. rewrite handler blocks in terms of classes and functions (directly during Lowering)
   * 2. class lifter
   * 3. state machine transformation of all functions (HandlerLowering, this class)
   *    a) translate nested definition (pre translate)
   *    b) partitioning
   *    c) translate code in current block (post translate)
   */
  
  case class VarsArrayInfo(mp: Map[LocalVarSymbol, Int]):
    def select(varClassPath: Path)(local: LocalVarSymbol) =
      DynSelect(varClassPath, Value.Lit(Tree.IntLit(mp(local))), true)
    def assign(varClassPath: Path)(local: LocalVarSymbol, value: Result, rest: Block) =
      AssignDynField(varClassPath, Value.Lit(Tree.IntLit(mp(local))), true, value, rest)
    def instantiate =
      val inv = mp.toList.iterator.map((a, b) => (b, a)).toMap
      val pcArg = Value.Lit(Tree.IntLit(0)).asArg
      val args = pcArg :: (1 until mp.size + 1).map(inv(_).asPath.asArg).toList
      Tuple(true, args)
    def readPc(varClassPath: Path) = DynSelect(varClassPath, Value.Lit(Tree.IntLit(0)), true)
    def assignPc(varClassPath: Path)(value: Path, rest: Block) = AssignDynField(varClassPath, Value.Lit(Tree.IntLit(0)), true, value, rest)
    
  private def createVarClass(nme: String, vars: Iterable[LocalVarSymbol]): VarsArrayInfo =
    val mp = vars.toArray.sortBy(_.uid).zipWithIndex.map:
        case (sym, idx) => (sym, idx + 1)
      .toMap
    VarsArrayInfo(mp)
  
  private val extraDefns: ListBuffer[Defn] = ListBuffer()

  private def translateBlock(nme: String, blk: Block, h: HandlerCtx, scopedVars: collection.Set[ScopedSymbol], extraRestoreVars: List[LocalVarSymbol])(using HandlerAnalysisRes): Block =
    given HandlerCtx = h

    def translateFunLike(fun: FunDefn, funcPath: Path, thisPath: Option[Path], debugNme: Str) =
      val scopedVars = fun.body.scopedVars
      val varList = scopedVars.collect:
        case sym: LocalVarSymbol => sym
      val sortedVars = varList.toList.sortBy(_.uid)
      val debugInfo = Value.Lit(Tree.StrLit(debugNme)).asArg :: sortedVars.zipWithIndex.filter(_._1.isInstanceOf[VarSymbol])
        .flatMap: (sym, idx) =>
          List(intLit(idx), Value.Lit(Tree.StrLit(sym.nme)))
        .map(_.asArg)
      val debugInfoSym = freshTmp(s"$debugNme$$debugInfo")
      // TODO: properly support spread argument by calculating the correct length.
      val rtArgLists = intLit(fun.params.length) :: fun.params.flatMap: pl =>
        intLit(pl.params.length) :: pl.params.map(p => p.sym.asSimpleRef)
      val newCtx = HandlerCtx.FunctionLike(FunctionCtx(funcPath, thisPath, ResumeInfo(rtArgLists, sortedVars, L(fun.sym)),
        DebugInfo(debugNme, if opt.debug then debugInfoSym.asSimpleRef else unit), thisPath.isDefined && fun.params.isEmpty))
      val bod2 = translateBlock(fun.dSym.nme, fun.body, newCtx, scopedVars, fun.params.flatMap(_.paramSyms))
      val fun2 = if fun.body is bod2 then fun else
        FunDefn(fun.owner, fun.sym, fun.dSym, fun.params, bod2)(fun.configOverride, Annot.Inline :: fun.annotations)
      (debugInfoSym, debugInfo, fun2)

    // transform inner function/class and effect handler intrinsics to the runtime functions.
    val preTransform = new BlockTransformer(SymbolSubst.Id):
      override def applyResult(r: Result)(k: Result => Block): Block = r match
        case Call(Value.MemberRef(sym, _), args) if sym is Elaborator.ctx.builtins.runtime.suspend =>
          k(Call(paths.mkEffectPath, args)(CallMetadata.mlsFunWithEffect))
        case Call(Value.MemberRef(sym, _), args) if sym is Elaborator.ctx.builtins.runtime.handle_suspension =>
          k(Call(paths.enterHandleBlockPath, args)(CallMetadata.mlsFunWithEffect))
        case _ => super.applyResult(r)(k)
      override def applyDefn(defn: Defn)(k: Defn => Block): Block = defn match
        case fun: FunDefn =>
          if h.currentBlockIsTrulyNested then
            raise(lifterReport(msg"Unexpected nested function: lambdas may not function correctly." -> fun.sym.toLoc :: Nil))
          val (debugInfoSym, debugInfo, fun2) = translateFunLike(fun, fun.sym.asMemberRef(fun.dSym), N, fun.sym.nme)
          if opt.debug then Scoped(Set.single(debugInfoSym), Assign(debugInfoSym, Tuple(false, debugInfo), k(fun2))) else k(fun2)
        case defn @ ClsLikeDefn(owner, isym, sym, ctorSym, kind, paramsOpt, auxParams, parentPath, methods, privateFields, publicFields, preCtor, ctor, companion, bufferable) =>
          if h.currentBlockIsTrulyNested then
            raise(lifterReport(msg"Unexpected nested class: lambdas may not function correctly." -> isym.toLoc :: Nil))
          val debugInfos = mutable.ArrayBuffer.empty[(TempSymbol, List[Arg])]
          val newMtds = methods.map: f =>
            val (debugInfoSym, debugInfo, fun2) = translateFunLike(f, isym.asThis.sel(new Tree.Ident(f.sym.nme), f.dSym),
              S(isym.asThis), s"${sym.nme}#${f.sym.nme}")
            debugInfos += debugInfoSym -> debugInfo
            fun2
          val companion2 = companion.map: bod =>
            val newMtds = bod.methods.map: f =>
              val (debugInfoSym, debugInfo, fun2) = translateFunLike(f, bod.isym.asThis.sel(new Tree.Ident(f.sym.nme), f.dSym),
                S(bod.isym.asThis), s"${sym.nme}.${f.sym.nme}")
              debugInfos += debugInfoSym -> debugInfo
              fun2
            // We cannot use this bc there is no subblock transform...
            // val newCtor = translateTrivialOrTopLevel(bod.ctor)
            // TODO: Companion's ctor is more well behaved so it is possible to handle it
            // However, JSBuilder inserts extra statements between preCtor and ctor and it's not possible to replicate the exact behavior
            // without many special handling.
            val newCtor = if opt.doNotInstrumentTopLevelModCtor && !h.currentBlockIsTrulyNested then bod.ctor else
              translateCtorLike(bod.ctor, bod.isym.asThis, true)
            tl.log(s"companion name: ${bod.isym.nme}")
            ClsLikeBody(bod.isym, newMtds, bod.privateFields, bod.publicFields, newCtor, bod.annotations)
          val c2 = ClsLikeDefn(owner, isym, sym, ctorSym, kind, paramsOpt, auxParams, parentPath, newMtds, privateFields, publicFields,
            translateCtorLike(preCtor, isym.asThis, false), translateCtorLike(ctor, isym.asThis, false), companion2, bufferable)(defn.configOverride, defn.annotations)
          if opt.debug then
            Scoped(debugInfos.map(_._1).toSet, debugInfos.foldRight(k(c2)): (elem, blk) =>
              Assign(elem._1, Tuple(false, elem._2), blk))
          else k(c2)
        case _ => super.applyDefn(defn)(k)
    val b = preTransform.applyBlock(blk)
    if !h.currentBlockIsTrulyNested then
      return postTranslateTopLevelCtx(b)
    if h.inCtor then
      return postTranslateIllegalEffectCtx(b, "in a constructor")
    val ctx = h.asInstanceOf[HandlerCtx.FunctionLike].ctx
    if ctx.inGetter then
      return postTranslateIllegalEffectCtx(b, "in a getter")
    given FunctionCtx = ctx
    val parts = partitionBlock(b)
    val needsStackSafety = parts.needsStackSafety && opt.stackSafety.isDefined
    val oneState = parts.states.size <= 1
    if oneState && !parts.containsError && !needsStackSafety then
      return b
    val vars = extraRestoreVars ::: (if opt.debug then ctx.resumeInfo.currentLocals else computeRestoreList(parts))
    val varsSet = vars.toSet
    
    val varClsInfo = createVarClass("VarsClass$" + nme, vars)
    val varsClsSym = VarSymbol(Tree.Ident(nme + "$varsClass"))
    
    val pcVar = VarSymbol(Tree.Ident("pc"))
    
    val pcPath = pcVar.asPath
    val pcAssign_ = varClsInfo.assignPc(varsClsSym.asPath)
    def pcAssign(value: Path, rest: Block) =
      Assign(pcVar, value, rest)
    def prePcAssign(value: Path, oldUid: Opt[Path], rest: Block) =
      oldUid match
        case Some(oldValue) => blockBuilder
          .assignFieldN(paths.runtimePath, paths.oldPcIdent, oldValue)
          .rest(pcAssign_(value, rest))
        case None => pcAssign_(value, rest)
    
    val curDepth = freshTmp("curDepth")
    val mainLoopLbl = freshLabel("main")

    val edges = computeEdges(parts)
    val straightLines = computeStraightLines(parts.entry, edges)
    
    def varRewriter(varsInfo: VarsArrayInfo, varsClsSym: LocalVarSymbol) =
      val sel = varsInfo.select(varsClsSym.asPath)
      val assign = varsInfo.assign(varsClsSym.asPath)
      new BlockTransformerShallow(SymbolSubst.Id):
        override def applyPath(p: Path)(k: Path => Block): Block = p match
          case Value.SimpleRef(sym: LocalVarSymbol) => if varsSet.contains(sym) then k(sel(sym)) else super.applyPath(p)(k)
          case _ => super.applyPath(p)(k)
        override def applyBlock(b: Block): Block = b match
          case Assign(s: LocalVarSymbol, rhs, rest) => 
            if varsSet.contains(s) then applyResult(rhs): newRhs =>
              assign(s, newRhs, applyBlock(rest))
            else super.applyBlock(b)
          case _ => super.applyBlock(b)

    def postTransform(transition: BigInt => Block) = new BlockTransformerShallow(SymbolSubst.Id):
      override def applyBlock(b: Block) = b match
        case PreStateTransition(uid, oldUid, rest) =>
          prePcAssign(intLit(uid), oldUid.map(intLit(_)), applyBlock(rest))
        case StateTransition(uid, resetOld) =>
          if resetOld then
            blockBuilder
              .assignFieldN(paths.runtimePath, paths.oldPcIdent, intLit(-1))
              .rest(transition(uid))
          else transition(uid)
        case r: Return => popFrame(r)
        case _ => super.applyBlock(b)
      override def applyResult(r: Result)(k: Result => Block): Block = r match
        case EffectfulResult() if needsStackSafety =>
          AssignField(paths.runtimePath, paths.stackDepthIdent, curDepth.asSimpleRef, super.applyResult(r)(k))(N)
        case _ => super.applyResult(r)(k)
    // The fallback form which always works
    val fallbackPostTransform = postTransform(id => pcAssign(intLit(id), Continue(mainLoopLbl)))
    // Note: `line` has the last state as the head, and the first state at the end
    def straightLineToArms(line: List[StateId]): Block => Block =
      def transformState(state: StateId) =
        val blk = parts.states(state)
        // If the state transition does not appear in tail position on the outer level,
        // we must wrap the transformed state in a label, and jump to that label when
        // encountering a state transition
        val isSimple = isSimpleTransition(blk.blk)
        lazy val lblSym = LabelSymbol(N, "brk" + state.toString())
        val nextState = edges(state).head
        val transform = postTransform: uid =>
          assert(uid === nextState)
          if isSimple then
            pcAssign(Value.Lit(Tree.IntLit(uid)), End())
          else
            Break(lblSym)
        val transformed = transform.applyBlock(blk.blk)
        if isSimple then transformed
        else Label(
          lblSym, false, transformed,
          pcAssign(Value.Lit(Tree.IntLit(nextState)), End())
        )
      line match
        case head :: next =>
          val headTransformed = fallbackPostTransform.applyBlock(parts.states(head).blk)
          val initial: Block => Block = blk =>
            Match(
              pcPath,
              Case.Lit(Tree.IntLit(head)) -> headTransformed :: Nil,
              N,
              blk
            )
          next.foldLeft(initial):
            // Applying this function to a block b will result in b appearing in the tail
            // of the sequence of match blocks
            case (acc, uid) => 
              val transformed = transformState(uid)
              blk =>
              Match(
                pcPath,
                Case.Lit(Tree.IntLit(uid)) -> transformed :: Nil,
                N,
                acc(blk)
              )
        case Nil => id

    var mainBody =
      if oneState then
        fallbackPostTransform.applyBlock(parts.states.head._2.blk)
      else
        val matches = straightLines.map(straightLineToArms).foldLeft[Block](End()):
          case (acc, f) => f(acc)
        Label(mainLoopLbl, true, matches, End())
    
    // worker defn symbols
    val workerDfnBms = BlockMemberSymbol(nme + "$worker", Nil, true)
    val workerDfnSym = TermSymbol(syntax.Fun, N, Tree.Ident(nme + "$worker"))
    
    mainBody = varRewriter(varClsInfo, varsClsSym).applyBlock(mainBody)
    mainBody = Assign(pcVar, varClsInfo.readPc(varsClsSym.asPath), mainBody)
        
    val getSavedTmp = freshTmp("saveOffset")
    def getSaved(off: BigInt): (Block => Block, Path) =
      if off == 0 then
        return (id, DynSelect(paths.runtimePath.selSN("resumeArr"), paths.runtimePath.selSN("resumeIdx"), true))
      val addOne = Assign(getSavedTmp, Call(State.builtinOpsMap("+").asSimpleRef, (paths.runtimePath.selSN("resumeIdx").asArg :: intLit(off).asArg :: Nil) ne_:: Nil)(CallMetadata.defaultFun), _)
      (addOne, DynSelect(paths.runtimePath.selSN("resumeArr"), getSavedTmp.asSimpleRef, true))

    val resumeArrIndexed = DynSelect(paths.runtimePath.selSN("resumeArr"), getSavedTmp.asSimpleRef, true)
    val plus = State.builtinOpsMap("+").asSimpleRef
    
    val extraVars = if needsStackSafety then Set(pcVar, curDepth) else Set.single(pcVar)

    mainBody = Scoped(
      scopedVars ++ extraVars,
      mainBody)
    
    // create worker definition
    val workerDefn = FunDefn(
      N, workerDfnBms, workerDfnSym, PlainParamList(Param.simple(varsClsSym) :: Nil) :: Nil, mainBody
    )(N, Nil)

    val tmp = TempSymbol(N)
    
    extraDefns.addOne(workerDefn)

    var wrapperBod = blockBuilder
      .assignScoped(tmp, varClsInfo.instantiate)
      .chain: blk =>
        pushFrame(Value.MemberRef(workerDfnBms, workerDfnSym), tmp.asPath, blk)
      .ret(Call(workerDefn.asPath, (tmp.asPath.asArg :: Nil) ne_:: Nil)(CallMetadata.defaultMlsFun))
    
    if config.stackSafety.isDefined then
      wrapperBod = AssignField(paths.runtimePath, paths.oldPcIdent, intLit(-1), wrapperBod)(N)
    
    wrapperBod
  
  private def translateCtorLike(b: Block, thisPath: Path, isModCtor: Bool)(using h: HandlerCtx, r: HandlerAnalysisRes): Block =
    translateBlock("ctor", b, if isModCtor then HandlerCtx.ModCtor(h.currentBlockIsTrulyNested) else HandlerCtx.Ctor, Set.empty, List.empty)
    
  /**
   * These functions does not recurse into nested definitions
   */

  private def postTranslateTopLevelCtx(b: Block)(using HandlerCtx): Block =
    postTranslateIllegalEffectCtx(b, Call.raw(paths.topLevelEffectPath, (Value.Lit(Tree.BoolLit(opt.debug)).asArg :: Nil) ne_:: Nil)(CallMetadata.defaultMlsFun), true, opt.stackSafety.map(_.stackLimit))

  private def postTranslateIllegalEffectCtx(b: Block, reason: Str)(using HandlerCtx): Block =
    postTranslateIllegalEffectCtx(b, Call.raw(paths.illegalEffectPath, (Value.Lit(Tree.StrLit(reason)).asArg :: Nil) ne_:: Nil)(CallMetadata.defaultMlsFun), false, N)

  /**
    * Translate the block and apply stack safety wrapper if needed. If needsStackSafety is true,
    * it is assumed that the current block is at top level and lambda definition will be created for each call
    */
  private def postTranslateIllegalEffectCtx(b: Block, onEffect: Call, isTopLevel: Bool, needsStackSafety: Opt[Int])(using HandlerCtx): Block =
    def effectCheck(l: Assignable, r: Result, rst: Block): Block =
      val stackLimit: Path = needsStackSafety match
        case Some(value) => intLit(value)
        case None => Value.Lit(Tree.UnitLit(false))
      
      if isTopLevel then
        val bodSym = BlockMemberSymbol("‹effectful body›", Nil, false)
        val bodFun = FunDefn.withFreshSymbol(N, bodSym, ParamList(ParamListFlags.empty, Nil, N) :: Nil, Ret(r))(configOverride = N, annotations = Nil)
        blockBuilder
          .scopedVars(Set.single(bodSym))
          .define(bodFun)
          .assign(l, Call(paths.trampolinePath, (stackLimit.asArg :: Value.MemberRef(bodSym, bodFun.dSym).asArg :: Nil) ne_:: Nil)(CallMetadata.defaultMlsFun))
          .rest(rst)
      else
        rst
    val topLevelPostTransform = new BlockTransformerShallow(SymbolSubst.Id):
      override def applyBlock(b: Block) = b match
        case Assign(lhs, r @ EffectfulResult(), rest) =>
          // Optimization to reuse lhs instead of fresh local
          effectCheck(lhs, r, applyBlock(rest))
        case _ => super.applyBlock(b)
      override def applyResult(r: Result)(k: Result => Block) = r match
        case r @ EffectfulResult() =>
          // Fallback case, this may lead to unnecessary assignments if it is assign-like
          val l = freshTmp()
          Scoped(Set(l), effectCheck(l, r, k(l.asSimpleRef)))
        case _ => super.applyResult(r)(k)
    topLevelPostTransform.applyBlock(b)
  
  // conservatively find list of functions that will have the wrapper
  // must be sound, i.e. if the function is found by this analysis, then it must be a wrapper that is inlined
  def analyze(b: Block): HandlerAnalysisRes =
    if !config.stackSafety.isDefined then return HandlerAnalysisRes(Map.empty)
    var m: mutable.Map[TermSymbol, Int] = mutable.Map.empty
    def isBlkTrivial(b: Block) = boundary:
      new BlockTraverserShallow():
        override def applyResult(r: Result): Unit = r match
          case EffectfulResult() => boundary.break(false)
          case Call(Value.SimpleRef(_: BuiltinSymbol), _) => super.applyResult(r)
          case _: Call => boundary.break(false)
          case _ => super.applyResult(r)
        applyBlock(b)
      true
    new BlockTraverser():
      override def applyFunDefn(fun: FunDefn): Unit =
        // TODO: if the fun is owned by a class or a module, should we skip it?
        if !isBlkTrivial(fun.body) then m.addOne(fun.dSym -> Math.min(fun.params.size, 1))
        super.applyFunDefn(fun)
      applyBlock(b)
    HandlerAnalysisRes(m.toMap)
    

  def translateProgram(prog: Program): Program =
    extraDefns.clear()
    val ctx = HandlerCtx.TopLevel
    given HandlerAnalysisRes = analyze(prog.main)
    var transformed = blockBuilder
        .staticif(
          !opt.doNotInstrumentTopLevelModCtor,
          _.assign(NoSymbol, Call(paths.resetEffects, Nil ne_:: Nil)(CallMetadata.defaultMlsFun))
        )
        .rest(translateBlock("main", prog.main, ctx, Set.empty, List.empty))
    transformed = extraDefns.foldLeft(transformed):
      case (acc, dfn) => Define(dfn, acc)
    transformed = Scoped(extraDefns.map(_.sym).toSet, transformed)
    if transformed is prog.main then prog
    else
      Program(
        prog.imports,
        transformed
      )
