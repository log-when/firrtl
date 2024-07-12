// SPDX-License-Identifier: Apache-2.0
// Author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package firrtl.backends.experimental.smt

import firrtl.annotations.{Target, ReferenceTarget, MemoryInitAnnotation, NoTargetAnnotation, PresetRegAnnotation}
import firrtl._
import firrtl.ir._
import firrtl.backends.experimental.smt.random._
import firrtl.options.Dependency
import firrtl.passes.MemPortUtils.memPortField
import firrtl.passes.PassException
import firrtl.passes.memlib.VerilogMemDelays
import firrtl.stage.Forms
import firrtl.stage.TransformManager.TransformDependency
import firrtl.transforms.{EnsureNamedStatements, PropagatePresetAnnotations}
import logger.LazyLogging

import scala.collection.mutable
import chiseltest.formal._
import sys.process._ 
import jhoafparser.parser.HOAFParser
import firrtl.analyses._

case class TransitionSystemAnnotation(sys: TransitionSystem) extends NoTargetAnnotation

/** Contains code to convert a flat firrtl module into a functional transition system which
  * can then be exported as SMTLib or Btor2 file.
  */
object FirrtlToTransitionSystem extends Transform with DependencyAPIMigration {
  //VerilogMemDelays we want to trace the renaming of the registers created my the mem delay pass, I haven't gotten it now, I will see.
  override def prerequisites: Seq[Dependency[Transform]] = Forms.LowForm ++
    Seq(
      Dependency(VerilogMemDelays),
      Dependency(EnsureNamedStatements), // this is required to give assert/assume statements good names
      Dependency[PropagatePresetAnnotations]
    )
  override def invalidates(a: Transform): Boolean = false
  // since this pass only runs on the main module, inlining needs to happen before
  override def optionalPrerequisites: Seq[TransformDependency] = Seq(Dependency[firrtl.passes.InlineInstances])

  override protected def execute(state: CircuitState): CircuitState = {
    // Maybe Death Code Elimination has elimated some codes which are irrivalent with assertion and output.
    val circuit = state.circuit

    // println(circuit)
    val presetRegs = state.annotations.collect {
      case PresetRegAnnotation(target) if target.module == circuit.main => target.ref
    }.toSet

    // in counter, no memory, no non-random memory
    // collect all non-random memory initialization
    val memInit = state.annotations.collect { case a: MemoryInitAnnotation if !a.isRandomInit => a }
      .filter(_.target.module == circuit.main)
      .map(a => a.target.ref -> a.initValue)
      .toMap

    // map module's name to module's firrtl, I think toMap is to make it explicitly
    // module look up table
    val modules = circuit.modules.map(m => m.name -> m).toMap
    
    // in counter, no uninterpreted module annotations, maybe find its meaning later
    // collect uninterpreted module annotations
    val uninterpreted = state.annotations.collect {
      case a: UninterpretedModuleAnnotation =>
        UninterpretedModuleAnnotation.checkModule(modules(a.target.module), a)
        a.target.module -> a
    }.toMap
    
    // println(CHAAnnos.toSeq)
    // ExtModuleException: Generally used for Verilog black boxes
    // see line 34, inlining has happened
    // convert the main module
    val main = modules(circuit.main)
    // println(main)
    // it seems that there are some pretreatments before this
    val sys = main match {
      case _: ir.ExtModule =>
        throw new ExtModuleException(
          "External modules are not supported by the SMT backend. Use yosys if you need to convert Verilog."
        )
      case m: ir.Module =>
        new ModuleToTransitionSystem(presetRegs = presetRegs, memInit = memInit, uninterpreted = uninterpreted).run(m)
    }
    state.copy(circuit = circuit, annotations = state.annotations :+ TransitionSystemAnnotation(TopologicalSort.run(sys)))
  }
}

private object UnsupportedException {
  val HowToRunStuttering: String =
    """
      |You can run the StutteringClockTransform which
      |replaces all clock inputs with a clock enable signal.
      |This is required not only for multi-clock designs, but also to
      |accurately model asynchronous reset which could happen even if there
      |isn't a clock edge.
      | If you are using the firrtl CLI, please add:
      |   -fct firrtl.backends.experimental.smt.StutteringClockTransform
      | If you are calling into firrtl programmatically you can use:
      |   RunFirrtlTransformAnnotation(Dependency[StutteringClockTransform])
      | To designate a clock to be the global_clock (i.e. the simulation tick), use:
      |   GlobalClockAnnotation(CircuitTarget(...).module(...).ref("your_clock")))
      |""".stripMargin
}

private class ExtModuleException(s: String) extends PassException(s)
private class AsyncResetException(s: String) extends PassException(s + UnsupportedException.HowToRunStuttering)
private class MultiClockException(s: String) extends PassException(s + UnsupportedException.HowToRunStuttering)
private class MissingFeatureException(s: String)
    extends PassException("Unfortunately the SMT backend does not yet support: " + s)

private class ModuleToTransitionSystem(
  presetRegs:    Set[String],
  memInit:       Map[String, MemoryInitValue],
  uninterpreted: Map[String, UninterpretedModuleAnnotation])
    extends LazyLogging {

  def run(m: ir.Module): TransitionSystem = {

    // first pass over the module to convert expressions; discover state and I/O
    m.foreachPort(onPort)
    m.foreachStmt(onStatement)

    // multi-clock support requires the StutteringClock transform to be run
    if (clocks.size > 1) {
      throw new MultiClockException(s"The module ${m.name} has more than one clock: ${clocks.mkString(", ")}")
    }

    // generate comments from infos
    val comments = mutable.HashMap[String, String]()
    infos.foreach {
      case (name, info) =>
        val infoStr = info.serialize.trim
        if (infoStr.nonEmpty) {
          val prefix = comments.get(name).map(_ + ", ").getOrElse("")
          comments(name) = prefix + infoStr
        }
    }

    // module info to the comment header
    val header = m.info.serialize.trim

    TransitionSystem(m.name, inputs.toList, states.values.toList, signals.toList, comments.toMap, header)
  }

  //notice these are mutable, and val refers to their reference is unchangable
  private val inputs = mutable.ArrayBuffer[BVSymbol]()
  private val clocks = mutable.ArrayBuffer[String]()
  private val signals = mutable.ArrayBuffer[Signal]()
  private val states = mutable.LinkedHashMap[String, State]()
  private val infos = mutable.ArrayBuffer[(String, ir.Info)]()

  private def onPort(p: ir.Port): Unit = {
    // no details about AsyncResetType
    if (isAsyncReset(p.tpe)) {
      throw new AsyncResetException(s"Found AsyncReset ${p.name}.")
    }
    // matain infos to generate comments in the future
    // if this port is an input, then handle it with its type (clock or general clock)
    infos.append(p.name -> p.info)
    p.direction match {
      case ir.Input =>
        if (isClock(p.tpe)) {
          clocks.append(p.name)
        } else {
          inputs.append(BVSymbol(p.name, bitWidth(p.tpe).toInt))
        }
      case ir.Output =>
    }
  }

  private def onStatement(s: ir.Statement): Unit = s match {
    case DefRandom(info, name, tpe, _, en) =>
      assert(!isClock(tpe), "rand should never be a clock!")
      // we model random sources as inputs and the enable signal as output
      infos.append(name -> info)
      inputs.append(BVSymbol(name, bitWidth(tpe).toInt))
      signals.append(Signal(name + ".en", onExpression(en, 1), IsOutput))
    case w: ir.DefWire =>
      if (!isClock(w.tpe)) {
        // InlineInstances can insert wires without re-running RemoveWires for now we just deal with it when
        // the Wires is connected to (ir.Connect).
      }
    case ir.DefNode(info, name, expr) =>
      if (!isClock(expr.tpe) && !isAsyncReset(expr.tpe)) {
        infos.append(name -> info)
        signals.append(Signal(name, onExpression(expr), IsNode))
      }
    case r: ir.DefRegister =>
      infos.append(r.name -> r.info)
      states(r.name) = onRegister(r)
    case m: ir.DefMemory =>
      // default: disallow bv-blasting
      // infos.append(m.name -> m.info)
      // val memSplitedStates = onMemory(m, true)
      // for(i <- memSplitedStates)
      // {
      //   states(i._1) = i._2
      // }
      states(m.name) = onMemory(m)
    case ir.Connect(info, loc, expr) =>
      if (!isGroundType(loc.tpe)) error("All connects should have been lowered to ground type!")
      if (!isClock(loc.tpe) && !isAsyncReset(expr.tpe)) { // we ignore clock connections
        val name = loc.serialize
        val e = onExpression(expr, bitWidth(loc.tpe).toInt, allowNarrow = false)
        Utils.kind(loc) match {
          case RegKind => states(name) = states(name).copy(next = Some(e))
          // I don't understand... Because submodules have been flattened, we don't need to consider submodule ?
          // But why IsOutput ?
          case PortKind | InstanceKind => // module output or submodule input
            infos.append(name -> info)
            signals.append(Signal(name, e, IsOutput))
          case MemKind | WireKind =>
            // Consider memory later
            // InlineInstances can insert wires without re-running RemoveWires for now we just deal with it.
            // println(s"mem connect, name: ${name}, expr:${e}")
            infos.append(name -> info)
            signals.append(Signal(name, e, IsNode))
        }
      }
    case i: ir.IsInvalid =>
      throw new UnsupportedFeatureException(s"IsInvalid statements are not supported: ${i.serialize}")
    // To See
    case ir.DefInstance(info, name, module, tpe) => 
      // println (s)
      onInstance(info, name, module, tpe)
    case s: ir.Verification =>
      if (s.op == ir.Formal.Cover) {
        logger.info(s"[info] Cover statement was ignored: ${s.serialize}")
      } else {
        val name = s.name
        val predicate = onExpression(s.pred)
        val enabled = onExpression(s.en)
        val e = BVImplies(enabled, predicate)
        infos.append(name -> s.info)
        val signal = if (s.op == ir.Formal.Assert) {
          Signal(name, BVNot(e), IsBad)
        } else {
          Signal(name, e, IsConstraint)
        }
        signals.append(signal)
      }
    case s: ir.Conditionally =>
      error(s"When conditions are not supported. Please run ExpandWhens: ${s.serialize}")
    case s: ir.PartialConnect =>
      error(s"PartialConnects are not supported. Please run ExpandConnects: ${s.serialize}")
    case s: ir.Attach =>
      error(s"Analog wires are not supported in the SMT backend: ${s.serialize}")
    case s: ir.Stop =>
      if (s.ret == 0) {
        logger.info(
          s"[info] Stop statements with a return code of 0 are currently not supported. Ignoring: ${s.serialize}"
        )
      } else {
        // we treat Stop statements with a non-zero exit value as assertions that en will always be false!
        val name = s.name
        infos.append(name -> s.info)
        signals.append(Signal(name, onExpression(s.en), IsBad))
      }
    case s: ir.Print =>
      logger.info(s"Info: ignoring: ${s.serialize}")
    case other => 
      // recursive processing  
      other.foreachStmt(onStatement)
  }

  private def onRegister(r: ir.DefRegister): State = {
    val width = bitWidth(r.tpe).toInt
    val resetExpr = onExpression(r.reset, 1)
    assert(resetExpr == False(), s"Expected reset expression of ${r.name} to be 0, not $resetExpr")
    val initExpr = onExpression(r.init, width)
    val sym = BVSymbol(r.name, width)
    val hasReset = initExpr != sym
    // _resetCount is preset, I think _resetCount has initial expression, others' initialization depends on it, and use next to express
    val isPreset = presetRegs.contains(r.name)
    assert(!isPreset || hasReset, s"Expected preset register ${r.name} to have a reset value, not just $initExpr!")
    val state = State(sym, if (isPreset) Some(initExpr) else None, None)
    state
  }

  private def onInstance(info: ir.Info, name: String, module: String, tpe: ir.Type): Unit = {
    if (!tpe.isInstanceOf[ir.BundleType]) error(s"Instance $name of $module has an invalid type: ${tpe.serialize}")
    if (uninterpreted.contains(module)) {
      onUninterpretedInstance(info: ir.Info, name: String, module: String, tpe: ir.Type)
    } else {
      // We treat all instances that aren't annotated as uninterpreted as blackboxes
      // this means that their outputs could be any value, no matter what their inputs are.
      logger.warn(
        s"WARN: treating instance $name of $module as blackbox. " +
          "Please flatten your hierarchy if you want to include submodules in the formal model."
      )
      val ports = tpe.asInstanceOf[ir.BundleType].fields
      // skip async reset ports
      ports.filterNot(p => isAsyncReset(p.tpe)).foreach { p =>
        if (!p.tpe.isInstanceOf[ir.GroundType]) error(s"Instance $name of $module has an invalid port type: $p")
        val isOutput = p.flip == ir.Default
        val pName = name + "." + p.name
        infos.append(pName -> info)
        // outputs of the submodule become inputs to our module
        if (isOutput) {
          if (isClock(p.tpe)) {
            clocks.append(pName)
          } else {
            inputs.append(BVSymbol(pName, bitWidth(p.tpe).toInt))
          }
        }
      }
    }
  }

  private def onUninterpretedInstance(info: ir.Info, instanceName: String, module: String, tpe: ir.Type): Unit = {
    val anno = uninterpreted(module)

    // sanity checks for ports were done already using the UninterpretedModule.checkModule function
    val ports = tpe.asInstanceOf[ir.BundleType].fields

    val outputs = ports.filter(_.flip == ir.Default).map(p => BVSymbol(p.name, bitWidth(p.tpe).toInt))
    val inputs = ports.filterNot(_.flip == ir.Default).map(p => BVSymbol(p.name, bitWidth(p.tpe).toInt))

    assert(anno.stateBits == 0, "TODO: implement support for uninterpreted stateful modules!")

    // for state-less (i.e. combinatorial) circuits, the outputs only depend on the inputs
    val args = inputs.map(i => BVSymbol(instanceName + "." + i.name, i.width)).toList
    outputs.foreach { out =>
      val functionName = anno.prefix + "." + out.name
      val call = BVFunctionCall(functionName, args, out.width)
      val wireName = instanceName + "." + out.name
      signals.append(Signal(wireName, call))
    }
  }

  private def onMemory(m: ir.DefMemory, memSplited: Boolean): Map[String, State] = {
    
    // --- noted by yusz: use bv to encode mem instead of array
    // try vector-blasting
    // --- notes ends
    checkMem(m)

    // derive the type of the memory from the dataType and depth
    // --- modified by yusz: original codes are in the else branch
    val dataWidth = bitWidth(m.dataType).toInt
    val indexWidth = Utils.getUIntWidth(m.depth - 1).max(1)
    val indexRange = scala.math.pow(2,indexWidth).toInt
    
    val memSplitedStates = (0 until indexRange).toSeq.map
    {
      x:Int =>
      {
        val memSymbol = BVSymbol(m.name + "_" + x.toString(), dataWidth)
        val init = None
        val next = if (m.writers.isEmpty) {
          memSymbol
        } 
        else {
          m.writers.foldLeft[BVExpr](memSymbol) 
          {
            case (prev, write) =>
              // update
              val addr = BVSymbol(memPortField(m, write, "addr").serialize, indexWidth)
              val data = BVSymbol(memPortField(m, write, "data").serialize, dataWidth)

              val update = BVIte(BVEqual(addr,BVLiteral(BigInt(x),indexWidth)), data, prev)
              // update guard
              val en = BVSymbol(memPortField(m, write, "en").serialize, 1)
              val mask = BVSymbol(memPortField(m, write, "mask").serialize, 1)
              BVIte(BVAnd(en, mask), update, prev)
          }
        }
        val state = State(memSymbol, init, Some(next))
        (m.name + x.toString(), state)
      }
    }

    // derive read expressions
    val readSignals = m.readers.map { 
      read =>
        val addr = BVSymbol(memPortField(m, read, "addr").serialize, indexWidth)
        val addrWithSliceBV = (0 until scala.math.pow(2,indexWidth).toInt).toSeq.map
        {
          x:Int =>
          {
            val sliceBV = BVSymbol(m.name + "_" + x.toString(), dataWidth)
            Tuple2(BVEqual(addr,BVLiteral(BigInt(x),indexWidth)), sliceBV)
          }     
        }
        val result = addrWithSliceBV.tail.foldLeft[BVExpr](addrWithSliceBV.head._2){
          case (orig, Tuple2(cond, branch)) =>
          {
            BVIte(cond, branch, orig)
          }
        }
        Signal(memPortField(m, read, "data").serialize, result, IsNode)
    }
    signals ++= readSignals
    memSplitedStates.toMap
  }

  private def onMemory(m: ir.DefMemory): State = {
    
    checkMem(m)
    // --- noted by yusz: use bv to encode mem instead of array
    // 1.mem init 2.mem update 3.mem read
    // access value dynamically? by enumaration? 
    // multi-write-port?
    // it seems that vector-blasting is better than regarding the whole array as a large vector ???
    // --- notes ends

    // derive the type of the memory from the dataType and depth
    if(false)
    {
      // --- modified by yusz: original codes are in the else branch
      val dataWidth = bitWidth(m.dataType).toInt
      val indexWidth = Utils.getUIntWidth(m.depth - 1).max(1)
      val flattenWidth = scala.math.pow(2,indexWidth).toInt * dataWidth
      val flattenMemSymbol = BVSymbol(m.name, flattenWidth)

      val init = None
      val next = if (m.writers.isEmpty) {
        flattenMemSymbol
      } else {
        m.writers.foldLeft[BVExpr](flattenMemSymbol) {
          case (prev, write) =>
            // update
            val addr = BVSymbol(memPortField(m, write, "addr").serialize, indexWidth)
            val data = BVSymbol(memPortField(m, write, "data").serialize, dataWidth)
            val addrWithSubsBV = (0 until scala.math.pow(2,indexWidth).toInt).toSeq.map
            {
              x:Int =>
              {
                val headHighIndex = scala.math.pow(2,indexWidth).toInt*dataWidth - 1
                val headLowIndex = (x+1)*dataWidth
                val tailHighIndex = x*dataWidth - 1
                val tailLowIndex = 0
                
                if(x == 0)
                {
                  val headSlice = BVSlice(prev, headHighIndex, headLowIndex)
                  val reConcatBV = BVConcat(headSlice, data)
                  Tuple2(BVEqual(addr,BVLiteral(BigInt(x),indexWidth)), reConcatBV)
                }
                else if(x == scala.math.pow(2,indexWidth) - 1)
                {
                  val tailSlice = BVSlice(prev, tailHighIndex, tailLowIndex) 
                  val reConcatBV = BVConcat(data,tailSlice)
                  Tuple2(BVEqual(addr,BVLiteral(BigInt(x),indexWidth)), reConcatBV)
                }
                else
                {
                  val headSlice = BVSlice(prev, headHighIndex, headLowIndex)
                  val tailSlice = BVSlice(prev, tailHighIndex, tailLowIndex)
                  val reConcatBV = BVConcat(BVConcat(headSlice, data), tailSlice)
                  Tuple2(BVEqual(addr,BVLiteral(BigInt(x),indexWidth)), reConcatBV)
                }
              }     
            }
            val update = addrWithSubsBV.foldLeft[BVExpr](prev){
              case (orig, subs) =>
              {
                BVIte(subs._1, subs._2, orig)
              }
            }
            // update guard
            val en = BVSymbol(memPortField(m, write, "en").serialize, 1)
            val mask = BVSymbol(memPortField(m, write, "mask").serialize, 1)
            BVIte(BVAnd(en, mask), update, prev)
        }
      }
      val state = State(flattenMemSymbol, init, Some(next))
      // derive read expressions
      val readSignals = m.readers.map { read =>
        val addr = BVSymbol(memPortField(m, read, "addr").serialize, indexWidth)
        val addrWithSliceBV = (0 until scala.math.pow(2,indexWidth).toInt).toSeq.map
        {
          x:Int =>
          {
            val sliceBV = BVSlice(flattenMemSymbol, (x+1)*dataWidth-1, x*dataWidth)
            Tuple2(BVEqual(addr,BVLiteral(BigInt(x),indexWidth)), sliceBV)
          }     
        }
        val result = addrWithSliceBV.tail.foldLeft[BVExpr](addrWithSliceBV.head._2){
          case (orig, Tuple2(cond, branch)) =>
          {
            BVIte(cond, branch, orig)
          }
        }
        Signal(memPortField(m, read, "data").serialize, result, IsNode)
      }
      signals ++= readSignals
      state
      // modification ends
    }
    else
    {
      val dataWidth = bitWidth(m.dataType).toInt
      val indexWidth = Utils.getUIntWidth(m.depth - 1).max(1)
      val memSymbol = ArraySymbol(m.name, indexWidth, dataWidth)

      // there could be a constant init
      val init = memInit.get(m.name).map(getMemInit(m, indexWidth, dataWidth, _))
      init.foreach(e => assert(e.dataWidth == memSymbol.dataWidth && e.indexWidth == memSymbol.indexWidth))

      // derive next state expression
      val next = if (m.writers.isEmpty) {
        memSymbol
      } else {
        m.writers.foldLeft[ArrayExpr](memSymbol) {
          case (prev, write) =>
            // update
            val addr = BVSymbol(memPortField(m, write, "addr").serialize, indexWidth)
            val data = BVSymbol(memPortField(m, write, "data").serialize, dataWidth)
            val update = ArrayStore(prev, index = addr, data = data)

            // update guard
            val en = BVSymbol(memPortField(m, write, "en").serialize, 1)
            val mask = BVSymbol(memPortField(m, write, "mask").serialize, 1)
            ArrayIte(BVAnd(en, mask), update, prev)
        }
      }

      val state = State(memSymbol, init, Some(next))

      // derive read expressions
      val readSignals = m.readers.map { read =>
        val addr = BVSymbol(memPortField(m, read, "addr").serialize, indexWidth)
        Signal(memPortField(m, read, "data").serialize, ArrayRead(memSymbol, addr), IsNode)
      }
      signals ++= readSignals

      state
    }
    
  }

  private def getMemInit(m: ir.DefMemory, indexWidth: Int, dataWidth: Int, initValue: MemoryInitValue): ArrayExpr =
    initValue match {
      case MemoryScalarInit(value) => ArrayConstant(BVLiteral(value, dataWidth), indexWidth)
      case MemoryArrayInit(values) =>
        assert(
          values.length == m.depth,
          s"Memory ${m.name} of depth ${m.depth} cannot be initialized with an array of length ${values.length}!"
        )
        // in order to get a more compact encoding try to find the most common values
        val histogram = mutable.LinkedHashMap[BigInt, Int]()
        values.foreach(v => histogram(v) = 1 + histogram.getOrElse(v, 0))
        val baseValue = histogram.maxBy(_._2)._1
        val base = ArrayConstant(BVLiteral(baseValue, dataWidth), indexWidth)
        values.zipWithIndex
          .filterNot(_._1 == baseValue)
          .foldLeft[ArrayExpr](base) {
            case (array, (value, index)) =>
              ArrayStore(array, BVLiteral(index, indexWidth), BVLiteral(value, dataWidth))
          }
      case other => throw new RuntimeException(s"Unsupported memory init option: $other")
    }

  private def checkMem(m: ir.DefMemory): Unit = {
    assert(m.readLatency == 0, "Expected read latency to be 0. Did you run VerilogMemDelays?")
    assert(m.writeLatency == 1, "Expected read latency to be 1. Did you run VerilogMemDelays?")
    assert(
      m.dataType.isInstanceOf[ir.GroundType],
      s"Memory $m is of type ${m.dataType} which is not a ground type!"
    )
    assert(m.readwriters.isEmpty, "Combined read/write ports are not supported! Please split them up.")
  }

  private def onExpression(e: ir.Expression, width: Int, allowNarrow: Boolean = false): BVExpr =
    FirrtlExpressionSemantics.toSMT(e, width, allowNarrow)
  private def onExpression(e: ir.Expression): BVExpr = FirrtlExpressionSemantics.toSMT(e)

  private def error(msg:        String):  Unit = throw new RuntimeException(msg)
  private def isGroundType(tpe: ir.Type): Boolean = tpe.isInstanceOf[ir.GroundType]
  private def isClock(tpe:      ir.Type): Boolean = tpe == ir.ClockType
  private def isReset(tpe:      ir.Type): Boolean = tpe == ir.ResetType
  private def isAsyncReset(tpe: ir.Type): Boolean = tpe == ir.AsyncResetType
  
   
}
