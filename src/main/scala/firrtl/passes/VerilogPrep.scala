// SPDX-License-Identifier: Apache-2.0

package firrtl.passes

import firrtl.Utils.{create_exps, flow, kind, toWrappedExpression}
import firrtl.ir._
import firrtl.Mappers._
import firrtl.options.Dependency
import firrtl._
import firrtl.annotations._

import firrtl.renamemap.MutableRenameMap

import scala.collection.mutable

import chiseltest.formal._

/** Makes changes to the Firrtl AST to make Verilog emission easier
  *
  * - For each instance, adds wires to connect to each port
  *   - Note that no Namespace is required because Uniquify ensures that there will be no
  *     collisions with the lowered names of instance ports
  * - Also removes Attaches where a single Port OR Wire connects to 1 or more instance ports
  *   - These are expressed in the portCons of WDefInstConnectors
  *
  * @note The result of this pass is NOT legal Firrtl
  */
object VerilogPrep extends Pass {

  override def prerequisites = firrtl.stage.Forms.LowFormMinimumOptimized ++
    Seq(
      Dependency[firrtl.transforms.BlackBoxSourceHelper],
      Dependency[firrtl.transforms.FixAddingNegativeLiterals],
      Dependency[firrtl.transforms.ReplaceTruncatingArithmetic],
      Dependency[firrtl.transforms.InlineBitExtractionsTransform],
      Dependency[firrtl.transforms.InlineAcrossCastsTransform],
      Dependency[firrtl.transforms.LegalizeClocksAndAsyncResetsTransform],
      Dependency[firrtl.transforms.FlattenRegUpdate],
      Dependency(passes.VerilogModulusCleanup),
      Dependency[firrtl.transforms.VerilogRename]
    )

  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized

  override def optionalPrerequisiteOf = Seq.empty

  override def invalidates(a: Transform) = false

  type AttachSourceMap = Map[WrappedExpression, Expression]

  // Finds attaches with only a single source (Port or Wire)
  //   - Creates a map of attached expressions to their source
  //   - Removes the Attach
  private def collectAndRemoveAttach(m: DefModule): (DefModule, AttachSourceMap) = {
    val sourceMap = mutable.HashMap.empty[WrappedExpression, Expression]
    lazy val namespace = Namespace(m)

    def onStmt(stmt: Statement): Statement = stmt.map(onStmt) match {
      case attach: Attach =>
        // println(s"attach: $attach")
        val wires = attach.exprs.groupBy(kind)
        val sources = wires.getOrElse(PortKind, Seq.empty) ++ wires.getOrElse(WireKind, Seq.empty)
        val instPorts = wires.getOrElse(InstanceKind, Seq.empty)
        // Sanity check (Should be caught by CheckTypes)
        assert(sources.size + instPorts.size == attach.exprs.size)

        sources match {
          case Seq() => // Zero sources, can add a wire to connect and remove
            val name = namespace.newTemp
            val wire = DefWire(NoInfo, name, instPorts.head.tpe)
            val ref = WRef(wire)
            for (inst <- instPorts) sourceMap(inst) = ref
            wire // Replace the attach with new source wire definition
          case Seq(source) => // One source can be removed
            assert(!sourceMap.contains(source)) // should have been merged
            for (inst <- instPorts) sourceMap(inst) = source
            EmptyStmt
          case moreThanOne =>
            attach
        }
      case s => 
      {
        s
      }
    }
    // println(s"sourceMap: $sourceMap")
    (m.map(onStmt), sourceMap.toMap)
  }

  def run(c: Circuit): Circuit = {
    def lowerE(e: Expression): Expression = e match {
      case (_: WRef | _: WSubField) if kind(e) == InstanceKind =>
        WRef(LowerTypes.loweredName(e), e.tpe, kind(e), flow(e))
      case _ => e.map(lowerE)
    }

    def lowerS(attachMap: AttachSourceMap)(s: Statement): Statement = s match {
      case WDefInstance(info, name, module, tpe) =>
        val portRefs = create_exps(WRef(name, tpe, ExpKind, SourceFlow))
        val (portCons, wires) = portRefs.map { p =>
          attachMap.get(p) match {
            // If it has a source in attachMap use that
            case Some(ref) => (p -> ref, None)
            // If no source, create a wire corresponding to the port and connect it up
            case None =>
              val wire = DefWire(info, LowerTypes.loweredName(p), p.tpe)
              (p -> WRef(wire), Some(wire))
          }
        }.unzip
        val newInst = WDefInstanceConnector(info, name, module, tpe, portCons)
        Block(wires.flatten :+ newInst)
      case other => other.map(lowerS(attachMap)).map(lowerE)
    }
    
    val modulesx = c.modules.map { mod =>
      val (modx, attachMap) = collectAndRemoveAttach(mod)
      modx.map(lowerS(attachMap))
    }
    c.copy(modules = modulesx)
  }


  def onModule(c: Circuit, renames: MutableRenameMap)(m: DefModule): DefModule = {
    def lowerE(e: Expression): Expression = e match {
      case _:WRef if kind(e) == InstanceKind =>
        WRef(LowerTypes.loweredName(e), e.tpe, kind(e), flow(e))
      case _:WSubField if kind(e) == InstanceKind =>
        val wire = WRef(LowerTypes.loweredName(e), e.tpe, kind(e), flow(e))
        wire
      case _ => e.map(lowerE)
    }

    def lowerS(attachMap: AttachSourceMap)(s: Statement): Statement = s match {
      case t@WDefInstance(info, name, module, tpe) =>
        val portRefs = create_exps(WRef(name, tpe, ExpKind, SourceFlow))
        val (portCons, wires) = portRefs.map { p =>
          attachMap.get(p) match {
            // If it has a source in attachMap use that
            case Some(ref) => (p -> ref, None)
            // If no source, create a wire corresponding to the port and connect it up
            case None =>
              val WSubField(sexpr,sname,_,_) = p
              val mTarget = ModuleTarget(c.main, m.name)

              val oldRT = Target.asTarget(mTarget)(p)

              val inlineTarget = mTarget.instOf(name, module)
              val temp = inlineTarget.ref(sname)
              val temp2 = mTarget.instOf(name, module).ofModuleTarget.ref(sname)

              val wire = DefWire(info, LowerTypes.loweredName(p), p.tpe)
              val newRT = mTarget.ref(LowerTypes.loweredName(p))
              
              // println(s"update RT: ${temp}, ${temp2}, ${newRT}")
              renames.record(temp, newRT)
              renames.record(temp2, newRT)
              (p -> WRef(wire), Some(wire))
          }
        }.unzip
        val newInst = WDefInstanceConnector(info, name, module, tpe, portCons)
        Block(wires.flatten :+ newInst)
      case other => other.map(lowerS(attachMap)).map(lowerE)
    }

    
    val (modx, attachMap) = collectAndRemoveAttach(m)
    val resutlModule = modx.map(lowerS(attachMap))
    resutlModule
  }

  override def execute(state: CircuitState): CircuitState = {
    // println(s"executes: ${state.circuit.serialize}")
    val c = state.circuit
    val renames = MutableRenameMap()
    val state_cha = state.annotations.toSeq.collect{
      case x:chaAnno => x
    }
    // println(s"state_cha: ${state_cha}")
    state.copy(circuit = c.map(onModule(c, renames)), renames = Some(renames))
    // state.copy(circuit = run(state.circuit))
  }
}
