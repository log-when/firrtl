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

/** Contains code to convert a flat firrtl module into a functional transition system which
  * can then be exported as SMTLib or Btor2 file.
  */
object EncodeSVA extends Transform with DependencyAPIMigration {
  //VerilogMemDelays we want to trace the renaming of the registers created my the mem delay pass, I haven't gotten it now, I will see.
  override def prerequisites: Seq[Dependency[Transform]] = Forms.LowForm ++
    Seq(
      Dependency(FirrtlToTransitionSystem)
    )
  override def invalidates(a: Transform): Boolean = false
  // since this pass only runs on the main module, inlining needs to happen before
  override def optionalPrerequisites: Seq[TransformDependency] = Seq(Dependency[firrtl.passes.InlineInstances])

  // sys: original transition system, extraInputNum: 
  private def encodeProps(sysWithSVA:TransitionSystem, accSignals:mutable.Seq[Signal]): TransitionSystem={

    println(s"accSignals: $accSignals")
    val just2BadStatesMap = sysWithSVA.states.filter
    {
      case s:State =>
        s.name != "_resetCount"
    }
    .map{
      case s:State => 
      {
        if(s.sym.isInstanceOf[BVSymbol])
        {
          val temp:BVSymbol = s.sym.asInstanceOf[BVSymbol]
          val temp2 = temp.copy(temp.name+"__",temp.width)
          Tuple2(s,s.copy(temp2,None,Some(temp2.asInstanceOf[SMTExpr])))
        }
        else
        {
          val temp:ArraySymbol = s.sym.asInstanceOf[ArraySymbol]
          val temp2 = temp.copy(temp.name+"__",temp.indexWidth,temp.dataWidth)
          Tuple2(s,s.copy(temp2,None,Some(temp2.asInstanceOf[SMTExpr])))
        }
      }
    }
    
    val noJust = accSignals.filter(_.lbl == IsJustice).isEmpty
    println(s"noJust: $noJust")
    var auxJust2BadStates = if (noJust) mutable.Seq[State]() else just2BadStatesMap.map{_._2}.toSeq
    var badSignals:mutable.Seq[Signal] = mutable.Seq[Signal]()
    val correspEquals = just2BadStatesMap.map{
      case t:Tuple2[State,State] =>
        if(t._1.sym.isInstanceOf[BVSymbol])
        {
          BVEqual(t._1.sym.asInstanceOf[BVExpr],t._2.sym.asInstanceOf[BVExpr])
        }
        else
        {
          ArrayEqual(t._1.sym.asInstanceOf[ArrayExpr],t._2.sym.asInstanceOf[ArrayExpr])
        }
    }
    var correspEqual = BVAnd(correspEquals)
    for(i <- 0 until accSignals.size)
    {
      if (accSignals(i).lbl == IsBad) {
        badSignals +:= accSignals(i)
      }
      else if (accSignals(i).lbl == IsJustice){
        // val reset = resetSignals(i)
        val seenSymbol = BVSymbol("seen"+"_"+i+"_",1)
        // val seen:State = State(seenSymbol,Some(BVLiteral(BigInt(0),1)),Some(BVAnd(List(BVOr(List(correspEqual,seenSymbol)),BVNot(reset)))))
        val seen:State = State(seenSymbol,Some(BVLiteral(BigInt(0),1)),Some(BVOr(List(correspEqual,seenSymbol))))
        auxJust2BadStates +:= seen

        val triggeredSymbol = BVSymbol("triggered"+"_"+i+"_",1)
        val triggered:State = State(triggeredSymbol,Some(BVLiteral(BigInt(0),1)),Some(BVOr(List(triggeredSymbol,BVAnd(List(accSignals(i).e.asInstanceOf[BVExpr],seenSymbol))))))
        // val triggered:State = State(triggeredSymbol,Some(BVLiteral(BigInt(0),1)),Some(BVAnd(List(BVOr(List(triggeredSymbol,BVAnd(List(accSignals(i).e.asInstanceOf[BVExpr],seenSymbol)))),BVNot(reset)))))
        auxJust2BadStates +:= triggered

        val loop = Signal("just2Bad" + i + "_", BVAnd(List(triggeredSymbol,correspEqual)) , IsBad)
        // val loop = Signal("just2Bad" + i + "_", BVAnd(List(triggeredSymbol,correspEqual):+BVNot(reset)) , IsBad)
        badSignals +:= loop
      }
    }
    sysWithSVA.copy(sysWithSVA.name,sysWithSVA.inputs,sysWithSVA.states:::auxJust2BadStates.toList,sysWithSVA.signals:::badSignals.toList,sysWithSVA.comments,sysWithSVA.header)
  }

  override protected def execute(state: CircuitState): CircuitState = {

    val circuit = state.circuit
    val sys = state.annotations.filter{_.isInstanceOf[TransitionSystemAnnotation]}.head.asInstanceOf[TransitionSystemAnnotation].sys

    val svaAnnos : AnnotationSeq = state.annotations.filter {_.isInstanceOf[svaSeqAnno]}
    //println(s"svaAnnos: ($svaAnnos).toSeq")
    val sortedSys =
    if(!svaAnnos.isEmpty)
    {
      val targetDirs = state.annotations.collect { case TargetDirAnnotation(d) => d }.toSet
      require(targetDirs.nonEmpty, "Expected exactly one target directory, got none!")
      require(targetDirs.size == 1, s"Expected exactly one target directory, got multiple: $targetDirs")

      val pslsWithMap : Seq[Tuple3[String, Map[String,Target], Target]] = svaAnnos.collect{
      // val pslsWithMap : Seq[Tuple2[String, Map[String,Target]]] = svaAnnos.collect{
        case s: svaSeqAnno => svaSeqAnno.SVAAnno2PSL(s)
      }

      var extraInputNum: Int = 0
      var extraInputs:mutable.Seq[BVSymbol] = mutable.Seq[BVSymbol]()
      var baStateNum:Int = 0
      var baStates:mutable.Seq[State] = mutable.Seq[State]()
      var accSignalNum:Int = 0
      var accSignals:mutable.Seq[Signal] = mutable.Seq[Signal]()

      val irLookup = IRLookup(circuit)
      val resetSignals:Seq[BVExpr] = pslsWithMap.collect{
        case t: Tuple3[String, Map[String,Target],Target] => 
        // case t: Tuple2[String, Map[String,Target]] => 
        {
          val thisExpr = irLookup.expr(t._3.asInstanceOf[ReferenceTarget])
          FirrtlExpressionSemantics.toSMT(thisExpr)
        }
      }

      val toTransitionSystems: Unit = pslsWithMap.collect{
        case t: Tuple3[String, Map[String,Target],Target] => 
        // case t: Tuple2[String, Map[String,Target],Target] => 
        {
          val cmd = Seq("ltl2tgba","-B","-D", "-f", t._1)
          val retr:os.CommandResult = os.proc(cmd).call(cwd = os.pwd / os.RelPath(targetDirs.head), check = false)
          
          val dba = Buchi2TransitionSystem.getDBA(retr)
          val ret = Buchi2TransitionSystem.psl2TransitionSystem(dba, t._2, extraInputNum, baStateNum, accSignalNum, circuit, t._3)
          extraInputs ++= ret._1
          baStates :+= ret._2
          accSignals :+= ret._3
          extraInputNum += dba.auxVarNum
          baStateNum += 1
          accSignalNum += 1
        }
      }

      val sysWithSVA = sys.copy(sys.name,sys.inputs:::extraInputs.toList,sys.states:::baStates.toList, sys.signals,sys.comments,sys.header)
      val sysJust2Bad = encodeProps(sysWithSVA,accSignals)
      TopologicalSort.run(sysJust2Bad)
    }
    else
    {
       TopologicalSort.run(sys)
    }
    val anno = TransitionSystemAnnotation(sortedSys)
    val newAnnotations = state.annotations.toSeq.filter(!_.isInstanceOf[TransitionSystemAnnotation]):+anno
    state.copy(circuit = circuit, annotations = AnnotationSeq(newAnnotations))
  }
}

