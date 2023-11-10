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
import scala.runtime.Statics

/** Contains code to convert a flat firrtl module into a functional transition system which
  * can then be exported as SMTLib or Btor2 file.
  */
object EncodeCHA extends Transform with DependencyAPIMigration {
  //VerilogMemDelays we want to trace the renaming of the registers created my the mem delay pass, index haven't gotten it now, index will see.
  override def prerequisites: Seq[Dependency[Transform]] = Forms.LowForm ++
    Seq(
      Dependency(FirrtlToTransitionSystem)
    )
  override def invalidates(a: Transform): Boolean = false
  // since this pass only runs on the main module, inlining needs to happen before
  override def optionalPrerequisites: Seq[TransformDependency] = Seq(Dependency[firrtl.passes.InlineInstances])

  private def meetJustCondtion(accSignal:Signal, resetSignal:BVExpr, seen:Option[State]): Option[State] = {

    assert(accSignal.lbl == IsConstraint | accSignal.lbl == IsFair)
    
    val accExpr = accSignal.e.asInstanceOf[BVExpr]
    val triggeredSymbol = BVSymbol("triggered"+"_"+accSignal.name+"_",1)

    // if accSignal is a constraint, then it is valid before tht loop
    // assume | assert | return
    //  safe  |  safe  | triggered_without_seen
    //  safe  |  live  | triggered_without_seen
    //  live  |  safe  | None
    //  live  |  live  | triggered_with_seen
    
    val triggered =
      if(accSignal.lbl == IsConstraint)
      {
        val triggerNext = BVOr(List(triggeredSymbol.asInstanceOf[BVExpr], accSignal.e.asInstanceOf[BVExpr]))
        Some(State(triggeredSymbol,Some(BVLiteral(BigInt(0),1)),Some(triggerNext)))
      }
      else
      {
        seen match {
          case None => None
          case Some(s) => 
            val seenExpr = s.next.get.asInstanceOf[BVExpr]
            val noReset = BVNot(resetSignal)
            val triggerNext = BVOr(List( BVAnd(List(triggeredSymbol, noReset)), BVAnd(List(accSignal.e.asInstanceOf[BVExpr],seenExpr))))
            Some(State(triggeredSymbol,Some(BVLiteral(BigInt(0),1)),Some(triggerNext)))
          }
      }
        
    triggered
  }

  private def genSafeSignals(just2BadStatesMap: Seq[Tuple2[State,State]], accSignal:Signal, resetSignal:BVExpr, i:Int) : Tuple3[Signal, Seq[State], Option[State]] = {
    
    val index = i 
    var safeSignals:mutable.Seq[Signal] = mutable.Seq[Signal]()
    var auxJust2BadStates:mutable.Seq[State] = mutable.Seq[State]()
     
    val correspEqual = BVAnd(just2BadStatesMap.filter
      {
        case t:Tuple2[State,State] =>
          t._1.name.slice(0,8) != "assertSta"  | t._1.name == "assertSta" + index.toString + "_"
      }
      .map{
      case t:Tuple2[State,State] =>
        if(t._1.sym.isInstanceOf[BVSymbol])
        {
          BVEqual(t._1.sym.asInstanceOf[BVExpr],t._2.sym.asInstanceOf[BVExpr])
        }
        else
        {
          ArrayEqual(t._1.sym.asInstanceOf[ArrayExpr],t._2.sym.asInstanceOf[ArrayExpr])
        }
      }.toList)

    assert(accSignal.lbl == IsBad | accSignal.lbl == IsJustice)
    if (accSignal.lbl == IsBad) {
      Tuple3(accSignal, Seq() ++ auxJust2BadStates, None)
    }
    else {
      val reset = resetSignal

      val seenSymbol = BVSymbol("seen"+"_"+index+"_",1)
      val seenNext = BVAnd(List(BVOr(List(correspEqual,seenSymbol)),BVNot(reset)))  
      val seen:State = State(seenSymbol,Some(BVLiteral(BigInt(0),1)),Some(seenNext))
      // val seen:State = State(seenSymbol,Some(BVLiteral(BigInt(0),1)),Some(BVOr(List(correspEqual,seenSymbol))))
      auxJust2BadStates +:= seen

      val triggeredSymbol = BVSymbol("triggered"+"_"+index+"_",1)
      val triggerNext = BVAnd(List(BVOr(List(triggeredSymbol,BVAnd(List(accSignal.e.asInstanceOf[BVExpr],seenNext)))),BVNot(reset)))
      // val triggered:State = State(triggeredSymbol,Some(BVLiteral(BigInt(0),1)),Some(BVOr(List(triggeredSymbol,BVAnd(List(accSignal.e.asInstanceOf[BVExpr],seenSymbol))))))
      val triggered:State = State(triggeredSymbol,Some(BVLiteral(BigInt(0),1)),Some(triggerNext))
      auxJust2BadStates +:= triggered

      val loop = Signal("just2Bad" + i + "_", BVAnd(List(triggeredSymbol,correspEqual):+BVNot(reset)) , IsBad)

      Tuple3(loop, Seq() ++ auxJust2BadStates, Some(seen))
    }
  }
  // sys: original transition system, extraInputNum: 
  private def encodeProps(sysWithCHA:TransitionSystem, accSignals:mutable.Seq[Signal], resetSignals:Seq[BVExpr]): TransitionSystem={

    println(s"accSignals: $accSignals")
    
    val just2BadStatesMap:Seq[Tuple2[State,State]] = sysWithCHA.states.filter
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
    
    // if all properties are safety properties, don't execute L2S 
    val noLive = accSignals.filter(x => x.lbl == IsJustice | x.lbl == IsFair).isEmpty
    println(s"noLive: $noLive")
    var auxJust2BadStates = if (noLive) mutable.Seq[State]() else just2BadStatesMap.map{_._2}.toSeq
    var safeSignals:mutable.Seq[Signal] = mutable.Seq[Signal]()
    // var auxSignals::mutable.Seq[Signal] = mutable.Seq[Signal]()
    assert(accSignals.size == resetSignals.size)
    val accWithResSignal = accSignals.zip(resetSignals).zipWithIndex.map{
      case t => Tuple3(t._1._1, t._1._2, t._2)
    }

    var constraintSignals = accSignals.filter(_.lbl == IsConstraint)

    val assumeAccSignal = accWithResSignal.filter(x => x._1.lbl == IsFair) 
    val assertAccSignal = accWithResSignal.filter(x => x._1.lbl == IsBad | x._1.lbl == IsJustice) 

    var gloAssumeStates: mutable.Seq[State] = mutable.Seq[State]()

    assertAccSignal.foreach{
      case t: Tuple3[Signal,BVExpr,Int] => {
        // translating assertion
        val assertResult = genSafeSignals(just2BadStatesMap, t._1, t._2, t._3)

        auxJust2BadStates = auxJust2BadStates ++ assertResult._2
        val seenState = assertResult._3

        var assumeResult = mutable.Seq[Option[State]]()
        assumeAccSignal.foreach{
          case s: Tuple3[Signal,BVExpr,Int] => 
            assumeResult = assumeResult :+ meetJustCondtion(s._1, s._2, seenState)
        }

        val validTrigState:Seq[State] = (Seq() ++ assumeResult).collect{
          case Some(s) => 
            auxJust2BadStates = auxJust2BadStates :+ s
            s
        }
        val trigStateSym = validTrigState.map(_.sym.asInstanceOf[BVSymbol].asInstanceOf[BVExpr])

        val assertSignal = assertResult._1

        val resultExpr = BVAnd(trigStateSym.toList :+ assertSignal.e.asInstanceOf[BVExpr])
        val resultSignal = assertSignal.copy(assertSignal.name, resultExpr, IsBad)
       safeSignals = safeSignals :+ resultSignal
      } 
    }
    println(s"safeSignal: ${safeSignals}")
    sysWithCHA.copy(sysWithCHA.name,sysWithCHA.inputs,sysWithCHA.states:::auxJust2BadStates.toList,sysWithCHA.signals:::safeSignals.toList:::constraintSignals.toList,sysWithCHA.comments,sysWithCHA.header)
  }

  override protected def execute(state: CircuitState): CircuitState = {

    val circuit = state.circuit
    val sys = state.annotations.filter{_.isInstanceOf[TransitionSystemAnnotation]}.head.asInstanceOf[TransitionSystemAnnotation].sys

    val chaAsserts : AnnotationSeq = state.annotations.filter {_.isInstanceOf[chaAssertAnno]}
    //println(s"chaAnnos: ($chaAnnos).toSeq")
    val chaAnnos : AnnotationSeq = state.annotations.filter {_.isInstanceOf[chaAnno]}
    
    // val assumeImplyAssert = AssumeImplyAssert(chaAssumes, chaAsserts)
    // chaAssume without chaAssert is meaningless 
    val sortedSys =
    if(!chaAsserts.isEmpty)
    {
      val targetDirs = state.annotations.collect { case TargetDirAnnotation(d) => d }.toSet
      require(targetDirs.nonEmpty, "Expected exactly one target directory, got none!")
      require(targetDirs.size == 1, s"Expected exactly one target directory, got multiple: $targetDirs")

      val pslsWithMap : Seq[Tuple4[String, Map[String,Target], Target, chaStmt]] = chaAnnos.collect{
      // val pslsWithMap : Seq[Tuple2[String, Map[String,Target]]] = chaAnnos.collect{
        case s: chaAnno => {println(s"chaAnno: ${chaAnno}"); chaAnno.CHAAnno2PSL(s)} 
      }

      var extraInputNum: Int = 0
      var extraInputs:mutable.Seq[BVSymbol] = mutable.Seq[BVSymbol]()
      var baStateNum:Int = 0
      var baStates:mutable.Seq[State] = mutable.Seq[State]()
      var accSignalNum:Int = 0
      var accSignals:mutable.Seq[Signal] = mutable.Seq[Signal]()

      val irLookup = IRLookup(circuit)
      val resetSignals:Seq[BVExpr] = pslsWithMap.collect{
        case t: Tuple4[String, Map[String,Target], Target, chaStmt] => 
        // case t: Tuple2[String, Map[String,Target]] => 
        {
          val thisExpr = irLookup.expr(t._3.asInstanceOf[ReferenceTarget])
          FirrtlExpressionSemantics.toSMT(thisExpr)
        }
      }

      println(s"resetSignals: ${resetSignals}")
      val addAssumeToTransitionSystems: Unit = pslsWithMap.collect{
        //case object doesn't work here
        case t: Tuple4[String, Map[String,Target], Target, chaStmt] if t._4 == chaAssumeStmt => 
        // case t: Tuple2[String, Map[String,Target],Target] => 
        {
          // add optimization: if assume(p) refers to a safety property and 
          // the negation of Gp corresponds to a deterministic automat, 
          // this assumption will be encoded to constraint 
          val isSafetyCmd = Seq("ltlfilt","-f",t._1,"--safety") 
          val isSafetyRes :os.CommandResult = os.proc(isSafetyCmd).call(cwd = os.pwd / os.RelPath(targetDirs.head), check = false)
          // val isSafety = 
          val isSafety = !isSafetyRes.out.string.isEmpty
          println(s"isSafety: ${isSafety}")
          println(s"chaAssumeStmt: ${t._1}, ${t._4}")

          val negAssumeFormular = "!" + {t._1}
          println(s"negAssumeFormular: ${negAssumeFormular}")
          val optiCmd = Seq("ltl2tgba","-B","-D", "-f", negAssumeFormular)
          val optRetr:os.CommandResult = os.proc(optiCmd).call(cwd = os.pwd / os.RelPath(targetDirs.head), check = false)
          val optiAvai = Buchi2TransitionSystem.assumeAvai(optRetr)
          val (optiEn, dba) = 
          optiAvai match{
            case Some(h) => Tuple2(true, h)
            case None => {
              val cmd = Seq("ltl2tgba","-B","-D", "-f", t._1)
              val retr:os.CommandResult = os.proc(cmd).call(cwd = os.pwd / os.RelPath(targetDirs.head), check = false)
              (false,Buchi2TransitionSystem.getDBA(retr))
            }
          }
          println(s"optiEn:$optiEn")
          // val dba = Buchi2TransitionSystem.getDBA(retr)
          val ret = Buchi2TransitionSystem.psl2TransitionSystem(dba, t._2, extraInputNum, baStateNum, accSignalNum, circuit, t._3, t._4, optiEn)
          extraInputs ++= ret._1
          baStates :+= ret._2
          accSignals :+= ret._3
          extraInputNum += dba.auxVarNum
          baStateNum += 1
          accSignalNum += 1
        }
      }

      val addAssertToTransitionSystems: Unit = pslsWithMap.collect{
        case t: Tuple4[String, Map[String,Target], Target, chaStmt] if t._4 == chaAssertStmt => 
        // case t: Tuple2[String, Map[String,Target],Target] => 
        {
          println(s"chaAssertStmt: ${t._1}")
          val cmd = Seq("ltl2tgba","-B","-D", "-f", t._1)
          val retr:os.CommandResult = os.proc(cmd).call(cwd = os.pwd / os.RelPath(targetDirs.head), check = false)
          
          val dba = Buchi2TransitionSystem.getDBA(retr)
          val ret = Buchi2TransitionSystem.psl2TransitionSystem(dba, t._2, extraInputNum, baStateNum, accSignalNum, circuit, t._3, t._4)
          extraInputs ++= ret._1
          baStates :+= ret._2
          accSignals :+= ret._3
          extraInputNum += dba.auxVarNum
          baStateNum += 1
          accSignalNum += 1
        }
      }

      val sysWithCHA = sys.copy(sys.name,sys.inputs:::extraInputs.toList,sys.states:::baStates.toList, sys.signals,sys.comments,sys.header)
      val sysJust2Bad = encodeProps(sysWithCHA, accSignals, resetSignals)
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

// encode assume(p) and assert(q) as (Gp->Gq), not work 
  // private def AssumeImplyAssert(chaAssumes:AnnotationSeq, chaAsserts:AnnotationSeq): Seq[chaAnno] = {
  //   val chaAssertsWithGlo = chaAsserts.toSeq.map(Seq(glo_prop(null)) +: _.asInstanceOf[chaAssertAnno].ttargets)
  //   val chaAssumesWithGlo = chaAssumes.toSeq.map(Seq(glo_prop(null)) +: _.asInstanceOf[chaAssumeAnno].ttargets)

  //   val chaAssumeSeqs = Seq(Seq(impl_prop(null,null))) :++
  //   (1 to chaAssumes.toSeq.size -1).map
  //   {
  //     x => Seq(and_prop(null,null)) 
  //   } ++: chaAssumesWithGlo.flatten
  //   println(s"chaAssumeSeqs: ${chaAssumeSeqs}")
    
  //   val assumeImplyAssert = 
  //     if(!chaAssumes.toSeq.isEmpty)
  //       chaAssertsWithGlo.toSeq.map(chaAssumeSeqs ++: _).map(chaAssertAnno(_))
  //     else
  //       chaAssertsWithGlo.toSeq.map(chaAssertAnno(_))
  //   println(s"assumeImplyAssert: ${assumeImplyAssert}")
  //   assumeImplyAssert
  // }