// added in cha: parse Buchi automata, synthesis the transiton system and 
package firrtl.backends.experimental.smt

import firrtl.annotations.{Target, ReferenceTarget, MemoryInitAnnotation, NoTargetAnnotation, PresetRegAnnotation}
import firrtl._
import firrtl.ir._

import chiseltest.formal._ 
import firrtl.analyses._
import java.io._
import jhoafparser.parser.HOAFParser._
import jhoafparser.ast.AtomAcceptance
import jhoafparser.ast.AtomLabel
import jhoafparser.ast.BooleanExpression
import jhoafparser.consumer.HOAConsumer
import jhoafparser.consumer.HOAConsumerException
import jhoafparser.parser.HOAFParser
import jhoafparser.parser.generated.ParseException
import scala.collection.mutable
import net.sf.javabdd.BDD

import scala.collection.mutable
import java.lang.ref.Reference
import javax.lang.model.`type`.ReferenceType

object Buchi2TransitionSystem {

  // Input: Seq((cond, branch)), default value; 
  // output: ite(cond1, branch1, ite(cond2, branch2, ... (cond_n, branch_n, default)))
  def genIte(bvs:mutable.Seq[Tuple2[BVExpr,BVExpr]], defau: BVExpr): BVExpr =
  {
      if(bvs.isEmpty)
      {
          defau
      }
      else
      {
          BVIte(bvs(0)._1, bvs(0)._2, genIte(bvs.slice(1,bvs.size), defau))
      }
  }

  // Given a state var and its trans relation(bvs), generate the smt expr
  def genTotalIte(baState:BVSymbol, bvs:mutable.Map[Int,mutable.Seq[Tuple2[BVExpr,BVExpr]]], defau: BVExpr, stateBits:Int): BVExpr =
  {
    if(bvs.isEmpty)
    {
      defau
    }
    else
    {
      val ffirst = bvs.head
      val remaining = bvs - (ffirst._1)
      BVIte(BVEqual(baState, BVLiteral(BigInt(ffirst._1), stateBits)), genIte(ffirst._2, defau), genTotalIte(baState, remaining, defau, stateBits))
    }
  }

  def bddToSMTExpr(apNum: Int, bdd:BDD, int2Ap:mutable.Map[Int,String], p2target:Map[String,Target], circuit:Circuit, auxVar: Seq[BVSymbol]) : BVExpr = 
  {
    if(bdd.isZero())
    {
      BVLiteral(BigInt(0),1)
    }
    else if(bdd.isOne())
    {
      BVLiteral(BigInt(1),1)
    }
    else
    {
      val atom:Int = bdd.`var`()
      val curExpr = 
        if(atom < apNum)
        {
          val thisTarget = p2target(int2Ap(bdd.`var`()))
          val irLookup = IRLookup(circuit)
          val thisExpr = irLookup.expr(thisTarget.asInstanceOf[ReferenceTarget])
          FirrtlExpressionSemantics.toSMT(thisExpr)
        }
        else
        {
          auxVar(atom-apNum)
        }

      val low:BVExpr = bddToSMTExpr(apNum,bdd.low(),int2Ap,p2target,circuit,auxVar)
      val high:BVExpr = bddToSMTExpr(apNum,bdd.high(),int2Ap,p2target,circuit,auxVar)
      
      // low: 0,x,1; high:0,x,1; (0,0),(1,1) are checked before
      if(bdd.low.isZero())
        if(bdd.high.isOne())  //(1,0)
          curExpr
        else                  //(x,0)
          BVAnd(List(curExpr,high)) 
      else if(bdd.high.isZero())
        if(bdd.low.isOne())   //(0,1)
          BVNot(curExpr)
        else                  //(0,x)
          BVAnd(List(BVNot(curExpr),low))
      else if(bdd.high.isOne) //(1,x)
        BVOr(List(curExpr, BVAnd(List(BVNot(curExpr),low))))
      else if(bdd.low.isOne)  //(x,1)
        BVOr(List(BVNot(curExpr), BVAnd(List(curExpr,high))))
      else                    //(x,x)
        BVOr(List(BVAnd(List(curExpr,high)), BVAnd(List(BVNot(curExpr),low))))

      // BVIte(curExpr,high,low)
    }
  }

  // Merge the accepting states of BA into one
  def genAcc(baState:BVSymbol, accepts:Seq[Int], stateBits:Int): BVExpr =
  {
    if(accepts.size == 1)
        BVEqual(baState, BVLiteral(BigInt(accepts(0)), stateBits))
    else
    {
        val accExprs:Seq[BVExpr] = accepts.map{a =>BVEqual(baState, BVLiteral(BigInt(a), stateBits))}
        val firstTerm:BVExpr = accExprs(0)
        accExprs.slice(1,accExprs.size).foldLeft(firstTerm)((a,b) => BVOr(List(a,b)))
    }  
  }

  def getDBA(retr:os.CommandResult): hoaParser = 
  {
    val is = new ByteArrayInputStream(retr.out.string().getBytes())
    val bis = new BufferedInputStream(is)    
    val h = new hoaParser()
    HOAFParser.parseHOA(bis,h)    
    bis.close()
    is.close()
      
    // println(s"before deter: ${h.transitionFunc}")
    // distinguish the intersection of the guard
    h.old_partialDeterministic()
    // println(s"deter: ${h.transitionFunc}")
    h.old_addAuxVar()
    h
  }

  def safeAssumeAsConst(retr:os.CommandResult): Option[hoaParser] = 
  {
    val is = new ByteArrayInputStream(retr.out.string().getBytes())
    val bis = new BufferedInputStream(is)    
    val h = new hoaParser()
    HOAFParser.parseHOA(bis,h)    
    bis.close()
    is.close()

    if(h.old_partialDeterministic() && h.badAccs())
      Some(h)
    else
      None
  }

  def psl2TransitionSystem(h:hoaParser, p2target:Map[String,Target], extraInputNum:Int, BAStateNum:Int, accSignalNum:Int, circuit:Circuit, resetTarget:Target, chastmt:chaStmt, optiEn:Boolean = false):Tuple3[Seq[BVSymbol], State, Signal] = 
  {
    // println(s"BAAccept: ${h.accStates}")
    val baState = 
      if(chastmt == chaAssertStmt)
        BVSymbol("atSta" + BAStateNum + "_", h.stateBits)
      else if(chastmt == chaCoverStmt)
        BVSymbol("cvSta" + BAStateNum + "_", h.stateBits)
      else 
        BVSymbol("amSta" + BAStateNum + "_", h.stateBits)
      
    val extraInput:Seq[BVSymbol] = (extraInputNum until (extraInputNum + h.auxVarNum)).toSeq.map{case i: Int => BVSymbol("extInput"+i,1)}
    // extraInputNum = extraInputNum + h.auxVarNum
    val trans_ = h.transitionFunc
    
    var totalTransSeq = mutable.Map[Int, mutable.Seq[Tuple2[BVExpr,BVExpr]]]()
    for(i <- 0 until h.stateNum)
    {
      var TransSeq: mutable.Seq[Tuple2[BVExpr,BVExpr]] = mutable.Seq[Tuple2[BVExpr,BVExpr]]()
      for((k,v) <- trans_(i))
      {
        val cond = bddToSMTExpr(h.apNum, k, h.int2Ap, p2target, circuit, extraInput)
        val defa:BVExpr = BVLiteral(BigInt(v.head),h.stateBits)
        TransSeq :+= Tuple2(cond, defa)
      }
      totalTransSeq += (i -> TransSeq)
    }
    val baStateInit:BVExpr = BVLiteral(h.initState,h.stateBits)
    
    val irLookup = IRLookup(circuit)
    val resetExpr = FirrtlExpressionSemantics.toSMT(irLookup.expr(resetTarget.asInstanceOf[ReferenceTarget]))

    val baStateNext = BVIte(resetExpr, baStateInit, genTotalIte(baState, totalTransSeq, BVLiteral(h.stateNum,h.stateBits), h.stateBits))
    val baState_ = State(baState, None, Some(baStateNext))

    val BAAccept = h.accStates
    val acceptExpr = genAcc(baState, BAAccept, h.stateBits)
    
    val r = h.badAccs()
    // println(s"badAccs: $r")
    // println(s"optiEn2: $optiEn")
    val accSignal = if(chastmt == chaAssertStmt)
    {
      if(r && optiEn)
        Signal("atAcc" + accSignalNum, BVAnd(List(BVNot(resetExpr), acceptExpr)) , IsBad)
      else
        Signal("atAcc" + accSignalNum, acceptExpr, IsJustice)
    }
    else if(chastmt == chaCoverStmt)
    {
      // println(s"optiEn: $optiEn")
      if(optiEn)
        Signal("coAcc" + accSignalNum, BVAnd(List(BVNot(resetExpr), acceptExpr)) , IsBad)
      else
        Signal("coAcc" + accSignalNum, acceptExpr, IsJustice)
    }
    else
    {
      // println(s"optiEn: $optiEn")
      if(optiEn)
        Signal("amAcc" + accSignalNum, BVAnd(List(BVNot(acceptExpr))) , IsConstraint)
      else
        Signal("amAcc" + accSignalNum, acceptExpr, IsFair)
    }
    
    Tuple3(extraInput, baState_, accSignal)
    // if all accepting states are bad states, liveness to safety is not necessary
    // val accSignal = if (r){
    //   if (chastmt == chaAssertStmt)
    //     Signal("BAacc" + accSignalNum, BVAnd(List(BVNot(resetExpr), acceptExpr)) , IsBad)
    //   else 
    //     Signal("BAacc" + accSignalNum, BVAnd(List(BVNot(resetExpr), acceptExpr)) , IsConstraint)
    //   // chastmt match{
    //   //   case chaAssertStmt => Signal("BAacc" + accSignalNum, BVAnd(List(BVNot(resetExpr), acceptExpr)) , IsBad) 
    //   //   case chaAssumeStmt => Signal("BAacc" + accSignalNum, BVAnd(List(BVNot(resetExpr), acceptExpr)) , IsConstraint) 
    //   // }
    // }
    // else{
    //   println(s"this!!!: ${chastmt}")
    //   println(s"this!!!: ${chaAssertStmt == chaAssumeStmt}")
    //   if (chastmt == chaAssertStmt)
    //     Signal("BAacc" + accSignalNum, acceptExpr, IsJustice)
    //   else
    //     Signal("BAacc" + accSignalNum, acceptExpr, IsFair)

    //   //Some match-case bug!
    //   // chastmt match{
    //   //   case chaAssumeStmt => Signal("BAacc" + accSignalNum, acceptExpr, IsFair)  
    //   //   case chaAssertStmt => {println(IsJustice); Signal("BAacc" + accSignalNum, acceptExpr, IsJustice)}
    //   //   case _ => Signal("BAacc" + accSignalNum, acceptExpr, IsFair) 
    //   // }
    // } 
    // println(s"accSignal: $accSignal")
    //  println("extraInput")
    //  println(extraInput.toSeq)
    
  }
}
