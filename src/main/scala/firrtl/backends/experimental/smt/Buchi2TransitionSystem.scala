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

  def genIte(bvs:Seq[Tuple2[BVExpr,BVExpr]], defau: BVExpr): BVExpr =
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

    def genTotalIte(baState:BVSymbol, bvs:Map[Int,Seq[Tuple2[BVExpr,BVExpr]]], defau: BVExpr, stateBits:Int): BVExpr =
    {
    println(s"remaining: ${bvs.size}")
    if(bvs.isEmpty)
    {
        defau
    }
    else
    {
        val ffirst = bvs.head
        val remaining = bvs - (ffirst._1)
        println(ffirst._2)
        println(genIte(ffirst._2, defau))
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
        val low:BVExpr = bddToSMTExpr(apNum,bdd.low(),int2Ap,p2target,circuit,auxVar)
        val high:BVExpr = bddToSMTExpr(apNum,bdd.high(),int2Ap,p2target,circuit,auxVar)
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
        BVIte(curExpr,high,low)
    }
    }

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
        println("---")           
        println(retr.out.string)
        println("---")

        val is = new ByteArrayInputStream(retr.out.string.getBytes())
        // 转 BufferedInputStream
        val bis = new BufferedInputStream(is)    
        // 打印
        //Stream.continually(bis.read()).takeWhile(_ != -1).foreach(println(_))
        val h = new hoaParser()
        HOAFParser.parseHOA(bis,h)    
        bis.close()
        is.close()
        
        println("//////////////////////////")
        println(h.transitionFunc)
        h.partialDeterministic()
        println("//////////////////////////")
        println(h.transitionFunc)
        h.addAuxVar()
        println("//////////////////////////")
        println(h.transitionFunc)

        //BVSymbol(p.name, bitWidth(p.tpe).toInt)
        println(s"auxVarNum: ${h.auxVarNum}")
        println(s"apNum: ${h.apNum}")
        h
    }

  def psl2TransitionSystem(h:hoaParser, p2target:Map[String,Target], extraInputNum:Int, BAStateNum:Int, accSignalNum:Int, circuit:Circuit):Tuple3[Seq[BVSymbol], State, Signal] = 
  {
    val baState = BVSymbol("baState" + BAStateNum, h.stateBits)
    val extraInput:Seq[BVSymbol] = (extraInputNum until (extraInputNum + h.auxVarNum)).toSeq.map{case i: Int => BVSymbol("extInput"+i,1)}
    // extraInputNum = extraInputNum + h.auxVarNum
    val trans_ = h.transitionFunc
    
    var totalTransSeq = Map[Int, mutable.Seq[Tuple2[BVExpr,BVExpr]]]()
    for(i <- 0 until h.stateNum)
    {
      var TransSeq: mutable.Seq[Tuple2[BVExpr,BVExpr]] = mutable.Seq[Tuple2[BVExpr,BVExpr]]()
      for((k,v) <- trans_(i))
      {
        println(s"k:  $k")
        val cond = bddToSMTExpr(h.apNum, k, h.int2Ap, p2target, circuit, extraInput)
        //val cond:BVExpr = BVAnd( BVEqual(baState, BVLiteral(BigInt(i),h.stateBits)), bddToSMTExpr(h.apNum, k, h.int2Ap, p2target, circuit, extraInput) ) 
        val defa:BVExpr = BVLiteral(BigInt(v.head),h.stateBits)
        TransSeq :+= Tuple2(cond, defa)
        //println(ttemp_)
      }
      totalTransSeq += (i -> TransSeq)
    }
    val baStateInit:BVExpr = BVLiteral(h.initState,h.stateBits)
    val baStateNext = genTotalIte(baState, totalTransSeq, BVLiteral(h.stateNum,h.stateBits), h.stateBits)
    val baState_ = State(baState, Some(baStateInit), Some(baStateNext))

    val BAAccept = h.accStates
    val acceptExpr = genAcc(baState, BAAccept, h.stateBits)
    val accSignal = Signal("BAacc" + accSignalNum, acceptExpr, IsJustice)
    println("extraInput")
    println(extraInput.toSeq)
    Tuple3(extraInput, baState_, accSignal)
  }
}
