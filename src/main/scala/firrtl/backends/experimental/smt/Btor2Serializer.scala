// SPDX-License-Identifier: Apache-2.0
// Author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package firrtl.backends.experimental.smt

import scala.collection.mutable

object Btor2Serializer {
  def serialize(sys: TransitionSystem, skipOutput: Boolean = false): Iterable[String] = {
    new Btor2Serializer().run(sys, skipOutput)
  }
}

private class Btor2Serializer private () {
  private val symbols = mutable.HashMap[String, Int]()
  private val lines = mutable.ArrayBuffer[String]()
  private var index = 1

  private def line(l: String): Int = {
    val ii = index
    lines += s"$ii $l"
    index += 1
    ii
  }

  private def comment(c: String): Unit = { lines += s"; $c" }
  private def trailingComment(c: String): Unit = {
    val lastLine = lines.last
    val newLine = if (lastLine.contains(';')) { lastLine + " " + c }
    else { lastLine + " ; " + c }
    lines(lines.size - 1) = newLine
  }

  // bit vector type serialization
  private val bitVecTypeCache = mutable.HashMap[Int, Int]()

  private def t(width: Int): Int = bitVecTypeCache.getOrElseUpdate(width, line(s"sort bitvec $width"))

  // bit vector expression serialization
  private def s(expr: BVExpr): Int = expr match {
    case BVLiteral(value, width) => lit(value, width)
    case BVSymbol(name, _)       => symbols.getOrElse(name, throw new RuntimeException(s"Unknown symbol: $name"))
    case BVExtend(e, 0, _)       => s(e)
    case BVExtend(e, by, true)   => line(s"sext ${t(expr.width)} ${s(e)} $by")
    case BVExtend(e, by, false)  => line(s"uext ${t(expr.width)} ${s(e)} $by")
    case BVSlice(e, hi, lo) =>
      if (lo == 0 && hi == e.width - 1) { s(e) }
      else {
        line(s"slice ${t(expr.width)} ${s(e)} $hi $lo")
      }
    case BVNot(BVEqual(a, b))                            => binary("neq", expr.width, a, b)
    case BVNot(BVNot(e))                                 => s(e)
    case BVNot(e)                                        => unary("not", expr.width, e)
    case BVNegate(e)                                     => unary("neg", expr.width, e)
    case BVReduceAnd(e)                                  => unary("redand", expr.width, e)
    case BVReduceOr(e)                                   => unary("redor", expr.width, e)
    case BVReduceXor(e)                                  => unary("redxor", expr.width, e)
    case BVImplies(BVLiteral(v, 1), b) if v == 1         => s(b)
    case BVImplies(a, b)                                 => binary("implies", expr.width, a, b)
    case BVEqual(a, b)                                   => binary("eq", expr.width, a, b)
    case ArrayEqual(a, b)                                => line(s"eq ${t(expr.width)} ${s(a)} ${s(b)}")
    case BVComparison(Compare.Greater, a, b, false)      => binary("ugt", expr.width, a, b)
    case BVComparison(Compare.GreaterEqual, a, b, false) => binary("ugte", expr.width, a, b)
    case BVComparison(Compare.Greater, a, b, true)       => binary("sgt", expr.width, a, b)
    case BVComparison(Compare.GreaterEqual, a, b, true)  => binary("sgte", expr.width, a, b)
    case BVOp(op, a, b)                                  => binary(s(op), expr.width, a, b)
    case BVConcat(a, b)                                  => binary("concat", expr.width, a, b)
    case call: BVFunctionCall => s(functionCallToArrayRead(call))
    case ArrayRead(array, index) =>
      line(s"read ${t(expr.width)} ${s(array)} ${s(index)}")
    case BVIte(cond, tru, fals) =>
      line(s"ite ${t(expr.width)} ${s(cond)} ${s(tru)} ${s(fals)}")
    case b @ BVAnd(terms) => variadic("and", b.width, terms)
    case b @ BVOr(terms)  => variadic("or", b.width, terms)
    case forall: BVForall =>
      throw new RuntimeException(s"Quantifiers are not supported by the btor2 format: ${forall}")
  }

  private def s(op: Op.Value): String = op match {
    case Op.Xor                  => "xor"
    case Op.ArithmeticShiftRight => "sra"
    case Op.ShiftRight           => "srl"
    case Op.ShiftLeft            => "sll"
    case Op.Add                  => "add"
    case Op.Mul                  => "mul"
    case Op.Sub                  => "sub"
    case Op.SignedDiv            => "sdiv"
    case Op.UnsignedDiv          => "udiv"
    case Op.SignedMod            => "smod"
    case Op.SignedRem            => "srem"
    case Op.UnsignedRem          => "urem"
  }

  private def unary(op: String, width: Int, e: BVExpr): Int = line(s"$op ${t(width)} ${s(e)}")

  private def binary(op: String, width: Int, a: BVExpr, b: BVExpr): Int =
    line(s"$op ${t(width)} ${s(a)} ${s(b)}")

  private def variadic(op: String, width: Int, terms: List[BVExpr]): Int = terms match {
    case Seq() | Seq(_) => throw new RuntimeException(s"expected at least two elements in variadic op $op")
    case Seq(a, b)      => binary(op, width, a, b)
    case head :: tail =>
      val tailId = variadic(op, width, tail)
      line(s"$op ${t(width)} ${s(head)} ${tailId}")
  }

  private def lit(value: BigInt, w: Int): Int = {
    val typ = t(w)
    lazy val mask = (BigInt(1) << w) - 1
    if (value == 0) line(s"zero $typ")
    else if (value == 1) line(s"one $typ")
    else if (value == mask) line(s"ones $typ")
    else {
      val digits = value.toString(2)
      val padded = digits.reverse.padTo(w, '0').reverse
      line(s"const $typ $padded")
    }
  }

  // array type serialization
  private val arrayTypeCache = mutable.HashMap[(Int, Int), Int]()

  private def t(indexWidth: Int, dataWidth: Int): Int =
    arrayTypeCache.getOrElseUpdate((indexWidth, dataWidth), line(s"sort array ${t(indexWidth)} ${t(dataWidth)}"))

  // array expression serialization
  private def s(expr: ArrayExpr): Int = expr match {
    case ArraySymbol(name, _, _) => symbols(name)
    case ArrayStore(array, index, data) =>
      line(s"write ${t(expr.indexWidth, expr.dataWidth)} ${s(array)} ${s(index)} ${s(data)}")
    case ArrayIte(cond, tru, fals) =>
      // println("WARN: ITE on array is probably not supported by btor2")
      // While the spec does not seem to allow array ite, it seems to be supported in practice.
      // It is essential to model memories, so any support in the wild should be fairly well tested.
      line(s"ite ${t(expr.indexWidth, expr.dataWidth)} ${s(cond)} ${s(tru)} ${s(fals)}")
    case ArrayConstant(e, indexWidth) =>
      // The problem we are facing here is that the only way to create a constant array from a bv expression
      // seems to be to use the bv expression as the init value of a state variable.
      // Thus we need to create a fake state for every array init expression.
      arrayConstants.getOrElseUpdate(
        e.toString, {
          comment(s"$expr")
          val eId = s(e)
          val tpeId = t(indexWidth, e.width)
          val state = line(s"state $tpeId")
          line(s"init $tpeId $state $eId")
          state
        }
      )
    case f: ArrayFunctionCall =>
      throw new RuntimeException(s"The btor2 format does not support uninterpreted functions that return arrays!: $f")
  }
  private val arrayConstants = mutable.HashMap[String, Int]()

  private def s(expr: SMTExpr): Int = expr match {
    case b: BVExpr    => s(b)
    case a: ArrayExpr => s(a)
  }

  // serialize the type of the expression
  private def t(expr: SMTExpr): Int = expr match {
    case b: BVExpr    => t(b.width)
    case a: ArrayExpr => t(a.indexWidth, a.dataWidth)
  }

  private def functionCallToArrayRead(call: BVFunctionCall): BVExpr = {
    if (call.args.isEmpty) {
      BVSymbol(call.name, call.width)
    } else {
      val args: List[BVExpr] = call.args.map {
        case b: BVExpr => b
        case other => throw new RuntimeException(s"Unsupported call argument: $other in $call")
      }
      val index = concat(args)
      val a = ArraySymbol(call.name, indexWidth = index.width, dataWidth = call.width)
      ArrayRead(a, index)
    }
  }
  private def concat(e: Iterable[BVExpr]): BVExpr = {
    require(e.nonEmpty)
    e.reduce((a, b) => BVConcat(a, b))
  }

  def run(sys: TransitionSystem, skipOutput: Boolean): Iterable[String] = {
    def declare(name: String, lbl: Option[SignalLabel], expr: => Int): Unit = {
      assert(!symbols.contains(name), s"Trying to redeclare `$name`")
      val id = expr
      symbols(name) = id
      // add label
      lbl match {
        case Some(IsOutput)     => if (!skipOutput) line(s"output $id ; $name")
        case Some(IsConstraint) => line(s"constraint $id ; $name")
        case Some(IsBad)        => line(s"bad $id ; $name")
        case Some(IsFair)       => line(s"fair $id ; $name")
        case Some(IsJustice)    => line(s"justice $id ; $name")
        case _ =>
      }
      // add trailing comment
      sys.comments.get(name).foreach(trailingComment)
    }

    // header
    if (sys.header.nonEmpty) {
      sys.header.split('\n').foreach(comment)
    }

    // declare inputs
    sys.inputs.foreach { ii =>
      declare(ii.name, None, line(s"input ${t(ii.width)} ${ii.name}"))
    }

    // declare uninterpreted functions a constant arrays
    val ufs = TransitionSystem.findUninterpretedFunctions(sys)
    ufs.foreach { foo =>
      // only functions returning bit-vectors are supported!
      val bvSym = foo.sym.asInstanceOf[BVSymbol]
      val sym = if (foo.args.isEmpty) { bvSym }
      else {
        ArraySymbol(bvSym.name, foo.args.map(_.asInstanceOf[BVExpr].width).sum, bvSym.width)
      }
      comment(foo.toString)
      declare(sym.name, None, line(s"state ${t(sym)} ${sym.name}"))
      line(s"next ${t(sym)} ${s(sym)} ${s(sym)}")
    }

    // define state init
    sys.states.foreach { st =>
      // calculate init expression before declaring the state
      // this is required by btormc (presumably to avoid cycles in the init expression)
      val initId = st.init.map {
        // only in the context of initializing a state can we use a bv expression to model an array
        case ArrayConstant(e, _) => comment(s"${st.sym}.init"); s(e)
        case init                => comment(s"${st.sym}.init"); s(init)
      }
      declare(st.sym.name, None, line(s"state ${t(st.sym)} ${st.sym.name}"))
      st.init.foreach { init => line(s"init ${t(init)} ${s(st.sym)} ${initId.get}") }
    }

    // define all other signals
    sys.signals.foreach { signal =>
      declare(signal.name, Some(signal.lbl), s(signal.e))
    }

    // define state next
    sys.states.foreach { st =>
      st.next.foreach { next =>
        comment(s"${st.sym}.next")
        line(s"next ${t(next)} ${s(st.sym)} ${s(next)}")
      }
    }

    lines
  }
}
