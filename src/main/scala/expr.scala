package at.logic.gapt.expr

// Types

abstract class TA {
  def ->(that: TA) = new ->(this, that)
}
abstract class TAtomicA extends TA
abstract class TComplexA extends TA
object TAtomicA {
  def unapply(ta: TA) = ta match {
    case Tindex => Some(ta)
    case Ti => Some(ta)
    case To => Some(ta)
    case _ => None
  }
}

case object Tindex extends TAtomicA { override def toString = "ω" }
case object Ti extends TAtomicA { override def toString = "ι" }
case object To extends TAtomicA { override def toString = "ο" }

case class ->(in: TA, out: TA) extends TComplexA {
  override def toString = s"($in -> $out)"
}

// Type helpers

object FOLFunctionHeadType {
  def apply(arity: Int): TA = arity match {
    case 0 => Ti
    case n => Ti -> FOLFunctionHeadType(n - 1)
  }
  def unapply(t: TA): Option[Int] = t match {
    case Ti => Some(0)
    case Ti -> FOLFunctionHeadType(n) => Some(n + 1)
    case _ => None
  }
}

object FOLAtomHeadType {
  def apply(arity: Int): TA = arity match {
    case 0 => To
    case n => Ti -> FOLAtomHeadType(n - 1)
  }
  def unapply(t: TA): Option[Int] = t match {
    case To => Some(0)
    case Ti -> FOLAtomHeadType(n) => Some(n + 1)
    case _ => None
  }
}

// Defined symbols

object ForallQ {
  val symbol = "∀"

  def apply(qtype: TA) = Const(symbol, (qtype -> To) -> To)
  def unapply(exp: LambdaExpression): Option[TA] = exp match {
    case Const(sym, exptype) => unapply(sym, exptype)
    case _ => None
  }
  def unapply(pair: (String, TA)): Option[TA] = pair match {
    case (`symbol`, (qtype -> To) -> To) => Some(qtype)
    case _ => None
  }
}

object AndC {
  val symbol = "∧"

  def apply() = Const(symbol, To -> (To -> To))
  def unapply(exp: LambdaExpression): Boolean = exp match {
    case Const(sym, exptype) => unapply(sym, exptype)
    case _ => false
  }
  def unapply(pair: (String, TA)): Boolean = pair match {
    case (`symbol`, To -> (To -> To)) => true
    case _ => false
  }
}

object NegC {
  val symbol = "¬"

  def apply() = Const(symbol, To -> To)
  def unapply(exp: LambdaExpression): Boolean = exp match {
    case Const(sym, exptype) => unapply(sym, exptype)
    case _ => false
  }
  def unapply(pair: (String, TA)): Boolean = pair match {
    case (`symbol`, To -> To) => true
    case _ => false
  }
}

object TopC {
  val symbol = "⊤"

  def apply() = Const(symbol, To)
  def unapply(exp: LambdaExpression): Boolean = exp match {
    case Const(sym, exptype) => unapply(sym, exptype)
    case _ => false
  }
  def unapply(pair: (String, TA)): Boolean = pair match {
    case (`symbol`, To) => true
    case _ => false
  }
}

// Traits

trait PartialFOLTerm extends LambdaExpression {
  def numberOfArguments: Int
}

trait FOLTerm extends PartialFOLTerm {
  override def numberOfArguments = 0
}

trait FOLVar extends Var with FOLTerm

trait PartialFOLFormula extends LambdaExpression {
  def numberOfArguments: Int
}

trait FOLFormula extends PartialFOLFormula {
  override def numberOfArguments = 0
}

trait FOLFormulaWithBoundVariable extends LambdaExpression

trait LogicalSymbol extends LambdaExpression

trait FOLQuantifier extends LogicalSymbol

trait FOLConnective extends LogicalSymbol with PartialFOLFormula

// Expressions

abstract class LambdaExpression {
  def exptype: TA

  override def toString = this match {
    case All(Var(x, Ti), e) => s"∀$x.$e"
    case All(Var(x, t), e) => s"∀$x:$t.$e"
    case Ands(xs @ Seq(_, _, _*)) => s"(${xs mkString "∧"})"
    case FOLAtom(r, xs) => s"$r(${xs mkString ","})"
    case FOLFunction(f, xs) => s"$f(${xs mkString ","})"

    case Abs(x, t) => s"λ$x.$t"
    case App(x, y) => s"($x $y)"
    case Var(x, t) => s"$x"
    case Const(x, t) => s"$x"
  }
}

class Var private[expr] (val name: String, val exptype: TA) extends LambdaExpression {}
class Const private[expr] (val name: String, val exptype: TA) extends LambdaExpression

class App private[expr] (val function: LambdaExpression, val arg: LambdaExpression) extends LambdaExpression {
  val exptype: TA =
    function.exptype match {
      case (in -> out) if in == arg.exptype => out
      case _ => throw new IllegalArgumentException(
        s"Types don't fit while constructing application ($function : ${function.exptype}) ($arg : ${arg.exptype})")
    }
}

class Abs(val variable: Var, val term: LambdaExpression) extends LambdaExpression {
  val exptype: TA = variable.exptype -> term.exptype
}

object Var {
  def apply(name: String, exptype: TA) = exptype match {
    case Ti => new Var(name, exptype) with FOLVar
    case _ => new Var(name, exptype)
  }

  def unapply(e: LambdaExpression) = e match {
    case v: Var => Some(v.name, v.exptype)
    case _ => None
  }
}

object Const {
  def apply(name: String, exptype: TA) = (name, exptype) match {
    case ForallQ(Ti) => new Const(name, exptype) with FOLQuantifier
    case AndC() => new Const(name, exptype) with FOLConnective {
      override val numberOfArguments = 2
    }
    case NegC() => new Const(name, exptype) with FOLConnective {
      override val numberOfArguments = 1
    }
    case TopC() => new Const(name, exptype) with FOLConnective with FOLFormula

    case (_, Ti) => new Const(name, exptype) with FOLTerm
    case (_, FOLFunctionHeadType(n)) => new Const(name, exptype) with PartialFOLTerm {
      override val numberOfArguments = n
    }
    case (_, To) => new Const(name, exptype) with FOLFormula
    case (_, FOLAtomHeadType(n)) => new Const(name, exptype) with PartialFOLFormula {
      override val numberOfArguments = n
    }
    case _ => new Const(name, exptype)
  }

  def unapply(e: LambdaExpression) = e match {
    case c: Const => Some(c.name, c.exptype)
    case _ => None
  }
}

object App {
  def apply(f: LambdaExpression, a: LambdaExpression) = f match {
    case f: PartialFOLTerm => f.numberOfArguments match {
      case 1 => new App(f, a) with FOLTerm
      case n => new App(f, a) with PartialFOLTerm {
        override val numberOfArguments = n - 1
      }
    }
    case f: PartialFOLFormula => f.numberOfArguments match {
      case 1 => new App(f, a) with FOLFormula
      case n => new App(f, a) with PartialFOLFormula {
        override val numberOfArguments = n - 1
      }
    }
    case f: FOLQuantifier => a match {
      case a: FOLFormulaWithBoundVariable => new App(f, a) with FOLFormula
      case _ => new App(f, a)
    }
    case _ => new App(f, a)
  }
  @deprecated("This constructor has moved to Apps")
  def apply(function: LambdaExpression, arguments: List[LambdaExpression]): LambdaExpression = Apps(function, arguments)

  def unapply(e: LambdaExpression) = e match {
    case a: App => Some((a.function, a.arg))
    case _ => None
  }
}

object Apps {
  def apply(function: LambdaExpression, arguments: LambdaExpression*): LambdaExpression =
    apply(function, arguments toList)

  // create an n-ary application with left-associative parentheses
  def apply(function: LambdaExpression, arguments: List[LambdaExpression]): LambdaExpression = arguments match {
    case Nil => function
    case x :: ls => apply(App(function, x), ls)
  }

  def unapply(e: LambdaExpression): Some[(LambdaExpression, List[LambdaExpression])] = e match {
    case App(Apps(hd, args), arg) => Some((hd, args ::: List(arg)))
    case e => Some((e, List()))
  }
}

object Abs {
  def apply(v: Var, t: LambdaExpression) = t match {
    case t: FOLFormula if v.exptype == Ti =>
      new Abs(v, t) with FOLFormulaWithBoundVariable
    case _ => new Abs(v, t)
  }

  def apply(variables: List[Var], expression: LambdaExpression): LambdaExpression = variables match {
    case Nil => expression
    case x :: ls => Abs(x, apply(ls, expression))
  }
  def unapply(e: LambdaExpression) = e match {
    case a: Abs => Some((a.variable, a.term))
    case _ => None
  }
}

// Helpers

object NonLogicalConstant {
  def apply(sym: String, t: TA) = {
    val c = Const(sym, t)
    require(!c.isInstanceOf[LogicalSymbol])
    c
  }
  def unapply(e: LambdaExpression) = e match {
    case _: LogicalSymbol => None
    case Const(sym, t) => Some((sym, t))
    case _ => None
  }
}

object FOLAtom {
  def apply(sym: String, args: FOLTerm*): FOLFormula = FOLAtom(sym, args toList)
  def apply(sym: String, args: List[FOLTerm]): FOLFormula =
    Apps(Const(sym, FOLAtomHeadType(args.length)), args).asInstanceOf[FOLFormula]

  def unapply(e: LambdaExpression): Option[(String, List[FOLTerm])] = e match {
    case Apps(NonLogicalConstant(sym, FOLAtomHeadType(_)), args) if e.isInstanceOf[FOLFormula] =>
      Some((sym, args.asInstanceOf[List[FOLTerm]]))
    case _ => None
  }
}

object FOLFunction {
  def apply(sym: String, args: FOLTerm*): FOLTerm = FOLFunction(sym, args toList)
  def apply(sym: String, args: List[FOLTerm]): FOLTerm =
    Apps(Const(sym, FOLFunctionHeadType(args.length)), args).asInstanceOf[FOLTerm]

  def unapply(e: LambdaExpression): Option[(String, List[FOLTerm])] = e match {
    case Apps(NonLogicalConstant(sym, FOLFunctionHeadType(_)), args) if e.isInstanceOf[FOLTerm] =>
      Some((sym, args.asInstanceOf[List[FOLTerm]]))
    case _ => None
  }
}

object FOLVar {
  def apply(sym: String): FOLVar = Var(sym, Ti).asInstanceOf[FOLVar]
  def unapply(e: LambdaExpression) = e match {
    case Var(sym, Ti) => Some(sym)
    case _ => None
  }
}

object All {
  def apply(v: Var, formula: LambdaExpression): LambdaExpression =
    App(ForallQ(v.exptype), Abs(v, formula))
  def apply(v: FOLVar, formula: FOLFormula): FOLFormula =
    All(v, formula.asInstanceOf[LambdaExpression]).asInstanceOf[FOLFormula]

  def unapply(e: LambdaExpression): Option[(Var, LambdaExpression)] = e match {
    // TODO: eta-expansion?
    case App(ForallQ(_), Abs(v, formula)) => Some((v, formula))
    case _ => None
  }

  def unapply(f: FOLFormula): Option[(FOLVar, FOLFormula)] = f.asInstanceOf[LambdaExpression] match {
    case All(v: FOLVar, formula: FOLFormula) => Some((v, formula))
    case _ => None
  }
}

object And {
  def apply(a: LambdaExpression, b: LambdaExpression): LambdaExpression =
    Apps(AndC(), a, b)
  def apply(a: FOLFormula, b: FOLFormula): FOLFormula =
    And(a, b.asInstanceOf[LambdaExpression]).asInstanceOf[FOLFormula]

  def unapply(formula: LambdaExpression): Option[(LambdaExpression, LambdaExpression)] = formula match {
    case App(App(AndC(), a), b) => Some((a, b))
    case _ => None
  }
  def unapply(formula: FOLFormula): Option[(FOLFormula, FOLFormula)] = formula.asInstanceOf[LambdaExpression] match {
    case And(a: FOLFormula, b: FOLFormula) => Some((a, b))
    case _ => None
  }
}

object Ands {
  def apply(conjs: LambdaExpression*): LambdaExpression = conjs match {
    case Seq() => TopC()
    case Seq(conj) => conj
    case Seq(conj, rest @ _*) => And(conj, Ands(rest: _*))
  }
  def apply(conjs: FOLFormula*): FOLFormula =
    Ands(conjs.asInstanceOf[Seq[LambdaExpression]]: _*).asInstanceOf[FOLFormula]

  def unapply(formula: LambdaExpression): Some[List[LambdaExpression]] = formula match {
    case And(Ands(as), Ands(bs)) => Some(as ::: bs)
    case a => Some(List(a))
  }
  def unapply(formula: FOLFormula): Some[List[FOLFormula]] = formula match {
    case And(Ands(as), Ands(bs)) => Some(as ::: bs)
    case a => Some(List(a))
  }
}

object Neg {
  def apply(a: LambdaExpression): LambdaExpression = App(NegC(), a)
  def apply(a: FOLFormula): FOLFormula = apply(a.asInstanceOf[LambdaExpression]).asInstanceOf[FOLFormula]
  def unapply(e: LambdaExpression): Option[LambdaExpression] = e match {
    case App(NegC(), a) => Some(a)
    case _ => None
  }
  def unapply(e: FOLFormula): Option[FOLFormula] = e.asInstanceOf[LambdaExpression] match {
    case Neg(a: FOLFormula) => Some(a)
    case _ => None
  }
}

object Top {
  def apply(): FOLFormula = TopC().asInstanceOf[FOLFormula]
  def unapply(e: LambdaExpression): Boolean = TopC.unapply(e)
}
