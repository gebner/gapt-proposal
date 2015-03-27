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

// Traits

trait PartialFOLTerm extends LambdaExpression {
  def numberOfArguments: Int
}

trait FOLTerm extends PartialFOLTerm {
  override def numberOfArguments = 0
}

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
      case (in -> out) => out
      case _ => throw new IllegalArgumentException(
        s"Types don't fit while constructing application ($function : ${function.exptype}) ($arg : ${arg.exptype})")
    }
}

class Abs(val variable: Var, val term: LambdaExpression) extends LambdaExpression {
  val exptype: TA = variable.exptype -> term.exptype
}

object Var {
  def apply(name: String, exptype: TA) = exptype match {
    case Ti => new Var(name, exptype) with FOLTerm
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

  // create an n-ary application with left-associative parentheses
  def apply(function: LambdaExpression, arguments: List[LambdaExpression]): LambdaExpression = arguments match {
    case Nil => function
    case x :: ls => apply(App(function, x), ls)
  }
  def unapply(e: LambdaExpression) = e match {
    case a: App => Some((a.function, a.arg))
    case _ => None
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

