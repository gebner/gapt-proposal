package at.logic.gapt.expr
import org.specs2.mutable._

class ExprTest extends Specification {
  "FOL traits" should {
    val f = Const("f", FOLFunctionHeadType(3))
    val c = Const("c", Ti)
    val R = Const("R", FOLAtomHeadType(2))
    val x = Var("x", Ti)

    "terms" in {
      App(f, List(c, c, c)) must beAnInstanceOf[FOLTerm]
    }

    "formulas" in {
      R must beAnInstanceOf[PartialFOLFormula]
      R.asInstanceOf[PartialFOLFormula].numberOfArguments must be_==(2)

      App(R, c) must beAnInstanceOf[PartialFOLFormula]
      App(R, List(c, c)) must beAnInstanceOf[FOLFormula]

      Abs(x, App(R, List(x, x))) must beAnInstanceOf[FOLFormulaWithBoundVariable]
      App(ForallQ(Ti), Abs(x, App(R, List(x, x)))) must beAnInstanceOf[FOLFormula]

      AndC() must beAnInstanceOf[PartialFOLFormula]
      App(AndC(), List(App(R, List(c, c)), App(R, List(c, c)))) must beAnInstanceOf[FOLFormula]
    }
  }
}