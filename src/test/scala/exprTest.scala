package at.logic.gapt.expr
import org.specs2.mutable._

class ExprTest extends Specification {
  "FOL traits for expressions constructed by hand" should {
    val f = Const("f", FOLFunctionHeadType(3))
    val c = Const("c", Ti)
    val R = Const("R", FOLAtomHeadType(2))
    val x = Var("x", Ti)

    "be on terms" in {
      Apps(f, c, c, c) must beAnInstanceOf[FOLTerm]

      x must beAnInstanceOf[FOLVar]
    }

    "be on formulas" in {
      R must beAnInstanceOf[PartialFOLFormula]
      R.asInstanceOf[PartialFOLFormula].numberOfArguments must be_==(2)

      App(R, c) must beAnInstanceOf[PartialFOLFormula]
      Apps(R, c, c) must beAnInstanceOf[FOLFormula]

      Abs(x, Apps(R, x, x)) must beAnInstanceOf[FOLFormulaWithBoundVariable]
      App(ForallQ(Ti), Abs(x, Apps(R, x, x))) must beAnInstanceOf[FOLFormula]

      AndC() must beAnInstanceOf[PartialFOLFormula]
      Apps(AndC(), Apps(R, c, c), Apps(R, c, c)) must beAnInstanceOf[FOLFormula]

      TopC() must beAnInstanceOf[FOLFormula]
      TopC() must beAnInstanceOf[LogicalSymbol]
    }
  }

  "FOL helpers" should {
    "have correct static types" in {
      val a: FOLTerm = FOLFunction("f", FOLVar("x"), FOLFunction("c"))
      val b: FOLFormula = FOLAtom("R", FOLVar("x"), FOLFunction("c"))
      val c: FOLFormula = And(FOLAtom("R"), FOLAtom("P"))
      val d: FOLFormula = All(FOLVar("x"), FOLAtom("R", FOLVar("x")))
      val e: FOLFormula = Top()
      ok
    }
  }

  "toString" should {
    "terminate" in {
      FOLAtom("P").toString must beEqualTo("P()")
    }
  }
}