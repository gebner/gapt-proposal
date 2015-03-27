package at.logic.gapt

import at.logic.gapt.expr._

object atoms {
  def apply(formula: FOLFormula): List[FOLFormula] = formula match {
    case a @ FOLAtom(_, _) => List(a)

    case All(x, f) => atoms(f)
    case And(f, g) => atoms(f) ::: atoms(g)
    case Neg(f) => atoms(f)
    case Top() => List()
  }
}

object subTerms {
  def apply(term: FOLTerm): List[FOLTerm] = term :: (term match {
    case FOLFunction(_, arguments) => arguments flatMap (subTerms(_))
    case FOLVar(_) => List()
  })
}