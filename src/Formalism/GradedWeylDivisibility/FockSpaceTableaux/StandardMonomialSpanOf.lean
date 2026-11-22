module

public import Formalism.GradedWeylDivisibility.StatementC

@[expose] public section

namespace Formalism.GradedWeylDivisibility

theorem standardMonomialSpanOf : StandardMonomialSpanOf := by
  intro h r n ν _
  exact h ℤ r n ν

end Formalism.GradedWeylDivisibility
