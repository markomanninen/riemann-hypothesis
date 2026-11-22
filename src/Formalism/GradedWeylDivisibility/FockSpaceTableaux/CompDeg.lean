module

public import Formalism.GradedWeylDivisibility.StatementC
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCcompLemmas

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem componentDegree : CompDeg := by
  intro B _ r n l j ω s f hf
  rw [← lccomp_component_colAddGen]
  exact (lccomp_degreeOf_component_le _ _ _ _).trans hf

end Formalism.GradedWeylDivisibility
