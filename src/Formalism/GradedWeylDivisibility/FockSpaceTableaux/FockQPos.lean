module

public import Formalism.GradedWeylDivisibility.StatementB
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockqLemmas

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem fischerInnerRatPos : FockQPos :=
  fun _ f g => ⟨lfockq_symm f g, fun hf => lfockq_self_pos f hf⟩

end Formalism.GradedWeylDivisibility
