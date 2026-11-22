module

public import Formalism.GradedWeylDivisibility.StatementB
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockqLemmas

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem fischerInnerRatBilinear : FockQBilin := fun _ f f' g c =>
  ⟨lfockq_add_left f f' g, lfockq_smul_left c f g⟩

end Formalism.GradedWeylDivisibility
