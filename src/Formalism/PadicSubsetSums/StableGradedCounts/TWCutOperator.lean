module

public import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral
public import Formalism.PadicSubsetSums.StableGradedCounts.TWCentralIdempotentIntegral

@[expose] public section

namespace Formalism.IrreducibleCountingLemmas.TW

theorem asAlgebraHom_apply_eq_sum {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (x : MonoidAlgebra K G) (v : V) :
    ρ.asAlgebraHom x v = ∑ g ∈ x.coeff.support, x.coeff g • ρ g v := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum,
    LinearMap.sum_apply]
  rfl

end Formalism.IrreducibleCountingLemmas.TW
