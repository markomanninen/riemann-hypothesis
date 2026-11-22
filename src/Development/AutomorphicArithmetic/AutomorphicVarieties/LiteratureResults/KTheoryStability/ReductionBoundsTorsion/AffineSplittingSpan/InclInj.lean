module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer

@[expose] public section

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SplitAffineSpectral

def EvCob : Prop :=
  ∀ (G : Type) [Group G] (j : ℕ) (e : (Fin (j + 1) → G) → ℝ), Inv (MonoidHom.id G) e →
    ∀ z : Chn G (j + 1), IsCyc z → ev (MonoidHom.id G) (dC e) 1 z = 0

namespace GluingInclusion

set_option linter.unusedSectionVars false

variable (L : Type) [Field L] [NumberField L] (n r : ℕ)

end GluingInclusion

end PositivityTheory.KB.SplitAffineSpectral

end
