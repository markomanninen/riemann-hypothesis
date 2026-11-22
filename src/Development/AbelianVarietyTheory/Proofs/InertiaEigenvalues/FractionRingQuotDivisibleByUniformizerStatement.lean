module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotDivisibleByUniformizer
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply

@[expose] public section

open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRingQuot_divisible_by_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ y : Formalism.NG.KO O, ϖ • y = x := by
  first | exact @GlobalTheory.KO_divisible_by_uniformiser | exact GlobalTheory.KO_divisible_by_uniformiser | (intros; apply GlobalTheory.KO_divisible_by_uniformiser <;> assumption)
