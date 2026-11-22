module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotKilledByPowUniformizer
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply

@[expose] public section

open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRingQuot_killed_by_pow_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  first | exact @GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer | exact GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer | (intros; apply GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer <;> assumption)
