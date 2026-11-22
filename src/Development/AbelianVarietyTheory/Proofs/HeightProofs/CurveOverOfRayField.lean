module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardEqIffStabilizer
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberSetSubsetRayField
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.RayExistCurve

section Quadratic

variable {K : Type} [Field K] [NumberField K] {d : ℕ}

end Quadratic


set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in
theorem _root_.GlobalTheory.FieldSize.RayExistCurve.finrank_adjoin {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    FiniteDimensional ℚ ℚ⟮r⟯ ∧ Module.finrank ℚ ℚ⟮r⟯ = 2 := by
  open Polynomial in
  have hroot : aeval r (X ^ 2 + C (d : ℚ)) = 0 := by simp [hr]
  have hmon : (X ^ 2 + C (d : ℚ)).Monic := monic_X_pow_add_C _ (by norm_num)
  have hint : IsIntegral ℚ r := ⟨_, hmon, by simpa [aeval_def] using hroot⟩
  have hdeg : (X ^ 2 + C (d : ℚ)).natDegree = 2 := natDegree_X_pow_add_C
  have hirr : Irreducible (X ^ 2 + C (d : ℚ)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; decide
    · intro x hx
      have hx' : x ^ 2 + (d : ℚ) = 0 := by simpa using hx
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      nlinarith [sq_nonneg x]
  have hmin : minpoly ℚ r = X ^ 2 + C (d : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm
  refine ⟨IntermediateField.adjoin.finiteDimensional hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint, hmin, hdeg]

end GlobalTheory.FieldSize.RayExistCurve
