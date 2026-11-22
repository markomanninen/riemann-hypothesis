module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodIdempotentIrreducibleCharacterGenericSumNeZe
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMultOneDimOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimParabolicInductionCuspidalEqOneStatement

@[expose] public section

open Formalism.BasicNotions GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_idempotent_irreducible_character_generic_sum_ne_zero : ∀ (D : D7), GrpSide D → ∀ [Fintype (G0g D.nd)] (U : Subgroup (G0g D.nd)) [Fintype U], U = Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r → ∀ ψ : U →* ℂˣ, Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ → 2 ≤ D.R.r → ∀ χ : G0g D.nd → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, D.ntypes.e0.coeff g * χ g = χ 1 → ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0 := by
  first | exact @GlobalTheory.WhittakerMeets.sum_ne_zero | exact GlobalTheory.WhittakerMeets.sum_ne_zero | (intros; apply GlobalTheory.WhittakerMeets.sum_ne_zero <;> assumption)
