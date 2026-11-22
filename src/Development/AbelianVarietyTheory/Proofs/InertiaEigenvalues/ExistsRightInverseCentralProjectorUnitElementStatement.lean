module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRightInverseCentralProjectorUnitElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UupEqOneOfLeOne
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc

@[expose] public section

open GlobalTheory.MeetsGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_right_inverse_centralProjectorUnitElement : ∀ {G : Type} [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (ψ : U →* ℂˣ) (e : MonoidAlgebra ℂ G), e * e = e → (∀ a, e * a = a * e) → (∀ χ : G → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, e.coeff g * χ g = χ 1 → ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0) → ∃ v : MonoidAlgebra ℂ G, uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) e * v = 1 := by
  first | exact @GlobalTheory.MeetsUnit.exists_rightInv_uElt | exact GlobalTheory.MeetsUnit.exists_rightInv_uElt | (intros; apply GlobalTheory.MeetsUnit.exists_rightInv_uElt <;> assumption)
