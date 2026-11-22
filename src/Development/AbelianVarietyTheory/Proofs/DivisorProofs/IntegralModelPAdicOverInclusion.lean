module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointOnModelPullbackCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentEvLieOfLieTie

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel

theorem exists_denom (p : ℕ) [Fact p.Prime] : ∀ (m : ℕ) (d : Fin m → ℂ_[p]), ∃ δ : 𝓞_ℂ_[p],
    (δ : ℂ_[p]) ≠ 0 ∧ ∀ l, (δ : ℂ_[p]) * d l ∈ 𝓞_ℂ_[p] := by
  intro m
  induction m with
  | zero => exact fun d => ⟨1, by simp, fun l => l.elim0⟩
  | succ m ih =>
    intro d
    obtain ⟨δ, hδ, hl⟩ := ih (Fin.tail d)
    by_cases ha : (δ : ℂ_[p]) * d 0 ∈ 𝓞_ℂ_[p]
    · refine ⟨δ, hδ, fun l => ?_⟩
      refine Fin.cases ha (fun l => ?_) l
      exact hl l
    · have hne : (δ : ℂ_[p]) * d 0 ≠ 0 := fun h => ha (h ▸ (𝓞_ℂ_[p]).zero_mem)
      have hinv : ((δ : ℂ_[p]) * d 0)⁻¹ ∈ 𝓞_ℂ_[p] := ((𝓞_ℂ_[p]).mem_or_inv_mem _).resolve_left ha
      refine ⟨δ * ⟨_, hinv⟩, ?_, fun l => ?_⟩
      · change (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ ≠ 0
        exact mul_ne_zero hδ (inv_ne_zero hne)
      · change (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ * d l ∈ 𝓞_ℂ_[p]
        refine Fin.cases ?_ (fun l => ?_) l
        · rw [show (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ * d 0 = 1 by
            rw [_root_.mul_comm (δ : ℂ_[p]), _root_.mul_assoc]; exact inv_mul_cancel₀ hne]
          exact (𝓞_ℂ_[p]).one_mem
        · rw [show (δ : ℂ_[p]) * ((δ : ℂ_[p]) * d 0)⁻¹ * d l.succ = ((δ : ℂ_[p]) * d 0)⁻¹ * ((δ : ℂ_[p]) * Fin.tail d l) by
            simp only [Fin.tail]; ring]
          exact (𝓞_ℂ_[p]).mul_mem _ _ hinv (hl l)


end GlobalTheory.FlatModel

end
