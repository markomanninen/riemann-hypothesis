module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

@[expose] public section

noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.Hk3.Inh

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_two {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (hq : Odd q) : Valued.v (2 : L) = 1 := by
  obtain ⟨-, -, -, -, -, h2, hc⟩ := h
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hc' : Nat.card (IsLocalRing.ResidueField O) = q ^ 2 := hc
  haveI : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero (by rw [hc']; positivity)
  haveI := Fintype.ofFinite (IsLocalRing.ResidueField O)
  have h0 : ((q ^ 2 : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← hc', Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
  have hle : Valued.v (2 : L) ≤ 1 := (2 : O).2
  by_contra hne
  have hlt : Valued.v (2 : L) < 1 := lt_of_le_of_ne hle hne
  have hm : (2 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [Valuation.mem_maximalIdeal_iff]; exact hlt
  have h2' : (2 : IsLocalRing.ResidueField O) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff (2 : O)).2 hm
    rwa [map_ofNat] at this
  obtain ⟨k, hk⟩ : Odd (q ^ 2) := hq.pow
  rw [hk] at h0
  push_cast at h0
  rw [h2'] at h0
  simp at h0




section Main

variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ}







end Main

section Laurent

end Laurent

end GlobalTheory.Hk3.Inh

end
