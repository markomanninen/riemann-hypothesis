module

public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs

@[expose] public section

noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI.I4

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)] {K'' : Type} [Fintype K''] {ι'' : K'' → Type}
  [∀ b, Fintype (ι'' b)]

@[simp] theorem vdeg_zero (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) : vdeg O y 0 = 1 := by simp [vdeg]

theorem vdeg_join (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) (a' : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a a') = vdeg O y a * vdeg O y' a' := by
  unfold vdeg
  rw [Fintype.prod_sum_type]
  rfl

theorem vdeg_join_inl (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a 0) = vdeg O y a := by rw [vdeg_join, vdeg_zero, mul_one]

theorem vdeg_join_inr (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a' : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim 0 a') = vdeg O y' a' := by rw [vdeg_join, vdeg_zero, one_mul]

namespace ValEq

variable {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {y'' : (Σ b, ι'' b) → Ω}

theorem of_eq {a : K → ℤ} {a' : K' → ℤ} (h : ∀ O : ValuationSubring Ω, vdeg O y a = vdeg O y' a') : ValEq k y a y' a' :=
  ⟨1, one_ne_zero, fun O _ => by rw [h O, map_one, one_mul]⟩

theorem symm {a : K → ℤ} {a' : K' → ℤ} (h : ValEq k y a y' a') : ValEq k y' a' y a := by
  obtain ⟨ρ, h0, h⟩ := h
  refine ⟨ρ⁻¹, inv_ne_zero h0, fun O hO => ?_⟩
  rw [h O hO, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul]

theorem trans {a : K → ℤ} {a' : K' → ℤ} {a'' : K'' → ℤ} (h : ValEq k y a y' a') (h' : ValEq k y' a' y'' a'') :
    ValEq k y a y'' a'' := by
  obtain ⟨ρ, h0, h⟩ := h
  obtain ⟨ρ', h0', h'⟩ := h'
  exact ⟨ρ * ρ', mul_ne_zero h0 h0', fun O hO => by rw [h O hO, h' O hO, map_mul, mul_assoc]⟩

theorem join_inl (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) : ValEq k (joinPt y y') (Sum.elim a 0) y a :=
  of_eq fun O => vdeg_join_inl O y y' a

theorem join_inr (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a' : K' → ℤ) : ValEq k (joinPt y y') (Sum.elim 0 a') y' a' :=
  of_eq fun O => vdeg_join_inr O y y' a'

end ValEq

end SheetDecomposition
