module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

namespace GlobalTheory.LocM.TorCheck

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

theorem minVal_eval (B : X → X → ℝ) : (InvFun.minVal O).eval X B = sInf {x | (∃ y, B y y = x) ∧ x ≠ B 0 0} := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr]
  change sInf _ = _
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, map_zero]
  exact and_congr_left' ⟨fun ⟨y, h⟩ => ⟨r y, h⟩, fun ⟨y, h⟩ => (hr y).elim fun z e => ⟨z, e ▸ h⟩⟩

theorem minVal_linearOn (γ : LinearMap.BilinForm ℤ X) : (InvFun.minVal O).LinearOn ![γ] := by
  intro c hc
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, InvFun.evalZ, minVal_eval, map_zero, Int.cast_zero, mul_zero,
    LinearMap.zero_apply]
  rcases (hc 0).eq_or_lt with h | h
  · rw [← h]
    simp only [zero_mul]
    convert Real.sInf_empty
    simp [eq_comm]
  · rw [← smul_eq_mul (c 0) (sInf _), ← Real.sInf_smul_of_nonneg (hc 0)]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨⟨y, rfl⟩, hx⟩
      exact ⟨_, ⟨⟨y, rfl⟩, fun e => hx (by rw [e, mul_zero])⟩, rfl⟩
    · rintro ⟨_, ⟨⟨y, rfl⟩, hx⟩, rfl⟩
      exact ⟨⟨y, rfl⟩, mul_ne_zero h.ne' hx⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

end GlobalTheory.LocM.TorCheck
