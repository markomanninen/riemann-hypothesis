module

public import Mathlib
public import Formalism.PeriodIntegrals.FoldMult
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MultiplicityMeasurability.MeasurableMult

@[expose] public section

open PI.FoldMult.UnitaryGroupMassFormula

theorem overlapMultiplicityProperties : PI.FoldMult.FoldMult := by
  intro G _ _ _ _ _ _ _ Γ hΓ Ω hΩ h1
  exact ⟨fun x => one_le_mult Γ Ω h1 x, fun x => mult_lt_top Γ Ω hΩ x,
    fun γ hγ x => mult_mul_left Γ Ω γ hγ x, measurable_mult Γ Ω hΩ⟩
