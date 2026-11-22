module

public import Mathlib
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdaptedCharacterForm.SecondCapelliMinorStandardBasis

@[expose] public section

theorem contraction_adapted : Formalism.FourierDecayAlt.Q.ContractionsCovariant → Formalism.FourierDecayAlt.Q.ChatAdapted ∧ Formalism.FourierDecayAlt.Q.Chat2Adapted := by
  intro hcov
  exact ⟨Formalism.FourierDecayAlt.Q.Adapted.chatAdapted_of hcov, Formalism.FourierDecayAlt.Q.Adapted.chat2Adapted_of hcov⟩
