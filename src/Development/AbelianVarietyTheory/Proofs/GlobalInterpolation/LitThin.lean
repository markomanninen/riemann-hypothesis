module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsFurther
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaAndWindowCount

@[expose] public section

namespace GlobalTheory.ThinScaleLiterature

theorem litThin : Formalism.MainNotions.LitThin :=
  ⟨GlobalTheory.ZerosNearOne.main, GlobalTheory.ZeroBounds.explicit_formula_and_window_count⟩

end GlobalTheory.ThinScaleLiterature
