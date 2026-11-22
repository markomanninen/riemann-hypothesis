module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandCLMInfApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanModerateGrowthMatrixSmoothingIntegr

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem smoothMatInf_keeps_modGrowth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α →
    tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W →
    IsModGrowthInf (smoothMatInf α W) :=
  isModGrowthInf_smoothMatInf

end GlobalTheory.JSW.MirCinf
