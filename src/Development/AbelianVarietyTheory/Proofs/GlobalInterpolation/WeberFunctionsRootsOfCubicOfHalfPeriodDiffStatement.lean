module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeberFunctionsRootsOfCubicOfHalfPeriodDiff
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta

@[expose] public section

open Complex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weberFunctionsRootsOfCubic_of_halfPeriodDiff : ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.HalfPeriodDiff τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.JacobiProduct τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.WeberCubic τ := by
  first | exact @GlobalTheory.WeberCubicAlgebra.weberCubic_of_halfPeriodDiff | exact GlobalTheory.WeberCubicAlgebra.weberCubic_of_halfPeriodDiff | (intros; apply GlobalTheory.WeberCubicAlgebra.weberCubic_of_halfPeriodDiff <;> assumption)
