module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulOfIsPrimitiveIntegralHahnGauss
public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss : ∀ {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (P Q : HahnSeries ℚ Ω), Prim A P → Prim A Q → Prim A (P * Q) := by
  first | exact @GlobalTheory.Glue.Prim.mul | exact GlobalTheory.Glue.Prim.mul | (intros; apply GlobalTheory.Glue.Prim.mul <;> assumption)
