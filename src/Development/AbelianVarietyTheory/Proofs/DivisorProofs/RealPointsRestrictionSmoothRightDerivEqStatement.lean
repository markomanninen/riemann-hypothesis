module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsRestrictionSmoothRightDerivEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
public import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

@[expose] public section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ φ : Sm E a, ∀ x, (glH E a).IsSmoothFun (glRes φ.1 x) ∧ ∀ X : glL E a, (glH E a).rightDeriv X (glRes φ.1 x) = glRes (lie E a (toL X.1) φ).1 x := by
  first | exact @GlobalTheory.HCA.glRes_smooth_rightDeriv | exact GlobalTheory.HCA.glRes_smooth_rightDeriv | (intros; apply GlobalTheory.HCA.glRes_smooth_rightDeriv <;> assumption)
