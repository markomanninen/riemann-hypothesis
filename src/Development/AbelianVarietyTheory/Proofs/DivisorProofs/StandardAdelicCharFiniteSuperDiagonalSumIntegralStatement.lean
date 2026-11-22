module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharFiniteSuperDiagonalSumIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAdelicCharFinite_superDiagonalSum_integral_eq_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (u : GL (Fin n) (Af E)), u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) → u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1 := by
  first | exact @GlobalTheory.WhitBump.psiFin_superDiag_eq_one_of_integral | exact GlobalTheory.WhitBump.psiFin_superDiag_eq_one_of_integral | (intros; apply GlobalTheory.WhitBump.psiFin_superDiag_eq_one_of_integral <;> assumption)
