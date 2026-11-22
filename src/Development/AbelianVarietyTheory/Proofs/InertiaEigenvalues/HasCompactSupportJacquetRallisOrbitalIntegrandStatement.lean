module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportJacquetRallisOrbitalIntegrand
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariantsStatement

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCompactSupport_jacquetRallisOrbitalIntegrand : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (n : ℕ) (Y : Gl n F), Delta (inv Y) ≠ 0 → HasCompactSupport (fun g : GL (Fin n) F => unitG n F (act g Y) * omega (act g Y)) := by
  first | exact @GlobalTheory.JR.orbG_integrand_hasCompactSupport | exact GlobalTheory.JR.orbG_integrand_hasCompactSupport | (intros; apply GlobalTheory.JR.orbG_integrand_hasCompactSupport <;> assumption)
