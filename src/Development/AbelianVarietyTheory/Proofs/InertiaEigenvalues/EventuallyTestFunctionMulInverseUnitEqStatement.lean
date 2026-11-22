module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyTestFunctionMulInverseUnitEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNormStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteNormedAlgebraEqModuleTopology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_testFunction_mul_inverse_unit_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ s in 𝓝 a, ∀ t : A.K, IsUnit t → φ' (s * Ring.inverse t, t) = φ' (a * Ring.inverse t, t) := by
  first | exact @GlobalTheory.eventually_testFn_mul_inverse_eq | exact GlobalTheory.eventually_testFn_mul_inverse_eq | (intros; apply GlobalTheory.eventually_testFn_mul_inverse_eq <;> assumption)
