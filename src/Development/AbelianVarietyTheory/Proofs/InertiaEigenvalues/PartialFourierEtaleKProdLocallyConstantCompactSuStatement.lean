module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierEtaleKProdLocallyConstantCompactSu
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnifConst
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFourier_etaleKProd_locallyConstantCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (fun p : A.K × A.K => A.tilde μK ψ φ' p.1 p.2) := by
  first | exact @GlobalTheory.JR.TildeTest.main | exact GlobalTheory.JR.TildeTest.main | (intros; apply GlobalTheory.JR.TildeTest.main <;> assumption)
