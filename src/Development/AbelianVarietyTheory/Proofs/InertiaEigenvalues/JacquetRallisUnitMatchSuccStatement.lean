module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSucc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_succ : WeilEt → GammaOne → ∀ r : ℕ, FourierMatch (r + 1) → UnitMatch r → UnitMatch (r + 1) := by
  first | exact @GlobalTheory.JR.UnitStep.unitMatch_succ | exact GlobalTheory.JR.UnitStep.unitMatch_succ | (intros; apply GlobalTheory.JR.UnitStep.unitMatch_succ <;> assumption)
