module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenFiniteEtaleHermitianPairOK
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_finiteEtaleHermitianPair_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsOpen A.OK := by
  first | exact @GlobalTheory.JR.OKOpen.isOpen_OK | exact GlobalTheory.JR.OKOpen.isOpen_OK | (intros; apply GlobalTheory.JR.OKOpen.isOpen_OK <;> assumption)
