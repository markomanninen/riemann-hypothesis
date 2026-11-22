module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryLatticeCountRatioTendsto
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent

@[expose] public section

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lattice_count_ratio_tendsto : UnitaryLimit := by
  first | exact @GlobalTheory.UnitLemma.unitaryLimit | exact GlobalTheory.UnitLemma.unitaryLimit | (intros; apply GlobalTheory.UnitLemma.unitaryLimit <;> assumption)
