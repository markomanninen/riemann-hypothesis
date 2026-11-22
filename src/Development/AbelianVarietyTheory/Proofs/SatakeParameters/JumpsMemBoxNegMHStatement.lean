module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsMemBoxNegMH
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumps_mem_box_neg_M_h : ∀ {n : ℕ} (W : WordData n), (∀ i, 0 ≤ W.sz i) → W.T1 → ∀ i, ∀ u ∈ W.J1 i, -(W.Mi i : ℤ) ≤ u ∧ u ≤ W.hi i := by
  first | exact @GlobalTheory.HTW.WordData.jumps_mem_box | exact GlobalTheory.HTW.WordData.jumps_mem_box | (intros; apply GlobalTheory.HTW.WordData.jumps_mem_box <;> assumption)
