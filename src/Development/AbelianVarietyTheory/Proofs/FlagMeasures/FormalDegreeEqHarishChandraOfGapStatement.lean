module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeEqHarishChandraOfGap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_eq_harishChandra_of_gap : ∀ (D : D7), Ties D → ∀ (τ : D.what₂.Tau) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc τ)) → Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ)) h → Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < h → D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) :=
  GlobalTheory.dsig_eq_fdegHC_of_gap
