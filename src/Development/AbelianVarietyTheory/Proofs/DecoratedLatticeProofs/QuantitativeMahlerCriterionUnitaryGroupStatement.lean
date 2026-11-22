module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuantitativeMahlerCriterionUnitaryGroup
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantitativeMahlerCriterion_unitaryGroup : ∀ I : AutInst, HtMin I := by
  first | exact @GlobalTheory.htMin_of_reduced | exact GlobalTheory.htMin_of_reduced | (intros; apply GlobalTheory.htMin_of_reduced <;> assumption)
