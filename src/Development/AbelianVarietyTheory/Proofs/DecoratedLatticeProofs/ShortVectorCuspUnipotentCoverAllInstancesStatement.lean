module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShortVectorCuspUnipotentCoverAllInstances
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortVectorCuspUnipotentCover_all_instances : ∀ I : AutInst, ShortCusp I := by
  first | exact @GlobalTheory.CuspGeo.shortCusp_all | exact GlobalTheory.CuspGeo.shortCusp_all | (intros; apply GlobalTheory.CuspGeo.shortCusp_all <;> assumption)
