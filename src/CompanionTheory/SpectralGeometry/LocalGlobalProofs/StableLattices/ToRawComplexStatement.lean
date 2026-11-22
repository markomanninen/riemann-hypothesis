module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToRawComplex
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ToRawComplex : ToRaw := by
  first | exact @GlobalTheory.CompanionTheory.ZuckToRaw.toRaw | exact GlobalTheory.CompanionTheory.ZuckToRaw.toRaw | (intros; apply GlobalTheory.CompanionTheory.ZuckToRaw.toRaw <;> assumption)
