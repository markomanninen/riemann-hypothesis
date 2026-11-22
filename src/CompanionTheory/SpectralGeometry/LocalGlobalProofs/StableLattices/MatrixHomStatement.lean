module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixHom
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.MatrixHom : MatHom := by
  first | exact @GlobalTheory.CompanionTheory.ZuckMatHom.matHom | exact GlobalTheory.CompanionTheory.ZuckMatHom.matHom | (intros; apply GlobalTheory.CompanionTheory.ZuckMatHom.matHom <;> assumption)
