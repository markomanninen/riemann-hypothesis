module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfFrameWittTorus
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

@[expose] public section

open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_of_frame_witt_torus : StFrame → StWitt → StTor → StDecomp := by
  first | exact @GlobalTheory.CompanionTheory.FlDecomp.stDecomp_of_frame_witt_tor | exact GlobalTheory.CompanionTheory.FlDecomp.stDecomp_of_frame_witt_tor | (intros; apply GlobalTheory.CompanionTheory.FlDecomp.stDecomp_of_frame_witt_tor <;> assumption)
