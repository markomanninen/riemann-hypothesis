module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StTensor
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite

@[expose] public section

open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stTensor' : StTensor := by
  first | exact @GlobalTheory.CompanionTheory.RestT.stTensor | exact GlobalTheory.CompanionTheory.RestT.stTensor | (intros; apply GlobalTheory.CompanionTheory.RestT.stTensor <;> assumption)
