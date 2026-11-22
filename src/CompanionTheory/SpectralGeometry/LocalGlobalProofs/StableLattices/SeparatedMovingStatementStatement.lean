module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SeparatedMovingStatement
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite

@[expose] public section

open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.SeparatedMovingStatement : StSepMove := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stSepMove | exact GlobalTheory.CompanionTheory.RgFl.stSepMove | (intros; apply GlobalTheory.CompanionTheory.RgFl.stSepMove <;> assumption)
