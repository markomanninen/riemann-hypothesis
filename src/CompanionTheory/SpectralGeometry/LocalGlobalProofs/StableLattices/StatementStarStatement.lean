module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StatementStar
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

@[expose] public section

open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.StatementStar : StStar := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.StarPf.stStar | exact GlobalTheory.CompanionTheory.RgFl.StarPf.stStar | (intros; apply GlobalTheory.CompanionTheory.RgFl.StarPf.stStar <;> assumption)
