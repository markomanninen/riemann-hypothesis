module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WittStatement
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

@[expose] public section

open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.WittStatement : StWitt := by
  first | exact @GlobalTheory.CompanionTheory.FlWitt.stWitt | exact GlobalTheory.CompanionTheory.FlWitt.stWitt | (intros; apply GlobalTheory.CompanionTheory.FlWitt.stWitt <;> assumption)
