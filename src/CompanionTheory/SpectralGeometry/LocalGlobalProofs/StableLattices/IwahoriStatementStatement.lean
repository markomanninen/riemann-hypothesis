module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriStatement
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

@[expose] public section

open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.IwahoriStatement : StIwahori := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.stIwahori | exact GlobalTheory.CompanionTheory.Iwahori.stIwahori | (intros; apply GlobalTheory.CompanionTheory.Iwahori.stIwahori <;> assumption)
