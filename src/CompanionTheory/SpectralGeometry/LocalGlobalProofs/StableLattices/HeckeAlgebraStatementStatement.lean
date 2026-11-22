module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeAlgebraStatement
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

@[expose] public section

open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeAlgebraTheorem : StHecke := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBern.stHecke | exact GlobalTheory.CompanionTheory.HeckeBern.stHecke | (intros; apply GlobalTheory.CompanionTheory.HeckeBern.stHecke <;> assumption)
