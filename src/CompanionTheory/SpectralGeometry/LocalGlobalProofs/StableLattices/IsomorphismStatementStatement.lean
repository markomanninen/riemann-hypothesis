module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsomorphismStatement
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite

@[expose] public section

open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.IsomorphismStatement : StIso := by
  first | exact @GlobalTheory.CompanionTheory.FactorIso.stIso | exact GlobalTheory.CompanionTheory.FactorIso.stIso | (intros; apply GlobalTheory.CompanionTheory.FactorIso.stIso <;> assumption)
