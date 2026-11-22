module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StatementCommutative
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

@[expose] public section

open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.StatementCommutative : StComm := by
  first | exact @GlobalTheory.CompanionTheory.Bernstein.stComm | exact GlobalTheory.CompanionTheory.Bernstein.stComm | (intros; apply GlobalTheory.CompanionTheory.Bernstein.stComm <;> assumption)
