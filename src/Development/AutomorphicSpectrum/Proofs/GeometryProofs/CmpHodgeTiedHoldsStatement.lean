module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpHodgeTiedHolds
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CmpHodgeTied_holds : GlobalTheory.CompanionTheory.Ar.HodgeComparisonCompatibility := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CmpTied.cmpHodgeTied | exact GlobalTheory.CompanionTheory.Ar.CmpTied.cmpHodgeTied | (intros; apply GlobalTheory.CompanionTheory.Ar.CmpTied.cmpHodgeTied <;> assumption)
