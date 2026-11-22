module

public import Mathlib
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationCharZeroOfBoundary
public import Development.WeilBound.CoreStatements.ResolutionCharZero.RqGbnd

@[expose] public section

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

theorem principalisationCharZero_closed : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero :=
  principalisationCharZero_of_boundary PositivityTheory.ResPlug.GBnd.gBoundary

end PositivityTheory.ResPlug.WeightsCompactStabilizer
