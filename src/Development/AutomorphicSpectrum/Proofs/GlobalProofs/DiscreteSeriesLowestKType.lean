module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesLowestKTypeOfClassification
public import Development.AutomorphicSpectrum.Proofs.SemilocalMultiplicity.LowKMultOneP
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DiscreteSeriesUpqUnique

@[expose] public section

namespace GlobalTheory.CompanionTheory.Glob

theorem discreteSeriesLowestKType : GlobalTheory.Published.DiscreteSeriesLowestKType :=
  GlobalTheory.Published.discreteSeriesLowestKType_iff.2
    ⟨GlobalTheory.CompanionTheory.TypeCount.LowK.lowKMultOne, GlobalTheory.CompanionTheory.Front.discreteSeriesUpqUnique⟩

end GlobalTheory.CompanionTheory.Glob
