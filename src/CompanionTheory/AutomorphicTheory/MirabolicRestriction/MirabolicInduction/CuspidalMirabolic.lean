module

public import CompanionTheory.AutomorphicTheory.MirabolicRestriction.MirabolicInduction.CuspidalRestrictsToInduced
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleTransportRep

@[expose] public section

namespace CompanionTheory.Mirab

theorem cuspidalMirabolic : GlobalTheory.Published.CuspidalMirabolic :=
  ⟨GlobalTheory.CompanionTheory.Hypotheses₂.cuspidalExists_holds, CompanionTheory.Mirab.Restr.cuspidalRestrictsToInduced⟩

end CompanionTheory.Mirab
