module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.GoodPlacesOutsideFiniteSet
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact

@[expose] public section

open GlobalTheory.CompanionTheory.Jp
theorem _root_.GlobalTheory.T.jacquet_piatetski_bound_holds : GlobalTheory.CompanionTheory.Jp.GoodPlacesOutsideFiniteSet := by
  first | exact @PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound | exact PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound | (intros; apply PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound <;> assumption)
