module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfFiniteFibres
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_finite_fibres : PositivityTheory.Tls2.Zar3.Ch1.FiniteOfFibres := by
  first | exact @GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | exact GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | (intros; apply GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres <;> assumption)
