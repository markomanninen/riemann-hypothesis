module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BetaWeightOfTorusFacts
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_weight_of_torus_facts : PositivityTheory.RgDs.K.HolFacts → PositivityTheory.RgDs.K.RhoTorus → PositivityTheory.RgDs.K.TorW → PositivityTheory.RgDs.K.BetaWeight := by
  first | exact @GlobalTheory.CompanionTheory.TorusSymbol.betaWeight | exact GlobalTheory.CompanionTheory.TorusSymbol.betaWeight | (intros; apply GlobalTheory.CompanionTheory.TorusSymbol.betaWeight <;> assumption)
