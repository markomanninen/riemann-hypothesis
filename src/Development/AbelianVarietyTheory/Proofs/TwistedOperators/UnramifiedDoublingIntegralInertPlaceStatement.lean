module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedDoublingIntegral_inert_place : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert := by
  first | exact @GlobalTheory.InertZeta.unramDoublingInert | exact GlobalTheory.InertZeta.unramDoublingInert | (intros; apply GlobalTheory.InertZeta.unramDoublingInert <;> assumption)
