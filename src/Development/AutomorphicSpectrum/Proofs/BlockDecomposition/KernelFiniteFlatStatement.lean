module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFiniteFlat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.KernelFinFlat := by
  first | exact @GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat | exact GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat | (intros; apply GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat <;> assumption)
