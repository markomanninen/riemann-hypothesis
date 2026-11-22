module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearTopologicalGroup
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.general_linear_topological_group : PositivityTheory.RgEis.GrpTop := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTop.grpTop | exact GlobalTheory.CompanionTheory.RgEisTop.grpTop | (intros; apply GlobalTheory.CompanionTheory.RgEisTop.grpTop <;> assumption)
