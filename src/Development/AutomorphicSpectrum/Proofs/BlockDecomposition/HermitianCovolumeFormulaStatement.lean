module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCovolumeFormula
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_covolume_formula : PositivityTheory.SiegelWeilFormula.KWhit.MeasP.HermCovol := by
  first | exact @GlobalTheory.CompanionTheory.SW.HermCov.hermCovol | exact GlobalTheory.CompanionTheory.SW.HermCov.hermCovol | (intros; apply GlobalTheory.CompanionTheory.SW.HermCov.hermCovol <;> assumption)
