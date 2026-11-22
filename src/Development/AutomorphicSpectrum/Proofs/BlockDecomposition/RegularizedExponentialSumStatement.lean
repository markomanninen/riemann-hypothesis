module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularizedExponentialSum
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds

@[expose] public section

open scoped Classical
namespace PositivityTheory.Rg.BcB.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_exponential_sum : PositivityTheory.Rg.BcB.F.ExpSum := by
  first | exact @GlobalTheory.CompanionTheory.ExpSums.expSum_holds | exact GlobalTheory.CompanionTheory.ExpSums.expSum_holds | (intros; apply GlobalTheory.CompanionTheory.ExpSums.expSum_holds <;> assumption)
