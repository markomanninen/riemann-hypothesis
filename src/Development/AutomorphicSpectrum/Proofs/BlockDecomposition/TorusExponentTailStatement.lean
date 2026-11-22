module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusExponentTail
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_exponent_tail : PositivityTheory.Rg.BcB.F.Tail.PExp.TorusExp := by
  first | exact @GlobalTheory.CompanionTheory.TorusExpU.torusExp | exact GlobalTheory.CompanionTheory.TorusExpU.torusExp | (intros; apply GlobalTheory.CompanionTheory.TorusExpU.torusExp <;> assumption)
