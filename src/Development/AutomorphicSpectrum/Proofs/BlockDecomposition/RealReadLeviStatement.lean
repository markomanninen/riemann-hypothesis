module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealReadLevi
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFixedNonzeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnCompactParabolicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicElementBlockFormStatement

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_read_levi : PositivityTheory.Rg.BcB.F.Tail.RReadLev := by
  first | exact @GlobalTheory.CompanionTheory.ReadLevel.rReadLev | exact GlobalTheory.CompanionTheory.ReadLevel.rReadLev | (intros; apply GlobalTheory.CompanionTheory.ReadLevel.rReadLev <;> assumption)
