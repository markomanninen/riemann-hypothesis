module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingFacts
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_ring_facts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := by
  first | exact @GlobalTheory.CompanionTheory.TiltFacts.obFacts | exact GlobalTheory.CompanionTheory.TiltFacts.obFacts | (intros; apply GlobalTheory.CompanionTheory.TiltFacts.obFacts <;> assumption)
