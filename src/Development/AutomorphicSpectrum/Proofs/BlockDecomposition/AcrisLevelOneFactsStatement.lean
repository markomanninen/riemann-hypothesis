module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelOneFacts
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_level_one_facts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcr1 l := by
  first | exact @GlobalTheory.CompanionTheory.ACrisMod.acr1 | exact GlobalTheory.CompanionTheory.ACrisMod.acr1 | (intros; apply GlobalTheory.CompanionTheory.ACrisMod.acr1 <;> assumption)
