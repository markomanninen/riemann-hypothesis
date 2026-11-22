module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingFactsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelOneFactsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelSequenceFactsStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem CrystallineSemistableComparison.RL.d_ob : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := GlobalTheory.T.integral_ring_facts

theorem CrystallineSemistableComparison.RL.acris_mod_l_base_change : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcr1 l := GlobalTheory.T.acris_level_one_facts

theorem CrystallineSemistableComparison.RL.d_seq : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcrSeq l := GlobalTheory.T.acris_level_sequence_facts
