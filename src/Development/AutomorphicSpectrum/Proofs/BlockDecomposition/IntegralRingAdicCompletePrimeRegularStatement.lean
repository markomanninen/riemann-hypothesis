module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingAdicCompletePrimeRegular
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_ring_adic_complete_prime_regular : ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {pFlat l}) (Ob l) ∧ pFlat l ∈ nonZeroDivisors (Ob l) := by
  first | exact @GlobalTheory.CompanionTheory.TiltCompl.complete_tf | exact GlobalTheory.CompanionTheory.TiltCompl.complete_tf | (intros; apply GlobalTheory.CompanionTheory.TiltCompl.complete_tf <;> assumption)
