module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharp_surjective_ker_span : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), Function.Surjective A.aToU1 ∧ RingHom.ker A.aToU1 = Ideal.span {A.pi} := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker | exact GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker | (intros; apply GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker <;> assumption)
