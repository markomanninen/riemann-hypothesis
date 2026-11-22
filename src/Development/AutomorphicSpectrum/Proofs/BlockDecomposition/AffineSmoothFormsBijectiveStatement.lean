module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineSmoothFormsBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.TopRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_smooth_forms_bijective : CrystallineSemistableComparison.Onto.AffOm → CrystallineSemistableComparison.Onto.OmNat → ∀ (K : Type) [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [IsAffine X] [Smooth q] (a : ℕ),
    ∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e := by
  first | exact @GlobalTheory.CompanionTheory.OmGlue.om_top | exact GlobalTheory.CompanionTheory.OmGlue.om_top | (intros; apply GlobalTheory.CompanionTheory.OmGlue.om_top <;> assumption)
