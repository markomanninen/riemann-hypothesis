module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormOne
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
theorem _root_.GlobalTheory.T.hodge_form_one : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0),
    CrystallineSemistableComparison.Om.L2.IsOmT q 0 e → e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤) := by
  first | exact @GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH | exact GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH | (intros; apply GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH <;> assumption)
