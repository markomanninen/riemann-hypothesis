module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormPullbackCompat
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
theorem _root_.GlobalTheory.T.hodge_form_pullback_compat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (e : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (e' : CrystallineSemistableComparison.HT.Hdg p a a ≃ₗ[K] OmU p ⊤ a),
    CrystallineSemistableComparison.Om.L2.IsOmT q a e → CrystallineSemistableComparison.Om.L2.IsOmT p a e' → ∀ x : CrystallineSemistableComparison.HT.Hdg p a a,
      e (CrystallineSemistableComparison.HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e' x)) := by
  first | exact @GlobalTheory.CompanionTheory.OmNatT.pull_nat | exact GlobalTheory.CompanionTheory.OmNatT.pull_nat | (intros; apply GlobalTheory.CompanionTheory.OmNatT.pull_nat <;> assumption)
