module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictAppLECompat
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_appLE_compat : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)), rs h ((f.appLE U W hW).hom s) = (f.appLE U V (h.trans hW)).hom s := by
  first | exact @GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply | exact GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply | (intros; apply GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply <;> assumption)
