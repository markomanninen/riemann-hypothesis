module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearModelFixesUnitSectionAbelian
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearModel_fixes_unit_section_abelian : ∀ (W K' : Type) [CommRing W] [IsDomain W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (σ : K' →+* K') (τ : W →+* W) (φ : G.left ⟶ G.left) (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) → φ ≫ G.hom = G.hom ≫ spMap τ → pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = ρ ≫ pullback.fst G.hom (spMap (algebraMap W K')) → ∀ (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → ∀ x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K')), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ ρ = spMap σ ≫ x → e₀ ≫ φ = spMap τ ≫ e₀ := by
  first | exact @GlobalTheory.SemilinearModel.unit_section_semilinear | exact GlobalTheory.SemilinearModel.unit_section_semilinear | (intros; apply GlobalTheory.SemilinearModel.unit_section_semilinear <;> assumption)
