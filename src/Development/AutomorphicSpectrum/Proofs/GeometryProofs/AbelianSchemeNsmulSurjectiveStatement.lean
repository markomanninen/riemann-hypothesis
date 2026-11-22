module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeNsmulSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_nsmul_surjective : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, n ≠ 0 → Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.surjective_pow_of_isAbelianScheme | exact GlobalTheory.CompanionTheory.Ar.Approx.surjective_pow_of_isAbelianScheme | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.surjective_pow_of_isAbelianScheme <;> assumption)
