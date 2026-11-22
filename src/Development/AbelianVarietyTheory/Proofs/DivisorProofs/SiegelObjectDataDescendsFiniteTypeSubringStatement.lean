module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDataDescendsFiniteTypeSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelObject_data_descends_finiteType_subring : ∀ (g n : ℕ), 3 ≤ n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), ∃ (R₁ : Subring R) (β₁ : cycAway n →+* R₁) (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), Algebra.FiniteType ℤ R₁ ∧ R₁.subtype.comp β₁ = β ∧ IsAbelianScheme A₁ ∧ SmoothOfRelativeDimension g A₁.hom ∧ P₁.IsLB ∧ IsPullbackTriple c.A c.P (lvOf c) A₁ P₁ lv₁ (spMap R₁.subtype) := by
  first | exact @GlobalTheory.SiegFg.siegPre_data_descends_fg | exact GlobalTheory.SiegFg.siegPre_data_descends_fg | (intros; apply GlobalTheory.SiegFg.siegPre_data_descends_fg <;> assumption)
