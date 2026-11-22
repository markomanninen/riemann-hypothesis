module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecOfIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPointStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianGroupSchemeCubicalBundleClosureStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianLocusEqTrivialTorusLocusProperStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelCoordinatesLocalBasisStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomainStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseFactsHasGeoExistsClos
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistSections
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionExtendingTorsionPointsSupport
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionsIndependentOnClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CharEqZeroOfIsProper
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyOfFourPropertiesGroupSchemeStatement

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ZH.GeoHalf.zhGeo : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → Laws3 → Laws4 → Laws5 → UTorsSt → ZHGeoSt :=
  GlobalTheory.ZH.GeoHalf.zhGeo_of @GlobalTheory.T.thetaSystem_hasTests_of_real_point @GlobalTheory.T.exists_semiAbelian_groupScheme_cubical_bundle_closure @GlobalTheory.T.abelianLocus_eq_trivial_torus_locus_proper @GlobalTheory.T.thetaModel_coordinates_local_basis @GlobalTheory.T.exists_uniformisation_completeLocalNormalDomain @GlobalTheory.ZH.baseFacts_hasGeo_exists_clos @GlobalTheory.ZH.ThetaData.exists_theta @GlobalTheory.ZH.TorsionValue.torsSec @GlobalTheory.ZH.TorsionSection.exists_section @GlobalTheory.T.thetaSections_independent_on_closed_fibre @GlobalTheory.ZH.AbelianLocus.abelian_locus @GlobalTheory.T.nonempty_of_fourProperties_groupScheme
