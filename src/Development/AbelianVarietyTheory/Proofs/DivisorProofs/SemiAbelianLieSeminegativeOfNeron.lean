module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EssFiniteTypeOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiNegativeDescendsFieldExtensionCurveStatement
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsLocalizedModuleGermLinearPointOfPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusExtendsSemiabelian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSpecialOfLocal
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoveringAndSmoothnessIffOfSeparableSplitting
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothTorusQuotientOfGoodOpenCover
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackKernelBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableOfSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NeronCurve.LieDescent

theorem semiNeg_of_iso {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] {F F' : C.Modules} (e : F ≅ F')
    (h : SemiNeg k F) : SemiNeg k F' := fun W r hW i _ =>
  h W r hW (i ≫ e.inv) (mono_comp i e.inv)

def lieBaseIso {C C' : Scheme.{0}} [IsIntegral C] (π : C' ⟶ C) (G : Over C) [GrpObj G] [IsSemiAbelian G] :
    (Scheme.Modules.pullback π).obj (Lie G) ≅ Lie ((Over.pullback π).obj G) :=
  have h := isGrpPullback_pullback G π
  have hg := (exists_isVB_of_isSemiAbelian G).choose_spec.1
  have := isIso_lieBase h hg
  asIso (lieBase h)

end GlobalTheory.NeronCurve.LieDescent

namespace GlobalTheory.NeronCurve

end GlobalTheory.NeronCurve
