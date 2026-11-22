module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.QuotientIsHausdorff
public import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.DetValuationLeOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsMonicIrreducibleCardGt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Formalism.LocalToGlobal.Divisibility.Frames
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Formalism.MeanHeightDescent.CombinedAverageDegreeBound
public import Formalism.MonomialMeanResidues.FilteredDegree
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonemptyCptOverOfFlatPreimmersion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonMiddle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangular
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameLawsOfModuli
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExpBCChart

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.CombMap

theorem isCombAt_spMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsCombAt x v cf w → IsCombAt (spMap φ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (Formalism.L2.Pj.dualMap φ) ≫ w) := by
  intro E _ _ _ H Dw l Xo S T _ _ φ x m v cf w hc
  obtain ⟨u, hu, hw⟩ := hc
  have hcomp : (Formalism.L2.Pj.dualMap φ).comp (algebraMap S (DualNumber S)) =
      (algebraMap T (DualNumber T)).comp φ := by
    ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let f : tEps (spMap φ ≫ x) ⟶ tEps x := Over.homMk (spMap (Formalism.L2.Pj.dualMap φ)) (by
    show spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap T (DualNumber T)) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hcomp,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc])
  let P : (tEps x ⟶ Xo.univ.t.G) →* (tEps (spMap φ ≫ x) ⟶ Xo.univ.t.G) :=
    { toFun := fun g => f ≫ g
      map_one' := CategoryTheory.MonObj.comp_one f
      map_mul' := CategoryTheory.MonObj.comp_mul f }
  refine ⟨fun i => f ≫ u i, fun i => ?_, ?_⟩
  · rw [Over.comp_left, hu i]
    show spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (cf i)) ≫ v i =
      spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (φ (cf i))) ≫ spMap (Formalism.L2.Pj.dualMap φ) ≫ v i
    rw [← Category.assoc, ← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp,
      ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
    congr 2
    ext y <;> simp [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, smul_eq_mul, map_mul,
      TrivSqZeroExt.algebraMap_eq_inl]
  · have h1 : (List.ofFn fun i => f ≫ u i) = (List.ofFn u).map P := by
      rw [List.map_ofFn]
      rfl
    rw [h1, ← map_list_prod]
    show (f ≫ (List.ofFn u).prod).left = _
    rw [Over.comp_left, hw]
    rfl

end GlobalTheory.CompanionTheory.Ar.CombMap
