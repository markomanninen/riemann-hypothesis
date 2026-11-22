module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeDimAtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureNeTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactRatioOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLowestKTypeWeylDimensionLeOfSizeBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFramesStrongApproximationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetIsTA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaTermTsumLeTwo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupMeasureDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentificationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRepresentativesInjectiveDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamily
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMeasureRatioLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LevelSubgroupIndexBounded
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HaarMeasureFundamentalDomainNeZeroOfCocompact
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeFundamentalDomainNeTopOfFiniteCovolume
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CovolumeRatioEqIndex
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.PlugPairs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogMeasureRatioBounded
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.SupremumConstantLogBound

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
namespace GlobalTheory.OneMeasureAll
theorem covolume_measure_eq_one : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D := by
  intro hP D Tu C t0 hC i P
  refine ⟨_root_.GlobalTheory.T.level_subgroup_index_bounded hP D Tu C t0 hC i P, fun τ => GlobalTheory.T.one_le_dimAt' D i τ, fun μ 𝓕 hF =>
    ⟨_root_.GlobalTheory.T.fundamentalDomain_volume_ne_zero hP D Tu C t0 hC i P μ 𝓕 hF, _root_.GlobalTheory.T.quotient_measure_lt_top_of_finite_covolume hP D Tu C t0 hC i P μ 𝓕 hF,
      _root_.GlobalTheory.T.covolume_ratio_eq_index hP D Tu C t0 hC i P μ 𝓕 hF, fun L hL =>
        ⟨fun τ => GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds D i L hL τ, _root_.MainStatements.Tam.Plug.tamagawa_pairs_compatible hP D Tu C t0 hC i P μ 𝓕 hF L hL,
          _root_.GlobalTheory.T.log_measure_ratio_bounded hP D Tu C t0 hC i P μ 𝓕 hF L hL⟩⟩⟩
end GlobalTheory.OneMeasureAll
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_covolume_eq_one : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D := by
  first | exact @_root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one | exact _root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one | (intros; apply _root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one <;> assumption)
end
