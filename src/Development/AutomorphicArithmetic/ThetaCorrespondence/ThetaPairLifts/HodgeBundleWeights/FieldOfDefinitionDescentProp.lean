module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypotheses
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasLevW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryLieBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMultipleInLieLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCmTypeProductSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTraceFormDetIndexStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeDualIndex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorProductBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianVolumeLieBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorLowerBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeHermitianRankAndHostDegreeEqStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeFromConjugateComplement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOfLevelClass
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryRepresentativesThetaCompatible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentificationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelicStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPackingSetMeasureGeCovolumeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountableRationalSubgroupInRealSpecialUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetDetImPosAtIndexStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureFinitePartPreimage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMassProductLowerBoundUnitaryPqStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

@[expose] public section

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.FieldOfDefinitionDescentProp : Prop :=  _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P) μ 𝓕 → ENNReal.ofReal (Real.exp (-(C * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)|)))) ≤ μ 𝓕
end
