module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
public import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
public import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CombinedBoundForRunScalarsStatement
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsScalarWeightAuxiliaryFormOfRunConditionsStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdmissibleThetaLatticeGeneratorsStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunHypothesesFormsScalarsOfParameterConditionsStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralFormsLogSupNormLowerBoundAbsoluteStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNetDimensionAndPointCountBoundStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PageBoundPolynomialDomination
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPrimeDataCurveLiftingHeightBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RecursivePageLatticeBoundStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspFormBasisSharesIndefiniteLiftIndexStatement
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.RunJoin

theorem genOK_refill {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (c : ℝ) (hG : GenOK h j hj large₂ G S c)
    (del th' rz alz th0 zc rq th iet et) :
    GenOK h j hj large₂ (FamilyHypotheses.refill G del th' rz alz th0 zc rq th iet et) S c := hG

end GlobalTheory.RunJoin
