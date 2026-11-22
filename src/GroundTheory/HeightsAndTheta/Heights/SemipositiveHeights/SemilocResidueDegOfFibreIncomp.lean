module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFStep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFSecRed
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFVert
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFHoriz
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreBij
public import GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.LeviOfRealSmulRight
public import GroundTheory.HeightsAndTheta.Heights.Intersections.MixedDiscEqZeroOfMulVec
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZIff
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZ
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsAlt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsRest
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
public import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsIntegralLogNormRat
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PullWMemFibre
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsSheetPullW
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjDeg
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFnDegRelDeg
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.NumericalSegre
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRC3ResidualContractionComponent
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixedField
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArithClosed
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Multilin
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.FibreDim
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocMaxIdeals
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueDeg
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueFibreDim
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueAdjoin
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocResidueFrac
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreDivSupp
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreOverFinite

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter

theorem projDeg_all :
    ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι' := by
  intro F _ K _ ι _ K' _ ι' _
  exact GroundTheory.Heights₂.Heights.Targets.ProjDeg.of_found
    (GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.of_divPushForward
      (GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.proof
        GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe.proof
        GroundTheory.Heights₂.Heights.NumbersDVR.DivPushForwardLocalZero))
    GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg.proof F ι ι'

theorem semilocMaxIdeals_of_fibreIncomp (hFI : FibreIncomp.Statement) : SemilocMaxIdeals.Statement :=
  SemilocMaxIdeals.proof (FibreOverFinite.proof hFI) hFI SemilocIntegral.full LocRingDimOne.full

theorem semilocResidueDeg_of_fibreIncomp (hFI : FibreIncomp.Statement) (hFD : FibreDimStatement) :
    SemilocResidueDeg.Statement :=
  SemilocResidueDeg.proof (SemilocResidueFibreDim.proof (FibreDivSupp.proof hFI) hFD FibreDimensionZero.full)
    (SemilocResidueAdjoin.proof
      (SemilocResidueFrac.proof SemilocFinite.full (semilocMaxIdeals_of_fibreIncomp hFI))
      ChartScalingIndep.full)

end GroundTheory.Heights₂.Heights.ForSecondHalf
