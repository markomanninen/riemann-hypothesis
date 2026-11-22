module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormLength
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PVertTermEq
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IsChowFormCMul
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGaussEq
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParAlgIndep
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBLinInj
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormEval
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowSecDegree
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormIdentity
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.POrdEq
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartTorsion
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowFormHomog
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowNormFormGeneric
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowNormForm
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PIncidenceNull
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PLengthDecomp
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormLocalization
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParDVRIsDVR
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParFracIsFractionRing
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PPrimitiveScale
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecAlgField
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBFinite
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBGeneric
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecLinNZD
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecMax
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecResidue
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

theorem NormLength.full : NormLength.Statement := NormLength.proof
theorem VertTermEq.full : VertTermEq.Statement := VertTermEq.proof
theorem ParAlgIndep.full : ParAlgIndep.Statement := ParAlgIndep.proof
theorem NormFormEval.full : NormFormEval.Statement := NormFormEval.proof
theorem ChartTorsion.full : ChartTorsion.Statement := ChartTorsion.proof
theorem ChowFormHomog.full : ChowFormHomog.Statement := ChowFormHomog.proof
theorem IncidenceNull.full : IncidenceNull.Statement := IncidenceNull.proof
theorem LengthDecomp.full : LengthDecomp.Statement := LengthDecomp.proof
theorem NormFormLocalization.full : NormFormLocalization.Statement := NormFormLocalization.proof
theorem ParDVRIsDVR.full : ParDVRIsDVR.Statement := ParDVRIsDVR.proof
theorem ParFracIsFractionRing.full : ParFracIsFractionRing.Statement := ParFracIsFractionRing.proof
theorem PrimitiveScale.full : PrimitiveScale.Statement := PrimitiveScale.proof
theorem SecBGeneric.full : SecBGeneric.Statement := SecBGeneric.proof
theorem SecBFinite.full : SecBFinite.Statement :=
  SecBFinite.proof IncidenceNull.full ChartTorsion.full PrimitiveScale.full

end GroundTheory.Heights₂.Heights.Vertical
