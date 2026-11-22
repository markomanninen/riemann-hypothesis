module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelTrivLine
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsCoordNeZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BirationalYPt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUpperNormalisation
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecMRankBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibreVar
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRankBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsSeparated
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallPacking
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelLatticeFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepLocal
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepHomog
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSerreGraded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSpanStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionRingFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSectionsPower
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeExtension
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanningExtension
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCovolumeLeGram
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGramContraction
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSections
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.UnipotentCharacter

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SublatticeDegree.full : SublatticeDegree.Statement :=
  SublatticeDegree.proof SublatticeExtension.proof SpanningExtension.proof CovolumeLeGram.proof
    GramContraction.proof

theorem SuccessiveMinimaSpan.of_leaves (hC : KH.CondStatement) (hR : RelSectionsLarge.Statement) : SuccessiveMinimaSpan.Statement :=
  SuccessiveMinimaSpan.proof
    (SectionRingFinite.proof (SectionLatticeFinite.proof hC)
      (SectionSpanStep.proof (SpanStepHomog.proof (SpanStepLocal.proof (RelLatticeFinite.proof hR)))
        SerreGraded.proof))
    SectionBounded.proof SectionBoundedMul.proof

end GroundTheory.Heights₂.Heights.Targets
