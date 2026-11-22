module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HSClosing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.DoubleBlock
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CNormSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeIntB
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageChi
public import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.ChiPSt
public import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.SupStMonoNormSqPos
public import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.GaussSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStE
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFSMass
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjectionBounds
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFSExtension
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealGramComparison
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResChiBounds
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResChiIndex
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseMonoBasis

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem BlockImageChi.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageChi.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageChi.proof

theorem ResChiBounds.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiBounds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiBounds.proof ResolutionSupBound.full

theorem ProjectionBounds.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds.proof ResChiBounds.full

theorem PullFSExtension.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PullFSExtension.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PullFSExtension.proof ProjFrameBasePtFree.full

theorem RealGramComparison.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RealGramComparison.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RealGramComparison.proof ResolutionSupBound.full ProjectionBounds.full PullFSExtension.full

theorem ResChiIndex.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiIndex.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiIndex.proof

theorem VeroneseMonoBasis.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseMonoBasis.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseMonoBasis.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
