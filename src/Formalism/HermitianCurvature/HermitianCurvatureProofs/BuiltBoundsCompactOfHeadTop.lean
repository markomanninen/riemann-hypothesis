module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfLeaves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UniformDecayOfPlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UniformDecayOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopLocalBuiltPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatioAlt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DegreeTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegLift

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem built_bounds_compact_of_head_top (hH : Formalism.FourierDecayAlt.KB.HeadTop) : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt := fun hA =>
  built_bounds_compact_of_leaves radial_head hH degree_of_lift_pairing top_local_built_places degree_top
    top_ratio (germ_parts_compact_support kernel_continuity_built germ_rate_bound hA)
    (fun hA' => uniform_decay_of_place hA' radial_head hH
      (uniform_decay_of_heads radial_head hH)) hA

end Formalism.FourierDecayAlt.P
