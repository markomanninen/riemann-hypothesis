module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfHeadTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbHeadTopOfMkTop

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem pb_builtBounds2Cpt_of_mkTop (hM : CutEX.MkTop) : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt :=
  built_bounds_compact_of_head_top (pb_headTop_of_mkTop hM)

end Formalism.FourierDecayAlt.P
