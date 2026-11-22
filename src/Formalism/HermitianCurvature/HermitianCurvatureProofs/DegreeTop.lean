module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbDegTopOfPolyTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingLoweringRelations

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem degree_top : Formalism.FourierDecayAlt.KB.DegTop := pb_degTop_of_polyTop polynomial_top

end Formalism.FourierDecayAlt.P
