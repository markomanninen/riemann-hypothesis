module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaugeNormPower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatrixUnitZeroZeroEqInsert
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBTAsm

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem pb_degTop_of (hRA : PBN.RadAATop) (hPT : PBN.PolyTop) : Formalism.FourierDecayAlt.KB.DegTop :=
  degree_top_of_parts word_recursion hRA hPT density_constant

end Formalism.FourierDecayAlt.P
