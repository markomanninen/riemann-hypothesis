module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinorCellOfPartsAlt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtNormPow
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JacquetRaisingOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialSideRaising
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbTopFirstOf

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem minor_cell : PBN.MinorCell :=
  minor_cell_of_parts right_rule_derivative left_rule_cell torus_cell gauge_positivity

theorem radial_raising_top : PBN.RadAATop :=
  radial_raising_top_of_parts jacquet_raising_operator raising_cell minor_cell radial_side_raising raising_compact_support

theorem pb_degTop_of_polyTop (hPT : PBN.PolyTop) : Formalism.FourierDecayAlt.KB.DegTop := pb_degTop_of radial_raising_top hPT

end Formalism.FourierDecayAlt.P
