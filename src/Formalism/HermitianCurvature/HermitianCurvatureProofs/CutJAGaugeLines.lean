module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesLeft
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesRight

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem gauge_lines_holds : PRho.GaugeLines :=
  PRho.GL.gaugeLines_of_cut PRho.GL.gauge_right_line_holds PRho.GL.gauge_left_line_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
