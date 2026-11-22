module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopActCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopActAlg

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem top_action_on_gauge_holds : GTRTopAct := TopAct.gTRTopAct_of_cut quadratic_top_algebra_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
