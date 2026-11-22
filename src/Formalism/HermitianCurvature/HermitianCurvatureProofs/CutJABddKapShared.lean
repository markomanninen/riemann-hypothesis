module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapNrmW

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jABddKapQQ_of_shared (hG : SSn.SSnGeom) (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines)
    (hDU : SSn.Rep.DatumUnit) : JABddKapQQ :=
  jABddKapQQ_of_cut hG hPE hGL hDU weighted_norm_facts_hold

end Formalism.FourierDecayAlt.P.CutMP.JA
