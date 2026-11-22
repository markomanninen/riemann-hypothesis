module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCoreAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstAsmS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepPolyFinish
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLines
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSPointwise
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSEntry

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem thConst_of_open (hMC : Core.TC.ModConst) (hLN : Core.TC.LineNonzero)
    (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : Core.ThConst := by
  rcases hPoly with h | h
  · exact Core.TC.theta_constancy_assembly h hMC hLN Core.TC.polynomial_finish_holds
  · exact Core.TC.theta_constancy_assembly_scalar h hMC hLN Core.TC.polynomial_finish_holds

theorem ssnRep_of_open (hPE : PRho.PRhoExists) (hTF : ThtFacts) (hMC : Core.TC.ModConst)
    (hLN : Core.TC.LineNonzero) (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : SSnRep :=
  second_shift_representation_assembly hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds hTF datum_unit_norm_holds
    (Core.theta_gauge_constancy_holds Formalism.FourierDecayAlt.P.CutMP.JA.quadratic_second_shift_form Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_pointwise_holds
      (thConst_of_open hMC hLN hPoly) Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_entry_holds hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds
      datum_unit_norm_holds)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
