module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelPlaceBuilt2OfHat
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpRFinal

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_bdd (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer) (hBdd : JA.JABddOpQQ) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_hat hJ hG hat_quadratic_operator_holds hBdd

end Formalism.FourierDecayAlt.P.CutMP
