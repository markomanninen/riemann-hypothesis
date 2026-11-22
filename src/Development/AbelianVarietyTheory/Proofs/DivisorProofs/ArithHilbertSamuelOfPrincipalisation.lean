module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelOfPrincipalisationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelNefOfAmpleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPullOfPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArCalcOfPrincipalisation

@[expose] public section

namespace GlobalTheory

theorem arithHilbertSamuel_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArithHilbertSamuel :=
  fun h => GlobalTheory.T.arithHilbertSamuel_nef_of_ample (GlobalTheory.MixHt.arCalc_of_principalisation h) (GlobalTheory.T.ampleArithHilbertSamuel_of_principalisation h)
    (GlobalTheory.SemiPullAll.semiPull_of_principalisation h)

end GlobalTheory
