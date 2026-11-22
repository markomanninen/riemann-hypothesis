module

public import Development.WeilBound.ThetaLifts.Reductions.MetaplecticDerivatives.ContinuousTo
public import Development.WeilBound.ThetaLifts.Reductions.MetaplecticDerivatives.MetaplecticUnipotentBlockSecondDiag
public import Development.WeilBound.ThetaLifts.Reductions.MetaplecticDerivatives.MapOfRealMul
public import Development.WeilBound.ThetaLifts.Reductions.MetaplecticDerivatives.HasFDerivAtOfCurves
public import Development.WeilBound.ThetaLifts.Reductions.MetaplecticDerivatives.MetaplecticGroupT2Space
public import Development.WeilBound.ThetaLifts.Reductions.MetaplecticDerivatives.HasFDerivAtOrb

@[expose] public section

open PositivityTheory.ThKR.Mp in
theorem PositivityTheory.ThKR.realMetaplecticRepresentation_holds : GlobalTheory.Published.RealMetaplecticRepresentation :=
  realMetaplectic_of_forall fun l _ _ _ =>
    have hS : SecEx l := secEx_of mkElt nrmUp
    have hO : Surj l := surj_of ddNe hS
    have hN : NearOne l := nearOne_of hS ker secDer
    have hC : Cover l := cover_of topG hO ker hS secDer
    ⟨topG, hC, hO, ker, smooth_of topG hN secDer, onePar_of topG hC hN secDer⟩
