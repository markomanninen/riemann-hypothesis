module

public import Development.WeilBound.ThetaLifts.LocalTheory.StepFacEq
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CuspidalClassOfWeilConvergence
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Kills0Of
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
public import Development.WeilBound.ThetaLifts.LatticeBasics.PolDense
public import Development.WeilBound.ThetaLifts.TowerModels.LeviEx
public import Development.WeilBound.ThetaLifts.LeviDeterminants.ActsEx

@[expose] public section

namespace PositivityTheory.ThKG.Loc

open GlobalTheory.ThK PositivityTheory.ThKF

theorem hyp_of (hT : ThetaBasic) (hW : WeilConv) (hS : SoCont) (hD : KDecay) (hC : KCoinv) (hK : Kills) (hO : ArchOp) (hL : ArchLie)
    (hU : ArchUniq) (hE : SplitEx) (hI : SplitInv2) (h0 : EvZero) (hF : FacNe) : Hyp :=
  ⟨PositivityTheory.ThKF0.actsEx, hW, hS, hD, hC, hK, kills0_of hT hW hC hK, hO, hL, hU,
    injPure_of hO hL hU PositivityTheory.ThKF0.actsEx hW hS hD hC hK (kills0_of hT hW hC hK), hE, hI, PositivityTheory.ThKG.Tow.leviEx, h0,
    GlobalTheory.ThK.Dbl.polDense, hF, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp _ hΦ g => I_left unimodularity_holds hT hp hΦ g⟩

end PositivityTheory.ThKG.Loc
