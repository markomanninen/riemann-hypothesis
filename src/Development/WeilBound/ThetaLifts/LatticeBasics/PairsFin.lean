module

public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsIrrOfArch
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
public import Development.WeilBound.ThetaLifts.SmallCones.SoStab
public import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid

@[expose] public section

namespace GlobalTheory.ThK.Dbl

theorem pairsIrr : PairsIrr := pairsIrr_of_arch PositivityTheory.ThKF.A.archOp

theorem pairsStable : PairsStable :=
  pairsStable_of (PositivityTheory.ThKEnd.Grp.matchStab_of PositivityTheory.ThKF.A.archOp PositivityTheory.ThKF.pureAct PositivityTheory.ThKEst.level PositivityTheory.ThKCT.soStab_of)

end GlobalTheory.ThK.Dbl
