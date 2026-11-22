module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.Factor
public import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
public import Development.WeilBound.ThetaLifts.FrameEstimates.HodgeTateFromSandwich

@[expose] public section

namespace PositivityTheory.ThKClose

theorem domWeil_of (h : PositivityTheory.ThKEst.DomWeilU) : PositivityTheory.ThKEst.DomWeil := PositivityTheory.ThKEst.domWeil_of_U h

theorem soSemi_of (h : PositivityTheory.ThKEst.SoSemiU) : PositivityTheory.ThKEst.SoSemi := PositivityTheory.ThKEst.soSemi_of_U h

end PositivityTheory.ThKClose
