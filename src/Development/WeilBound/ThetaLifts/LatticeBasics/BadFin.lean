module

public import Development.WeilBound.ThetaLifts.LatticeBasics.BadFactor
public import Development.WeilBound.ThetaLifts.LatticeBasics.PresDOf
public import Development.WeilBound.ThetaLifts.LatticeBasics.NearUnits
public import Development.WeilBound.ThetaLifts.LatticeBasics.RatEquiv
public import Development.WeilBound.ThetaLifts.TowerModels.StabEx

@[expose] public section

namespace GlobalTheory.ThK.Dbl

theorem badFactor : BadFactor := badFactor_of dblX PositivityTheory.ThKG.Tow.stabEx vacFix2 bump

end GlobalTheory.ThK.Dbl
