module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefRealA

@[expose] public section

namespace PositivityTheory.ThKEst

theorem coefReal_of : CoefReal := fun _ _ _ _ _ _ N => RealFourierCoefficientBounds.main N

end PositivityTheory.ThKEst
