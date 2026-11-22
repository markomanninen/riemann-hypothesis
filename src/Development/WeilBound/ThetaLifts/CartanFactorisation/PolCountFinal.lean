module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.PolCount
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFock

@[expose] public section

namespace PositivityTheory.ThKF

theorem polCount_of_derEx (h : GlobalTheory.RealLift.DerEx) : PolCount :=
  PC.polCount_of (PositivityTheory.RL.fockEx h) (PositivityTheory.RL.vacLine h)

end PositivityTheory.ThKF
