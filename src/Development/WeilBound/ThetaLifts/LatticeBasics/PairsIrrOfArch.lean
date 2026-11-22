module

public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsB
public import Development.WeilBound.ThetaLifts.LatticeBasics.PolFin
public import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep

@[expose] public section

namespace GlobalTheory.ThK.Dbl

theorem polFinTri : PolFin := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => polFin (PositivityTheory.ThKG.pairV h)

theorem pairsIrr_of_arch (hO : PositivityTheory.ThKF.ArchOp) : PairsIrr :=
  pairsIrr_of PositivityTheory.ThKH.Locrep.locRepEx PositivityTheory.ThKF.pureAct hO polFinTri

end GlobalTheory.ThK.Dbl
