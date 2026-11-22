module

public import Development.EtaleCohomology.KummerTheory.InvOfField
public import Development.EtaleCohomology.KummerTheory.LocalHomotopyEtaleCohomology
public import Development.EtaleCohomology.KummerTheory.FinSHInv
public import Development.EtaleCohomology.KummerTheory.FinStalk
public import Development.EtaleCohomology.KummerTheory.FinBock
public import Development.EtaleCohomology.KummerTheory.FinAdicDeg
public import Development.EtaleCohomology.KummerTheory.FinLimit

@[expose] public section

namespace LateralTheory.KummerTheory

theorem goal_holds : GOAL :=
  goal_of LateralTheory.Fin.LH.intersectionNumber_baseChange LateralTheory.Fin.SHInv.intersectionNumber_baseChange LateralTheory.Fin.Stalk.intersectionNumber_baseChange LateralTheory.Fin.Bock.intersectionNumber_baseChange
    LateralTheory.Fin.AdicDeg.intersectionNumber_baseChange LateralTheory.Fin.Limit.intersectionNumber_baseChange

end LateralTheory.KummerTheory
