module

public import Development.WeilBound.ThetaLifts.SphericalLattices.FunAsm
public import Development.WeilBound.ThetaLifts.SphericalLattices.UnitLiftSt
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunAvg
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunCount
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunSieg
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunEvInv
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunChar
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunFin
public import Development.WeilBound.ThetaLifts.SphericalLattices.InvMemKgKCart2

@[expose] public section

namespace PositivityTheory.Sph

theorem sphFun_of_modSt (hM : ModSt) : SphFun :=
  sphFun_of countSt avgSt pInvSt unitLiftSt charSt evInvSt siegSt hM cartanSt2 finSt

end PositivityTheory.Sph
