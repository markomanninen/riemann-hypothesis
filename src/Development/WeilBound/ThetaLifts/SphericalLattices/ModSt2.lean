module

public import Development.WeilBound.ThetaLifts.SphericalLattices.RelIndexTransport
public import Development.WeilBound.ThetaLifts.SphericalLattices.LocMod
public import Development.WeilBound.ThetaLifts.SphericalLattices.ExistsFrameLag

@[expose] public section

namespace PositivityTheory.Sph

theorem modSt2 : ModSt := M2.modSt_of M2.chart M2.locMod

end PositivityTheory.Sph
