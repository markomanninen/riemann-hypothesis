module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritOf
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UniformInitialGrowth.InitBnd
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.ExistsMeasureLeProd

@[expose] public section

namespace PositivityTheory.Rg.Rs

theorem sqIntCrit_of_finTr (h : FinTr) : SqIntCrit := sqIntCrit_of initBnd_holds h boxvol_holds

end PositivityTheory.Rg.Rs
