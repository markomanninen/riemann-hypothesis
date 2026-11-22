module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritOfFinTr
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag

@[expose] public section

namespace PositivityTheory.Rg.Rs

theorem sqIntCrit_holds : SqIntCrit := sqIntCrit_of_finTr finTr_holds

end PositivityTheory.Rg.Rs
