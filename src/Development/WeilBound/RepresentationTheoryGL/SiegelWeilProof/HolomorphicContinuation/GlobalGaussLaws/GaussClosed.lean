module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussFinal
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FTfact
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellA

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem gaussLaw : GaussLaw := gaussian_law_of_weil wEx fTfact

end PositivityTheory.Rg.Sw.Glob
