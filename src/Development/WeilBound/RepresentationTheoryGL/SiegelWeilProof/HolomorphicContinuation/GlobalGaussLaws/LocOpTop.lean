module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocFactPf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.EvXTemperate
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem locOpEx_of_locFact (hF : LocFact) : LocOpEx := locOpEx_of_fact hF awayIn schFP lNe

end PositivityTheory.Rg.Sw.Glob
