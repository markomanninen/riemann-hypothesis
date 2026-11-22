module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLawOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.TensInjOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WeightFactorEqAutomorphy
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocMul
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentPartBlockMatrix
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem gaussLaw_of' (hV : VacK) (hG : GZSch) : GaussLaw := by
  have hT : TensInj := tensInj_of awayIn
  exact gaussLaw_of hT (lawN_of unipTau hT) (lawM_of hT) hV (locMul_of hT) hG lNe

end PositivityTheory.Rg.Sw.Glob
