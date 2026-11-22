module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IteratedDerivMulConst
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ActsAwayNbar
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompAway
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Decomp
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FTfact
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WopTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocFactPf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussClosed
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSch
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFactPf
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilThetaConvergence.WeilThetaConvergenceOfSiegelSet

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem awayAct_gen (hG : GenA) : AwayAct := awayAct_of hG fTfact decompAway

theorem locFact : LocFact := locFact_of decomp (opGen_of fTfact)

theorem localRepresentationL2 : LocalL2Isometry := local_L2_isometry fTfact

theorem gIdil_gen (h : GlobalTheory.Published.WeilThetaConvergence) (hG : GenA) : GIdil :=
  gIdil_of h gZSch decompAway (awayAct_gen hG) locFact gaussLaw awayIn localRepresentationL2

end PositivityTheory.Rg.Sw.Glob
