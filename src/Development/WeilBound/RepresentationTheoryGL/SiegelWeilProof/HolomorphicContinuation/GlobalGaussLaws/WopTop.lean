module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HasCLMNbar
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2Isometry
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentPartBlockMatrix
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AdelicConjTransposeBlockMatrixTwoByTwoFin
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Decomp
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayNZ

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem opGen_of (hF : FTfact) : OpGen := opGen_of' unipTau leviTau wEx schOps hF

theorem opCLM_of' (hF : FTfact) : OpCLM := opCLM_of unipTau leviTau wEx schOps hF decomp lNe

theorem local_L2_isometry (hF : FTfact) : LocalL2Isometry :=
  local_isometry_of_hypotheses unipTau leviTau wEx schOps hF decomp lNe planchLoc awayNZ

end PositivityTheory.Rg.Sw.Glob
