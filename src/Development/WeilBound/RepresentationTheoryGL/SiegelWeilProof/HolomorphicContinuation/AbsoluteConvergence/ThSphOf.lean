module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphC
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphB

@[expose] public section

namespace PositivityTheory.Rg.Sw.AbsSt

theorem thSph_of : KAK → Mult → DerivativeVacuumDilations → Sph → SecZero → HolParam → LC → NullIff → ThSph :=
  fun hKAK hMult hD hSph hSZ hHP hLC _ => thSph_of' helpA helpC hKAK hMult hD hSph hSZ hHP hLC

end PositivityTheory.Rg.Sw.AbsSt
