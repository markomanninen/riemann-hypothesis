module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TsGenOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DifferentiableSecondCayleyBlockDilation

@[expose] public section

namespace PositivityTheory.Rg.Sw.AbsSt

theorem tsGen : Iwa → CayleyBlocksInvertible → KAK → Mult → SecZero → DerivativeVacuumDilations → HolParam → LC → TSGen :=
  fun _ hD hK hM hS hDF hH hLC => tsGen_of hD hK hM hS hDF hH hLC tsbFacts

end PositivityTheory.Rg.Sw.AbsSt
