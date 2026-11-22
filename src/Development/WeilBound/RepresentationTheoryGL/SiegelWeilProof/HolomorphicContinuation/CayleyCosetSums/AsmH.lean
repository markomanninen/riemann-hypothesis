module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AsmCore
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.TopHolPf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FarId
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SmoothTop

@[expose] public section

namespace PositivityTheory.Rg.Sw.HSt

theorem asmH : AsmH :=
  asmH_of farId Conv.smoothX topHol rcCongr (fun _ x Z t hx => expLie x Z t hx)

end PositivityTheory.Rg.Sw.HSt
