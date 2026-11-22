module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.FrameExOfFin
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.FrameBound
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSwap
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.USideFree
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FinalAllB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PJEigB

@[expose] public section

namespace UpperTheory.BaseChangeIdentities

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F in
theorem baseChangeNB : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  Plug2B.bci_of
    (HeckeLevelFrameExistence.frameEx_of_fin uSide (FX.candFin_of_jEigFin Tail.JB.jEigFin))
    FrameWordIdentity.frameBound FinalAllB.frameRead_holdsB

end UpperTheory.BaseChangeIdentities
