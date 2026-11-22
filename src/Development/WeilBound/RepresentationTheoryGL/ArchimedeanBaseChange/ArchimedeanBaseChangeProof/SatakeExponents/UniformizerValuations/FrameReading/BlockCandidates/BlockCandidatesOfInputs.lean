module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.BlockCandOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PPowNe
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.FrameMatrixPowerHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.PLevRead
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.LevIdem
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreePrecursors.PreOfTreeHolds

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.BC

theorem level_reading_holds : FG.LevRead := FG.levReadOf_holds (levIdem slots)

theorem block_candidates_of_inputs (h1 : ChiTr) (h2 : LimAt) (h3 : Ident) : BlockCand :=
  blockCand_of h1 h2 h3 (powNeOf_holds FA.convMul_holds) SpectralAccumulation.preOfTree_holds RS.joinEx_holds level_reading_holds
    (FG.frGood_of level_reading_holds) FG.frame_weight_holds

end PositivityTheory.Rg.BcB.F.BC
