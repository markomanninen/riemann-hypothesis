module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.FrameWordLengthEqOneOfHyp
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.TmulPf
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PHuhecke
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PPsigen
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PChainsc
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PProdok
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PFrfacts
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PPsilet
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PPsiword
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.AtPlaceAppend
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.UokPf
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.TwokPf
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PArchlet
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PArchsc
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PAdelword
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PTestword
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PTraceword
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.PLocWord
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.PLocMatch
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.FrameBoundOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.HM2
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.UnitaryAdjointHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HermitianConvolution.EllHomPf

@[expose] public section

namespace UpperTheory.BaseChangeIdentities.FrameWordIdentity

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.BlockFiniteConvolution

theorem wordId (hW : LocWord) (hM : LocMatch) : WordId := by
  have l1 := frameWord_length_eq_one_of_hyp hW
  have po := prodok_pf tmul_pf locOk₀ l1
  have pw := psiword_pf (psiGen_of_algebras fmAlg' rtAlg' blkLevel) (psilet_pf fmAlg' locOk₀ frfacts_pf) l1 locOk₀
    MatchAll.matchLMId frfacts_pf
  have tw := twok_pf blkWord₀
  have aw := adelWord_of_parts adelRep' finConv' pw po locOk₀ frfacts_pf tw
  have sc := archsc_pf blkWord₀ tw (archlet_pf blkOp₀ FBL.hermInf_holds)
  exact wordId_of (testword_pf pTTest₀ hM pw po usph_pf tw frfacts_pf locOk₀)
    (traceword_pf U.unitary_words_holds hM (chainsc_pf FBL.ellHom_holds) FBL.ellHom_holds aw sc usph_pf
      (uok_pf U.unitary_adjoint_holds huhecke_pf) frfacts_pf)

theorem frameBound : FrameBound :=
  frameBound_of (wordId locWord (locMatch locWord MatchAll.matchLMB2₀ MatchAll.matchLMWordS₀ MatchAll.matchLMUnit₀))

end UpperTheory.BaseChangeIdentities.FrameWordIdentity
