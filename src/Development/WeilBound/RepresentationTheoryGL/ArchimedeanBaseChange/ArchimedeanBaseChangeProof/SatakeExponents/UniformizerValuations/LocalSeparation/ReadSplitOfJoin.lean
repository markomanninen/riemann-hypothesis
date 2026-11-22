module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.LeafSeparation.LeafModHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PTreeModOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PReadModOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PTreeSatOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PPairSat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.SaturationTransportPair
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChiDetPowSplitCentre
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfOfTwPart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatVMapMulChi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasInfCharGLRankZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisFurther
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitAtOfValuation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFlipGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmVecTranslate

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.RS

theorem joinEx_holds : JoinEx := GlobalTheory.CompanionTheory.JoinDatum.joinEx

theorem joinInf_holds : JoinInf := GlobalTheory.CompanionTheory.JoinInfProof.joinInf

theorem joinSat_holds : JoinSat := GlobalTheory.CompanionTheory.JoinSatPf.joinSat

theorem treeInf_holds : TreeInf := GlobalTheory.CompanionTheory.TreeInfSum.treeInf

theorem weightJoin_holds : WeightJoin := GlobalTheory.CompanionTheory.WeightJoin.main

theorem muLoc_holds' : MuLoc := GlobalTheory.CompanionTheory.MuLocal.muLoc_holds

theorem treeMod_of (h : JoinMod) : TreeMod := treeModOf_holds leafMod_holds GlobalTheory.CompanionTheory.NodeSep.nodeMod h

theorem readMod_of (h : JoinMod) : ReadMod := readModOf_holds (treeMod_of h)

theorem readSplit_of_join (h : JoinMod) : ReadSplit :=
  readSplit_of (treeSatOf_holds (treeMod_of h)) pairSat_holds thetaSat2_holds GlobalTheory.CompanionTheory.CtS.ctSat muLoc_holds' joinSat_holds
    GlobalTheory.CompanionTheory.SatSplitAt.satSplit GlobalTheory.CompanionTheory.ConjSat.satConj

end PositivityTheory.Rg.BcB.F.RS
