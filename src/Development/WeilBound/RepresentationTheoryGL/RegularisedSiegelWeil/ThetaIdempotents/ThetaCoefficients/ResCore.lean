module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.SphBound
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.HasLevel
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIdemEx
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEv
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LBumpEx
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajor
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MatGExt
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.GenK
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WMaj
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FixW
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixTh
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThProd
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LRowTotal
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.MuCellTop
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibEx
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterQuadraticFormIdentity
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LPosExt
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxId
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EisMeasTop
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LNullSing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdemExTrans
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEqSmulOfInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongrOverOfFrame
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularStab
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIkSch
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ProjKComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsLast
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.ContinuousHermitianInnerSelf
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FromColsSmulApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendByZeroHermitianVal
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThCoef
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFourierPt
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.JstTranspose
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.JPosOfIdemEx
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRel
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfInv
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBdd
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLow
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutId
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LResCore

@[expose] public section

theorem PositivityTheory.Rg.Rsw.resCore : PositivityTheory.Rg.Rsw.ResCore :=
  open PositivityTheory.Rg.Rsw in
  have i := PositivityTheory.Rg.Rsw.L.idemEx
  have ge := PositivityTheory.Rg.Rsw.L.goodEv i
  have be := PositivityTheory.Rg.Rsw.L.bumpEx i
  have wm := PositivityTheory.Rg.Rsw.L.wMaj
  have tp := PositivityTheory.Rg.Rsw.L.thProd wm
  have rt := PositivityTheory.Rg.Rsw.L.rowTotal i be
  have fw := PositivityTheory.Rg.Rsw.L.fixW i PositivityTheory.Rg.Rsw.L.genK wm
  have ns := PositivityTheory.Rg.Rsw.L.nullSing i
  have t2 := GlobalTheory.CompanionTheory.ColumnSplitting.main i PositivityTheory.Rg.Rsw.L.latBound GlobalTheory.CompanionTheory.QKAvg.qk PositivityTheory.Rg.Rsw.L.ikSch
  have em := PositivityTheory.Rg.Rsw.Em.eisMeas i be (PositivityTheory.Rg.Rsw.L.major i ge be) fw (PositivityTheory.Rg.Rsw.L.fixTh i PositivityTheory.Rg.Rsw.L.geng PositivityTheory.Rg.Rsw.L.genK) tp (PositivityTheory.Rg.Rsw.Cell.muCell htExist i)
    PositivityTheory.Rg.Rsw.L.fibEx (GlobalTheory.CompanionTheory.RCellP.rcell wm PositivityTheory.Rg.Rsw.L.partFT) PositivityTheory.Rg.Rsw.L.posExt (PositivityTheory.Rg.Rsw.L.approxId i)
  have mi := PositivityTheory.Rg.Rsw.L.muId i ge be tp em ns (GlobalTheory.CompanionTheory.OrbUniq.uniq_of_trans i ns (GlobalTheory.CompanionTheory.RgTrans.idemEx_trans i)) (GlobalTheory.CompanionTheory.RswNoFrame.noFrame i) t2 (PositivityTheory.Rg.Rsw.L.toS i)
  have ci := GlobalTheory.CompanionTheory.RkCoef.target polar resMu mapsExist cfFJ pcBound pcFc rSec htExist tp rt wm PositivityTheory.Rg.Rsw.L.ikSch t2 mi
  have tb := PositivityTheory.Rg.Rsw.L.thBdd wm PositivityTheory.Rg.Rsw.L.latBound PositivityTheory.Rg.Rsw.L.wa1
  have cl := PositivityTheory.Rg.Rsw.L.cutLow PositivityTheory.Rg.Rsw.L.fourierPt PositivityTheory.Rg.Rsw.L.wa1
  have ie := (fun _ _ _ => PositivityTheory.Rg.Rsw.L.ikEq2 : PositivityTheory.Rg.Rsw.L.GenG → PositivityTheory.Rg.Rsw.L.WMaj → PositivityTheory.Rg.Rsw.L.IkSch → PositivityTheory.Rg.Rsw.L.IkEq) PositivityTheory.Rg.Rsw.L.geng wm PositivityTheory.Rg.Rsw.L.ikSch
  have tc := PositivityTheory.Rg.Rsw.L.thCoef PositivityTheory.Rg.Rsw.L.latBound
  PositivityTheory.Rg.Rsw.L.resCore polar cfFJ i ge fw wm (GlobalTheory.CompanionTheory.Jp.jPos_of_idemEx i) (PositivityTheory.Rg.Rsw.L.cfRel htExist) PositivityTheory.Rg.Rsw.L.cfInv cl
    (PositivityTheory.Rg.Rsw.L.cutId polar cfFJ ci tc PositivityTheory.Rg.Rsw.L.fourierPt PositivityTheory.Rg.Rsw.L.wa1 PositivityTheory.Rg.Rsw.L.cfInv tb cl PositivityTheory.Rg.Rsw.L.ikSch ie wm) tb tc PositivityTheory.Rg.Rsw.L.ikSch ie
