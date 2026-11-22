module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagBasis
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagMove
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PGrHom
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PSSOfSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.EqZeroOfLowBlk
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PContGL
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PMatEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PMatConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.POpConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.POpUniq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHopGal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PPieceStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PRelDim
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCompSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PDegFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHtotFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHtDesc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PStabOpen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PDegCont
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PExtCont
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PTotCont
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.VFinOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopSpec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtnGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClos
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIdentityMove
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClosD
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RepAsm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGoodHolds

@[expose] public section

namespace UpperTheory.Gal.Int.Geo

theorem bcSplits : G3.BcSplits := G3.pBcSplits (G3.pSplitsBasic (G3.pSplitsPts G3.pIsoPts) G3.pPtsOfSplits)

theorem etGood : G3.EtGood := G3.pEtGood (G3.pEtnGood (G3.pFEtBasic G3.pPtsOfSplits) G3.pEtTr)

theorem galClos : G3.GalClos := G3.pGalClos (G3.pGalClosD (G3.pSplitsPts G3.pIsoPts) (G3.pOrdEx G3.pOrdStep))

theorem hopSpec : G3.HopSpec := G3.pHopSpec etGood (G3.pBcGood bcSplits (G3.pBcGal bcSplits)) galClos (G3.pOpEx G3.pOpTr)
  G3.pOpTr G3.pOpEt (G3.pOpBc bcSplits (G3.pBcGal bcSplits)) bcSplits

theorem grEx : GrEx := grEx_of flagEx_of flagBasis_of flagMove_of grHom_of (grSS_of grHom_of sSOfSum_of)

theorem hopGal : HopGal := hopGal_of hopSpec opConj_of (opUniq_of hopSpec (G3.pOpEx G3.pOpTr) G3.pOpEt etGood bcSplits)

theorem pieceStab : PieceStab := pieceStab_of hopGal

theorem degFin (h : KunnethLefschetz.Core) : DegFin :=
  degFin_of h.qDual KunnethLefschetz.inSum_holds h.inputs.a9 KunnethLefschetz.projBC_holds KunnethLefschetz.sumCl_holds KunnethLefschetz.sumHl_holds KunnethLefschetz.piBC_holds relDim_of compSum_of

theorem htotFin (h : KunnethLefschetz.Core) : HtotFin := htotFin_of (degFin h)

theorem degCont : DegCont := degCont_of (stabOpen_of htDesc_of)

theorem totCont (h : KunnethLefschetz.Core) : TotCont := totCont_of (vFin_of h.inputs) degCont

theorem repEx_core (h : KunnethLefschetz.Core) : RepEx :=
  repEx_of grEx contGL_of matEx_of matConj_of pieceStab (htotFin h) extCont_of (totCont h) KunnethLefschetz.projBC_holds

theorem repEx_holds : RepEx := repEx_core KunnethLefschetz.core_holds

end UpperTheory.Gal.Int.Geo
