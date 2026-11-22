module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopSpec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtnGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClos
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClosD
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIdentityMove

@[expose] public section

open UpperTheory.Gal.Seam

private theorem bcSplits : UpperTheory.Gal.G3.BcSplits :=
  UpperTheory.Gal.G3.pBcSplits (UpperTheory.Gal.G3.pSplitsBasic (UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts) UpperTheory.Gal.G3.pPtsOfSplits)

private theorem hopSpec : UpperTheory.Gal.G3.HopSpec :=
  UpperTheory.Gal.G3.pHopSpec
    (UpperTheory.Gal.G3.pEtGood (UpperTheory.Gal.G3.pEtnGood (UpperTheory.Gal.G3.pFEtBasic UpperTheory.Gal.G3.pPtsOfSplits) UpperTheory.Gal.G3.pEtTr))
    (UpperTheory.Gal.G3.pBcGood bcSplits (UpperTheory.Gal.G3.pBcGal bcSplits))
    (UpperTheory.Gal.G3.pGalClos (UpperTheory.Gal.G3.pGalClosD (UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts)
      (UpperTheory.Gal.G3.pOrdEx UpperTheory.Gal.G3.pOrdStep)))
    (UpperTheory.Gal.G3.pOpEx UpperTheory.Gal.G3.pOpTr) UpperTheory.Gal.G3.pOpTr UpperTheory.Gal.G3.pOpEt
    (UpperTheory.Gal.G3.pOpBc bcSplits (UpperTheory.Gal.G3.pBcGal bcSplits)) bcSplits

theorem UpperTheory.Gal.Seam.hopExS :
    True → HopEx := by
  intro _ l _ k Ω _ _ _ _ _ H hN g
  obtain ⟨d, hd⟩ := hN.2.2 g
  have hl : (l : k) ≠ 0 := by
    intro h
    have h0 : (l : Ω) = 0 := by rw [← map_natCast (algebraMap k Ω), h, map_zero]
    exact (Fact.out : l.Prime).ne_zero (Nat.cast_eq_zero.mp h0)
  exact (hopSpec l hl H Ω g d hd).1
