module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PlaceData
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClosD
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdStep

@[expose] public section

theorem UpperTheory.Gal.Mod.galEx : UpperTheory.Gal.Mod.GalEx := UpperTheory.Gal.G3.pGalClosD (UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts)
  (UpperTheory.Gal.G3.pOrdEx UpperTheory.Gal.G3.pOrdStep)
