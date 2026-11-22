module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.ExistsAuxiliaryPrime
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PCjMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PDiscInt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PBarAdj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.MemIffDvd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSides

@[expose] public section

open UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1

namespace UpperTheory.Gal.Int.Geo.Pl

theorem datEx_holds : DatEx := datEx_of exists_auxiliary_prime ArithK_holds SetupEx_holds ScOf_holds PerfCof_holds

theorem sides_holds : Sides := pSides pCjMem (pBarAdj pDiscInt) (pKeyK pDiscInt) RootAt_holds

end UpperTheory.Gal.Int.Geo.Pl
