module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SetupBasicHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNormHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PAuxPrime
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PArithK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PScOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PRootAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PStdForm

@[expose] public section

open UpperTheory.Gal.W2.Seed

namespace UpperTheory.Gal.G1

theorem exists_auxiliary_prime : AuxiliaryInertOddPrime := exists_auxiliary_prime_cmDatum
theorem ArithK_holds : ArithK := pArithK BarEx_holds QuadEx_holds CEx_holds UnitMod_holds CodiffGen_holds CodiffUnit_holds IdemEx_holds RealGen_holds PosGen_holds DeltaEx_holds PerfOf_holds
theorem ScOf_holds : ScOf := pScOf SetupBasic_holds
theorem RootAt_holds : RootAt := pRootAt

end UpperTheory.Gal.G1
