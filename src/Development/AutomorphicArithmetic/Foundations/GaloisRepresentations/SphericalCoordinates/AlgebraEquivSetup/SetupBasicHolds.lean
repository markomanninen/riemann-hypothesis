module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PBarEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ExistsClose
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCodiffGen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDeltaEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDiagTrace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormOKSt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormPerfSt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PHdSign
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIdemEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLiftEx
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateSqrtNeg
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.POrbEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfCof
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PQuadEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepAdj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepLaws
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSetupBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTraceType
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HenselRoot
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PUnitMod
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCodiffUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormCoord
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKqEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.POrient
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealIso
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSigSt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAtPEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDomSt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPosGen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealGen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSetupEx

@[expose] public section

namespace UpperTheory.Gal.W2.Seed

theorem BarEx_holds : BarEx := pBarEx
theorem CEx_holds : CEx := pCEx
theorem CodiffGen_holds : CodiffGen := pCodiffGen
theorem DeltaEx_holds : DeltaEx := pDeltaEx
theorem DiagTrace_holds : DiagTrace := pDiagTrace
theorem FormOKSt_holds : FormOKSt := pFormOKSt
theorem FormPerfSt_holds : FormPerfSt := pFormPerfSt
theorem HdSign_holds : HdSign := pHdSign
theorem IdemEx_holds : IdemEx := pIdemEx
theorem LiftEx_holds : LiftEx := pLiftEx
theorem OrbEx_holds : OrbEx := pOrbEx
theorem PerfCof_holds : PerfCof := pPerfCof
theorem PerfOf_holds : PerfOf := pPerfOf
theorem QuadEx_holds : QuadEx := pQuadEx
theorem RepAdj_holds : RepAdj := pRepAdj
theorem RepEx_holds : RepEx := pRepEx
theorem RepLaws_holds : RepLaws := pRepLaws
theorem SetupBasic_holds : SetupBasic := pSetupBasic
theorem TraceType_holds : TraceType := pTraceType
theorem UEx_holds : UEx := pUEx
theorem UnitMod_holds : UnitMod := pUnitMod
theorem CodiffUnit_holds : CodiffUnit := pCodiffUnit UnitMod_holds
theorem FormCoord_holds : FormCoord := pFormCoord TraceType_holds
theorem KqEx_holds : KqEx := pKqEx TraceType_holds
theorem Orient_holds : Orient := pOrient TraceType_holds HdSign_holds
theorem RealIso_holds : RealIso := pRealIso TraceType_holds
theorem SigSt_holds : SigSt := pSigSt HdSign_holds
theorem AtPEx_holds : AtPEx := pAtPEx KqEx_holds UEx_holds OrbEx_holds LiftEx_holds
theorem DomSt_holds : DomSt := pDomSt TraceType_holds RealIso_holds FormCoord_holds HdSign_holds DiagTrace_holds
theorem PosGen_holds : PosGen := pPosGen CodiffUnit_holds
theorem RealGen_holds : RealGen := pRealGen CodiffGen_holds CodiffUnit_holds
theorem SetupEx_holds : SetupEx := pSetupEx FormOKSt_holds FormPerfSt_holds SigSt_holds DomSt_holds AtPEx_holds RepEx_holds RepLaws_holds RepAdj_holds Orient_holds

end UpperTheory.Gal.W2.Seed
