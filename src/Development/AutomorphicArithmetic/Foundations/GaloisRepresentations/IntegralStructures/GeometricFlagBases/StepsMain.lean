module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.MapInvMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RepMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCutStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.AevalSmulProd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwCrys
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwJ
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CharPolEqRootPol
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.UnrPolNegOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.SatCard
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.JumpsOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RichOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EsStepHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractHolds

@[expose] public section

namespace UpperTheory.Gal.Int.Geo

theorem steps_of (hC : CrysStep) (hJ : JumpStep) (hP : PhiStep) : Steps :=
  ⟨repEx_holds, Mod.esStep_holds, hC, hJ, hP, cutStep_holds, twES, twCrys, twJ, twPhi, phiOf, satCard, jumpsOf, richOf,
    TP.Sub.charEx, TP.Sub.sSLeft_holds, TP.Sub.contLeft_holds⟩

end UpperTheory.Gal.Int.Geo
