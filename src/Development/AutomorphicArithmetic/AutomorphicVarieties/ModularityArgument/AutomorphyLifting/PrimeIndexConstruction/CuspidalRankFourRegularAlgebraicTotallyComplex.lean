module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CuspidalRankFourRegularAlgebraic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.HalfPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc

@[expose] public section

open UpperTheory.GalN.V UpperTheory.V.Ws.Pt UpperTheory.V.Z.Win

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp Formalism.BasicNotions Formalism.MainNotions.N

namespace UpperTheory.V.Z.Win.Birth

def CuspidalRankFourRegularAlgebraicTotallyComplex {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (π : CuspSub L 4) : Prop := (CG.mk π).IsRegAlg ∧ ImaginaryQuadraticEtaCharacter.AllWin π

theorem mkReg' {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {π : CuspSub L 4} (h : (CG.mk π).IsRegAlg) (u : ImaginaryQuadraticEtaCharacter.AllWin π) :
    CuspidalRankFourRegularAlgebraicTotallyComplex π := ⟨h, u⟩

end UpperTheory.V.Z.Win.Birth
