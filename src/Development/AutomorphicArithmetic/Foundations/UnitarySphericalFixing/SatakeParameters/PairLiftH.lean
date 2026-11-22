module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualOfLabels
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MembersGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompAtEqOneOfTameAt
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ClsEqOfLocVEqG
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralTwistStable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.SplitPairLift

namespace UpperTheory.One.M

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def RepGood {T : WDTie N A} (S : Reading T) : Prop := ∀ i w hw P, GoodI ((S i w hw).rep P)

end UpperTheory.One.M
