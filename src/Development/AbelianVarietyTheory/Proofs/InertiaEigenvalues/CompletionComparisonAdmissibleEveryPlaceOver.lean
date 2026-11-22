module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.BridgeTie

theorem localCoefficientCompatibility : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i :=
  fun D i => coefficient_compatibility_of D i (fun w hw => GlobalTheory.bridge_degW D.nbr i w hw)

end GlobalTheory.BridgeTie
