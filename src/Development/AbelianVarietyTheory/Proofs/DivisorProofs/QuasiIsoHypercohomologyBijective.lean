module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfQuasiIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem quasiIso_hypercohomology_bijective' : A1 := by
  intro R _ K L f _ F n
  haveI : (res R F).IsKInjective := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).1
  exact GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso R f (res R F) n

end GlobalTheory.EtC
