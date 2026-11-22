module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoCechNerveChainsOfEtaleLocallySurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveEtaleLocallyHasSectionsStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace GlobalTheory.EtC

theorem chains_cechAug_quasiIso_of_smooth (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X)
    [Smooth f] [Surjective f] : QuasiIso ((chains R).map (cechAug f)) :=
  GlobalTheory.T.quasiIso_cechNerveChains_of_etaleLocallySurjective R (yoneda.map f) (fun U y => GlobalTheory.T.smooth_surjective_etale_locally_has_sections f U y)

end GlobalTheory.EtC
