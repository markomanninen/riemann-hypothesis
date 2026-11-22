module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEquivalenceSchemeOfStrictlyHenselianStalksStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem tateTwist_local_to_global_strictlyHenselian : B3 := by
  intro q Y X S f p _ _ _ _ _ i h
  exact GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) Y X S f p
    (fun O _ s hs => h O s hs.1)

end GlobalTheory.EtC
