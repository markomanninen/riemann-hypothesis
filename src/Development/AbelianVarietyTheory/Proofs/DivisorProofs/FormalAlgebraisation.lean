module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphismsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationProperFormalSchemeAmpleBundleStatement

@[expose] public section

namespace GlobalTheory

theorem formalAlgebraisation : GlobalTheory.Published.FormalAlgebraisation :=
  ⟨GlobalTheory.T.formalAlgebraisation_morphisms', GlobalTheory.T.algebraisation_properFormalScheme_ampleBundle⟩

end GlobalTheory
