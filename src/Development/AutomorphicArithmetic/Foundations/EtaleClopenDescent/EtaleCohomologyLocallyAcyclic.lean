module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialCohomologyVanishingStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.Cb.etale_cohomology_locally_acyclic :
    GlobalTheory.EtC.C5 :=
  GlobalTheory.T.etale_cohomology_locally_acyclic
