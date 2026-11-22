module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedOfSmoothOverFieldStatement

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.smoothRed_of :
    SmoothReduced :=
  GlobalTheory.T.isReduced_of_smooth_over_field'
