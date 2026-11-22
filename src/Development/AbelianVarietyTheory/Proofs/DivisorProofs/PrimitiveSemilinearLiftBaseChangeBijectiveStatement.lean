module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveSemilinearLiftBaseChangeBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero

@[expose] public section

open Coalgebra GlobalTheory GlobalTheory.PDiv

theorem _root_.GlobalTheory.T.primitive_semilinearLift_baseChange_bijective
    {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] [CommRing R']
    [Algebra R R'] (hC : Module.Projective R (Cot R (CartierDual R A))) :
    Function.Bijective (liftSemi (toBaseChange R R' A).prim) :=
  liftSemi_prim_toBaseChange_bijective R' hC
