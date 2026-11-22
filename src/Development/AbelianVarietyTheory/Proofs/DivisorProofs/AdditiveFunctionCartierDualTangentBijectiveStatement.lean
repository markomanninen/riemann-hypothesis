module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFunctionCartierDualTangentBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero

@[expose] public section

open Coalgebra

theorem GlobalTheory.T.additiveFunctionCartierDualTangent_bijective
    {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A]
    [Module.Projective R A] [IsCocomm R A] :
    Function.Bijective (GlobalTheory.PDiv.primTangent R A) :=
  GlobalTheory.PDiv.primTangent_bijective
