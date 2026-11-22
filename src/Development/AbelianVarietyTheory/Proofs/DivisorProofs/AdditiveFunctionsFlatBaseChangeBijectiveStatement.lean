module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFunctionsFlatBaseChangeBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero

@[expose] public section

open GlobalTheory.PDiv

theorem GlobalTheory.T.additiveFunctions_flatBaseChange_bijective {R A : Type} (R' : Type)
    [CommRing R] [CommRing A] [Bialgebra R A] [CommRing R'] [Algebra R R'] [Module.Flat R R'] :
    Function.Bijective (liftSemi (toBaseChange R R' A).prim) :=
  liftSemi_prim_baseChange_bijective R'
