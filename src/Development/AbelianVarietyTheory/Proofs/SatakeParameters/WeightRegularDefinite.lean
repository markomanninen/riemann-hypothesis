module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt

@[expose] public section

namespace GlobalTheory.LocalInv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem weightRegular_definite : ∀ (D : D7), GlobalTheory.LocalInv.WeightRegular D.nd D.naut :=
  fun D => weightRegular_of_ext D.nd D.naut D.nbc

end GlobalTheory.LocalInv
