module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition

@[expose] public section

noncomputable section

namespace GlobalTheory.Proof.EigenvalueCoprimeConjugation

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual Formalism.CyclotomicNorms ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.WeilDeligne

variable (D : D7)

theorem normV_plGw (k : Fin 2) (v : D.nd.PlG k) : normV (D.naut.plGw k v) = D.host.g k :=
  normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v)

end GlobalTheory.Proof.EigenvalueCoprimeConjugation

end
