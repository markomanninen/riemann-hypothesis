module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericNoetherNormalisation
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProofSimp

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Polynomial MvPolynomial Ideal Nat RingHom List

namespace GenericNoetherNormalisation

section Nagata

variable {A : Type*} [CommRing A] [IsDomain A] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) A)
variable (v w : Fin (n + 1) →₀ ℕ)



end Nagata

section Combination

variable {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {m : ℕ}

variable {c : A} {z : Fin m → D} {s : Finset D}

end Combination

universe u

theorem proof : GenericNoetherNormalisation.Statement.{u} :=
  _root_.UpperTheory.Reformulated.B.GenericNoetherNormalisationCapelliIdentities.proof

end GenericNoetherNormalisation

end GroundTheory.Heights₂.Heights
