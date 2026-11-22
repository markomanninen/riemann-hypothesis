module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open TensorProduct MvPolynomial

noncomputable section

universe u v

namespace FlatBC

variable {S S' : Type*} [CommRing S] [CommRing S'] [Algebra S S']

variable {X Y X' Y' : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
  [AddCommGroup X'] [Module S' X'] [AddCommGroup Y'] [Module S' Y']

variable [Module.Flat S S']

end FlatBC

namespace FlatBC

section Hom

variable {R : Type*} [CommRing R] {X Y Z : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
  [Module R Y] [AddCommGroup Z] [Module R Z]

end Hom

end FlatBC

namespace FlatBC

variable {S S' : Type*} [CommRing S] [CommRing S'] [Algebra S S'] [Module.Flat S S']
variable {X Y Z X' Y' Z' : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
  [AddCommGroup Z] [Module S Z] [AddCommGroup X'] [Module S' X'] [AddCommGroup Y'] [Module S' Y']
  [AddCommGroup Z'] [Module S' Z']

end FlatBC

namespace FlatBC

section CechDeg

open Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type*} [CommRing R] {G : Cell U → Type*}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {deg : ∀ I, Submodule R (G I)}
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

end CechDeg

section Poly

variable (S : Type u) [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] (N : ℕ)

variable {S S' N}

end Poly

end FlatBC

namespace FlatBC

section Loc

variable {S : Type u} [CommRing S] {N : ℕ}

variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]

variable {S' : Type u} [CommRing S'] [Algebra S S']
  {M' : Type v} [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M']
  [IsScalarTower S' (Poly S' N) M'] [Module S M'] [IsScalarTower S S' M']
  (f : M →ₗ[S] M')
  (hX : ∀ (i : Fin (N + 1)) (m : M), f ((X i : Poly S N) • m) = (X i : Poly S' N) • f m)



end Loc

end FlatBC

namespace FlatBC

section Grade

variable {S : Type u} [CommRing S] {N : ℕ}
  {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
  {S' : Type u} [CommRing S'] [Algebra S S']
  {M' : Type v} [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M']
  [IsScalarTower S' (Poly S' N) M'] [Module S M'] [IsScalarTower S S' M']
  (f : M →ₗ[S] M')
  (hX : ∀ (i : Fin (N + 1)) (m : M), f ((X i : Poly S N) • m) = (X i : Poly S' N) • f m)
  (hf : IsBaseChange S' f) (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S' N M')
  (hdeg : ∀ (c : ℤ) (m : M), m ∈ 𝓜.piece c → f m ∈ 𝓜'.piece c)




end Grade

end FlatBC

namespace FlatBC

section Final

variable {S : Type u} [CommRing S] {N : ℕ}
  {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
  {S' : Type u} [CommRing S'] [Algebra S S'] [Module.Flat S S']
  {M' : Type v} [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M']
  [IsScalarTower S' (Poly S' N) M'] [Module S M'] [IsScalarTower S S' M']
  (f : M →ₗ[S] M')
  (hX : ∀ (i : Fin (N + 1)) (m : M), f ((X i : Poly S N) • m) = (X i : Poly S' N) • f m)
  (hf : IsBaseChange S' f) (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S' N M')
  (hdeg : ∀ (c : ℤ) (m : M), m ∈ 𝓜.piece c → f m ∈ 𝓜'.piece c) (c : ℤ)

end Final

end FlatBC

end

end GroundTheory.Heights₂.Heights.Kleiman
