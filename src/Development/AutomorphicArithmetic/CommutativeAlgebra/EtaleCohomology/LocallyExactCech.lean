module

public import Mathlib

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Et

abbrev PMod (R : Type) [CommRing R] : Type 2 := Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)

variable {R : Type} [CommRing R]

abbrev sec (M : PMod R) (U : Scheme.{0}) : Type 1 := M.obj (op U)

abbrev rs (M : PMod R) {V U : Scheme.{0}} (g : V ⟶ U) (x : sec M U) : sec M V := (M.map g.op).hom x

abbrev ap {M N : PMod R} (α : M ⟶ N) {U : Scheme.{0}} (x : sec M U) : sec N U := (α.app (op U)).hom x

def LocT (τ : GrothendieckTopology Scheme.{0}) (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Prop :=
  ∃ S : Sieve U, S ∈ τ U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → P V g

def Inv (q : ℕ) (U : Scheme.{0}) : Prop := IsUnit (q : Γ(U, ⊤))

def Gen (τ : GrothendieckTopology Scheme.{0}) (q : ℕ) (M : PMod R) {U : Scheme.{0}} (g : sec M U) : Prop :=
  q • g = 0 ∧ (∀ (V : Scheme.{0}) (k : V ⟶ U) (c : ℕ), Nonempty V → c • rs M k g = 0 → q ∣ c) ∧
  ∀ (V : Scheme.{0}) (k : V ⟶ U) (y : sec M V), LocT τ V fun _ h => ∃ c : ℕ, rs M h y = c • rs M (h ≫ k) g

section Cech
variable {Y X : Scheme.{0}} (f : Y ⟶ X)




variable {f}

variable (f)


end Cech

end UpperTheory.Et

end
