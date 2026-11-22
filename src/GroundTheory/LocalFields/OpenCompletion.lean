module

public import Mathlib

@[expose] public section

namespace GroundTheory.LocalField

section Completion

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

def openFiniteIndex : Set (Subgroup G) :=
  {H | IsOpen (H : Set G) ∧ H.FiniteIndex}


variable {G} in
def quotientMapOfLE {H H' : Subgroup G} (h : H ≤ H') : G ⧸ H →* G ⧸ H' :=
  QuotientGroup.map H H' (MonoidHom.id G) h


def openCompletion : Subgroup (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) where
  carrier := {a | ∀ (H H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'), quotientMapOfLE h (a H) = a H'}
  one_mem' := fun H H' h => by simp
  mul_mem' := fun ha hb H H' h => by simp [map_mul, ha H H' h, hb H H' h]
  inv_mem' := fun ha H H' h => by simp [map_inv, ha H H' h]

namespace openCompletion

variable {G}






theorem discreteTopology_quotient (H : openFiniteIndex G) : DiscreteTopology (G ⧸ (H : Subgroup G)) :=
  QuotientGroup.discreteTopology H.2.1

end openCompletion

end Completion

end GroundTheory.LocalField
