module

public import Mathlib
public import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection
public import GroundTheory.AutomorphicForms.UnitaryRepresentations.Integrated

@[expose] public section

namespace GroundTheory.Automorphic

namespace UnitaryRep

open scoped InnerProductSpace
open ContinuousLinearMap Submodule

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

variable {π : UnitaryRep G H}

lemma IsInvariant.iSup {ι : Sort*} {V : ι → Submodule ℂ H} (h : ∀ i, π.IsInvariant (V i)) :
    π.IsInvariant (⨆ i, V i) := by
  intro g v hv
  exact Submodule.iSup_induction V (motive := fun x => π g x ∈ ⨆ i, V i) hv
    (fun i x hx => Submodule.mem_iSup_of_mem i (h i g x hx)) (by simp)
    (fun x y hx hy => by simpa using add_mem hx hy)


section decomposition

variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]

end decomposition

end UnitaryRep

end GroundTheory.Automorphic
