module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [TopologicalSpace k] [Group G]

abbrev underlyingRep (X : TopRep.{u} k G) : Rep.{u} k G :=
  Rep.of X.ρ.toRepresentation

section Discrete

variable [DiscreteTopology k]

variable [TopologicalSpace G]

end Discrete

end GroundTheory.ProfCoh
