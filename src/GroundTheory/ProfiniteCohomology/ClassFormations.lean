module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.ClassFormationDefs
public import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
public import GroundTheory.ProfiniteCohomology.ClassFormations.Quotient
public import GroundTheory.ProfiniteCohomology.ClassFormations.Finite

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section QuotQuot

variable {U V V' : Subgroup G} [(V.subgroupOf U).Normal] [(V'.subgroupOf U).Normal]


variable (C : Rep.{u} k G)

variable [IsDiscreteRep C]

end QuotQuot

namespace PreClassFormation

variable [CompactSpace G] [TotallyDisconnectedSpace G]
  {C : Rep.{u} k G} [IsDiscreteRep C] (F : PreClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

end PreClassFormation

namespace ClassFormation

variable [CompactSpace G] [TotallyDisconnectedSpace G]
  {C : Rep.{u} k G} [IsDiscreteRep C] (F : ClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

include F

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem inv_injective (W : OpenSubgroup G) : Function.Injective (F.inv W) :=
  (F.inv_bijective W).1

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem exists_inv_eq (W : OpenSubgroup G) (q : QZ) : ∃ x : H2Open C W, F.inv W x = q :=
  (F.inv_bijective W).2 q


include hVU in
theorem tate_hypotheses (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) :
    IsZero (groupCohomology (Rep.res S.subtype ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U))) 1) ∧
      addOrderOf ((groupCohomology.map S.subtype (𝟙 _) 2).hom
        (F.groupFundamentalClass U V)) = Nat.card S ∧
      ∀ y, ∃ m : ℤ, y = m • (groupCohomology.map S.subtype (𝟙 _) 2).hom
        (F.groupFundamentalClass U V) :=
  F.toPreClassFormation.tate_hypotheses hVU F.inv_injective (F.exists_inv_eq U _) S

end ClassFormation

namespace ClassFormationAt

variable [CompactSpace G] [TotallyDisconnectedSpace G] {P : Set Nat.Primes}
  {C : Rep.{u} k G} [IsDiscreteRep C] (F : ClassFormationAt P C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

include F


variable (hP : ∀ p : Nat.Primes, (p : ℕ) ∣ (V : Subgroup G).relIndex U → p ∈ P)


end ClassFormationAt

end GroundTheory.ProfCoh
