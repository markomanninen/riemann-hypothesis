module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.InducedPull

variable {X X' Z : Scheme.{0}}

theorem val_pull_g (B : LB X) (a : Z ⟶ X) (i i' : (B.pull a).ι)
    (l : (B.pull a).U i ⊓ (B.pull a).U i' ≤ a ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit))) :
    ((B.pull a).g i i').val = (a.appLE _ _ l).hom (B.g (i PUnit.unit) (i' PUnit.unit)).val := by
  have : (B.pull a).g i i' = res l (pullU a _ (B.g (i PUnit.unit) (i' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  rw [this]
  rfl

end GlobalTheory.TrueGeo.InducedPull
