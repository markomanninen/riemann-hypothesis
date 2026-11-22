module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

def SameDiv {X : Scheme.{0}} {L M : LB X} (σ : L.Sec) (τ : M.Sec) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (i : L.ι) (j : M.ι) (hi : U ≤ L.U i) (hj : U ≤ M.U j) (u : Γ(X, U)ˣ),
    x ∈ U ∧ resG X hi (σ.f i) = (u : Γ(X, U)) * resG X hj (τ.f j)

end GlobalTheory.LogPair
