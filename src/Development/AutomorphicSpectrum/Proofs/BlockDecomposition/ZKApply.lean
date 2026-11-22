module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.BasisBase

def zK {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (Q : ObjectProperty (Thick (smFun X q))) (t u : ℤ) (ht : t ≤ 0) (j : ℕ) : HdR q j →ₗ[K] HQ Q t u j :=
  ((toSq (sFil Q t) (sFil Q u) fun T => by
    change T.obj.pdPow t.toNat = ⊤
    rw [Int.toNat_of_nonpos ht, Thick.pdPow_zero]).pull j).comp (resK q Q j)

end GlobalTheory.CompanionTheory.BasisBase
