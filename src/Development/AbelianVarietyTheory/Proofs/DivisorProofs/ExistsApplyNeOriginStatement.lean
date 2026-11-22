module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyNeOrigin
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_apply_ne_origin' : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), f ≠ 0 → ∃ a : A.X.left, f.hom.left a ≠ B.origin := by
  first | exact @GlobalTheory.AV.AbVar.exists_apply_ne_origin | exact GlobalTheory.AV.AbVar.exists_apply_ne_origin | (intros; apply GlobalTheory.AV.AbVar.exists_apply_ne_origin <;> assumption)
