module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseLineBundleGeneratorOfTrivialPullb
public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointwiseLineBundleGenerator_of_trivial_pullback : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB → ∀ q : Y ⟶ X, GlobalTheory.AbLaw.Triv (L.pull q.left) → ∃ t, IsPtGen L q t := by
  first | exact @GlobalTheory.PtExt.exists_isPtGen | exact GlobalTheory.PtExt.exists_isPtGen | (intros; apply GlobalTheory.PtExt.exists_isPtGen <;> assumption)
