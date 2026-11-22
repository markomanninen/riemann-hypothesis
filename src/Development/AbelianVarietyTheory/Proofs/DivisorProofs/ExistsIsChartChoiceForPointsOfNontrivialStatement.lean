module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsChartChoiceForPointsOfNontrivial
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
theorem _root_.GlobalTheory.T.exists_isChartChoiceForPoints_of_nontrivial : ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∃ j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι, IsChoice P j := by
  first | exact @GlobalTheory.PtExt.exists_isChoice | exact GlobalTheory.PtExt.exists_isChoice | (intros; apply GlobalTheory.PtExt.exists_isChoice <;> assumption)
