module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationPerfectPairing
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
theorem _root_.GlobalTheory.T.de_rham_polarization_perfect_pairing : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[k] HdR B →ₗ[k] k, AbDual.IsCorrForm (dp0 k) (𝟙 _) A B P φ → φ.IsPerfPair := by
  first | exact @GlobalTheory.FieldPerf.isPerfPair | exact GlobalTheory.FieldPerf.isPerfPair | (intros; apply GlobalTheory.FieldPerf.isPerfPair <;> assumption)
