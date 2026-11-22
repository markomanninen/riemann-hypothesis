module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionDifferentialsInvariantOneFormsAf
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_retraction_differentials_invariantOneForms_affine : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, ∃ r : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] (Sec A.hom U.unop.1 ⊗[R] GlobalTheory.InvForm.InvForm A), ∀ w : GlobalTheory.InvForm.InvForm A, r (evForm A.hom U w.1) = 1 ⊗ₜ w := by
  first | exact @GlobalTheory.InvFormRetract.retract | exact GlobalTheory.InvFormRetract.retract | (intros; apply GlobalTheory.InvFormRetract.retract <;> assumption)
