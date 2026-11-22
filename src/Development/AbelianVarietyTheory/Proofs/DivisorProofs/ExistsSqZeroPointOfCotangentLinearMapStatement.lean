module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroPointOfCotangentLinearMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.HopfLaurent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sqZeroPoint_of_cotangent_linearMap : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A], (GlobalTheory.LieVB.omega A).IsQuasicoherent → ∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (l : GlobalTheory.SqZeroPt.Wmod A →ₗ[O] M), ∃ (v : GlobalTheory.SqZeroPt.TM O M ⟶ A) (h : GlobalTheory.SqZeroPt.zeroSec O M ≫ v = η[A]), ∀ w, GlobalTheory.SqZeroPt.Phi v h w = l w := by
  first | exact @GlobalTheory.SqZeroPt.exists_Phi_eq_of_linearMap | exact GlobalTheory.SqZeroPt.exists_Phi_eq_of_linearMap | (intros; apply GlobalTheory.SqZeroPt.exists_Phi_eq_of_linearMap <;> assumption)
