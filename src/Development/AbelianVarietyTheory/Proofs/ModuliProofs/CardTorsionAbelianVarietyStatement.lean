module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_eq_pow_two_mul_dim : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g N : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (N : k) ≠ 0 → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ B // x ^ N = 1} = N ^ (2 * g) := by
  first | exact @GlobalTheory.card_torsion_abelianVariety | exact GlobalTheory.card_torsion_abelianVariety | (intros; apply GlobalTheory.card_torsion_abelianVariety <;> assumption)
