module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsAbelianVarietyOfNoPiTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePointsAbelianVarietyOfNoTorsion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_points_abelianVariety_of_no_pi_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (π : 𝓞 E) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → π ≠ 0 → ¬ IsUnit π → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ act.act π = 1 → x = 1) → Finite (𝟙_ (Over (Sp k)) ⟶ A) := by
  first | exact @GlobalTheory.NoPiTorsion.finite_points | exact GlobalTheory.NoPiTorsion.finite_points | (intros; apply GlobalTheory.NoPiTorsion.finite_points <;> assumption)
