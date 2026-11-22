module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraOrderActi
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialGoodReduction_of_divisionAlgebra_order_action : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.DivPotGood.potGood_of_divisionAlgebra_action | exact GlobalTheory.DivPotGood.potGood_of_divisionAlgebra_action | (intros; apply GlobalTheory.DivPotGood.potGood_of_divisionAlgebra_action <;> assumption)
