module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_modelHasJacobianOrder : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ M : Model R A, M.Irr → ∃! n : ℤ, HasOrd M D π n := by
  first | exact @GlobalTheory.SS.Ord.existsUnique_hasOrd | exact GlobalTheory.SS.Ord.existsUnique_hasOrd | (intros; apply GlobalTheory.SS.Ord.existsUnique_hasOrd <;> assumption)
