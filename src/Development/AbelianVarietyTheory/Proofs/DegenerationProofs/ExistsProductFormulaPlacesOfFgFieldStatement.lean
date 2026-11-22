module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProductFormulaPlacesOfFgField
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
theorem _root_.GlobalTheory.T.exists_productFormula_places_of_fg_field : ∀ (k : Type) [Field k] [IsAlgClosed k] (K : Type) [Field K] [Algebra k K], (⊤ : IntermediateField k K).FG → ∃ Pl : Places k K, ∀ x : K, (∀ i, x ∈ Pl.O i) → x ∈ Set.range (algebraMap k K) := by
  first | exact @GlobalTheory.SS.exists_places_of_fg | exact GlobalTheory.SS.exists_places_of_fg | (intros; apply GlobalTheory.SS.exists_places_of_fg <;> assumption)
