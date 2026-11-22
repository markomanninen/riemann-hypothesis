module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcQuotientTwoVariableCoords
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcQuotient_twoVariable_coords : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f → ∀ a : algOver k (FractionRing (PowerSeries k)) ⟶ G, ∃ (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) d ≠ 0 ∧ (∀ i, MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) (h i) = 0) ∧ TwoVar j f a h d := by
  first | exact @GlobalTheory.SS.ArcInf.TwoVarSetup.exists_twoVar | exact GlobalTheory.SS.ArcInf.TwoVarSetup.exists_twoVar | (intros; apply GlobalTheory.SS.ArcInf.TwoVarSetup.exists_twoVar <;> assumption)
