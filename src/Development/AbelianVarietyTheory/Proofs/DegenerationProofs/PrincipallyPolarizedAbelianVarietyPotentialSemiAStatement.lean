module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PrincipallyPolarizedAbelianVarietyPotentialSemiA
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
theorem _root_.GlobalTheory.T.principallyPolarizedAbelianVariety_potentialSemiAbelianModel : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ P : Out.PolAV (Sp K), PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  first | exact @GlobalTheory.SemiPol.potModel_semiAbelian | exact GlobalTheory.SemiPol.potModel_semiAbelian | (intros; apply GlobalTheory.SemiPol.potModel_semiAbelian <;> assumption)
