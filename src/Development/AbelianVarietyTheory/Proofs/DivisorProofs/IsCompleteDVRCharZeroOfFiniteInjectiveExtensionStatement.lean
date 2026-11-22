module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompleteDVRCharZeroOfFiniteInjectiveExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompleteDVRCharZero_of_finiteInjectiveExtension : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R → FinExt ρ → GlobalTheory.LN.CDvr R' := by
  first | exact @GlobalTheory.Mum.cDvr_of_finExt | exact GlobalTheory.Mum.cDvr_of_finExt | (intros; apply GlobalTheory.Mum.cDvr_of_finExt <;> assumption)
