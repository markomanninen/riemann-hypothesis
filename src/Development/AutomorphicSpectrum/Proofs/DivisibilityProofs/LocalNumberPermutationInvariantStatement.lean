module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalNumberPermutationInvariant
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_number_permutation_invariant : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (r : ℕ) (e : Equiv.Perm (Fin r)) (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)), (∀ (a : O) (x : Fin r → K → ℤ), laNum P a (x ∘ e) k Q = laNum P a x k Q) ∧ ∀ T : LocPair ι O (Fin r), (T.comp e).ck P k Q = T.ck P k Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.RootPerm.root_perm | exact GlobalTheory.CompanionTheory.Ar.Num.RootPerm.root_perm | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.RootPerm.root_perm <;> assumption)
