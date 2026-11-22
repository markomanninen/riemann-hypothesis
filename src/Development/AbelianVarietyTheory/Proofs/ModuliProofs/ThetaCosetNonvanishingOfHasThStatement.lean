module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCosetNonvanishing_of_hasTh : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (n : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R) (q : Ideal R), 2 ≤ n → n ∣ N' → t.HasTh x v → q.IsPrime → Coset n N' v q := by
  first | exact @GlobalTheory.coset_of_hasTh | exact GlobalTheory.coset_of_hasTh | (intros; apply GlobalTheory.coset_of_hasTh <;> assumption)
