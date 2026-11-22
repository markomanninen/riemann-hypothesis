module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivedSeriesDerivation
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorBundlePullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedIntCastLeIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeDegreeNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHermUnitConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqNsmulOfActs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrderPullbackAlongHom

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_adele_unit_congruence_sequence : ∀ (p : ℕ) [Fact p.Prime] (ε ε' : AfP p), IsIntAf ε → IsIntAf ε' → ε * ε' = 1 → ∃ u : ℕ → ℤ, (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ u (n * m) - u n) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∃ β : AfP p, IsIntAf β ∧ ε = (u n : AfP p) + (n : AfP p) * β := by
  first | (exact @GlobalTheory.UnitApprox.exists_int_approx) | (exact GlobalTheory.UnitApprox.exists_int_approx) | (intros; apply GlobalTheory.UnitApprox.exists_int_approx  <;> assumption)
