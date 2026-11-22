module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletio
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
theorem _root_.GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ ∀ v ∈ LaHat D, j • A v ∈ LaHat D := by
  first | (exact @GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem) | (exact GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem) | (intros; apply GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem  <;> assumption)
