module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetOfContainsRayFi
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weberInvariantTorsionValues_subset_of_containsRayField : ∀ (K L : IntermediateField ℚ ℂ) [NumberField K] [NumberField L] [_root_.NumberField.IsTotallyComplex K] (h : K ≤ L), Module.finrank ℚ K = 2 → discr K < -4 → ∀ P : PeriodPair, (∀ z, z ∈ P.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion h).toRingHom n → weberSet P n ⊆ L := by
  first | exact @GlobalTheory.FieldSize.WeberIn.weberSet_subset | exact GlobalTheory.FieldSize.WeberIn.weberSet_subset | (intros; apply GlobalTheory.FieldSize.WeberIn.weberSet_subset <;> assumption)
