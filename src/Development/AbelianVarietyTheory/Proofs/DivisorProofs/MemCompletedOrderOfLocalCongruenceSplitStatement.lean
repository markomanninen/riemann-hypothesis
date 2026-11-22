module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderOfLocalCongruenceSplit
public import Formalism.PairingDivisors.StatementA
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedOrder_of_local_congruence_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ c → Splits v) → ∀ z : Af E, (∀ v, LocIn (expIn c v) v z) → z ∈ hatO c := by
  first | exact @GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn | exact GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn | (intros; apply GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn <;> assumption)
