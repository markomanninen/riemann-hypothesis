module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIdeleModuleExistsRat
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteIdele_module_exists_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := by
  first | exact @GlobalTheory.CMVal.ModFRat.modF_rat | exact GlobalTheory.CMVal.ModFRat.modF_rat | (intros; apply GlobalTheory.CMVal.ModFRat.modF_rat <;> assumption)
