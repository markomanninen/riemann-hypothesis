module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneHodgeFiltrationPerfectField
public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

open GlobalTheory GlobalTheory.PDivGroup

theorem GlobalTheory.T.dieudonne_hodgeFiltration_perfectField :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
      (∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega) ∧
      (∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n) ∧
      (∀ m, G.rigToLie (GlobalTheory.Dieu.p_eq_zero p k) (T.red G m) = 0 ↔ ∃ n, m = T.V G n) ∧
      Function.Injective G.rigOfOmega :=
  @GlobalTheory.Dieu.Theory.hodge_filtration
