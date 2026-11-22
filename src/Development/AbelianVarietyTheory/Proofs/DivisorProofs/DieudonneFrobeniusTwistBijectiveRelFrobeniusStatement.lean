module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFrobeniusTwistBijectiveRelFrobenius
public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

open GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius :
    ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p fun _ _ _ => True)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k),
      Function.Bijective (B.smap trivial trivial (frobProj (p_eq_zero p k) G)) ∧
      (∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G)
        (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m) ∧
      ∀ m n, B.smap trivial trivial (frobProj (p_eq_zero p k) G) n =
        B.map trivial trivial (verschiebung (p_eq_zero p k) G) m →
        B.F G trivial n = p • m :=
  @GlobalTheory.Dieu.frobTwist_module
