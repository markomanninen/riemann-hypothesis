module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneTheoryVEqVerschiebungInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
      Function.Injective (T.F G) ∧ Function.Injective (T.V G) ∧
      (∀ m, T.smap (frobProj (p_eq_zero p k) G) (T.V G m) =
        T.map (verschiebung (p_eq_zero p k) G) m) ∧
      (∀ (H : PDivGroup p k) (φ : T.M H →ₗ[WittVector p k] T.M G),
        (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m)) ∧
      ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
        T.map f (T.V H m) = T.V G (T.map f m) :=
  @GlobalTheory.Dieu.theory_V_verschiebung
