module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDieudonneModFrobeniusDifferentials
public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p],
      ∃ θ : ∀ G : PDivGroup p k, T.M G →+ G.omega,
        ∀ G : PDivGroup p k,
          (∀ m, G.rigOfOmega (θ G m) = T.red G (T.V G m)) ∧
          Function.Surjective (θ G) ∧
          (∀ m, θ G m = 0 ↔ ∃ n, m = T.F G n) ∧
          (∀ (a : WittVector p k) m,
            θ G (WittVector.frobenius a • m) = WittVector.constantCoeff a • θ G m) ∧
          ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
            θ G (T.map f m) = omegaMap G H f (θ H m) :=
  @GlobalTheory.Dieu.theta_exists
