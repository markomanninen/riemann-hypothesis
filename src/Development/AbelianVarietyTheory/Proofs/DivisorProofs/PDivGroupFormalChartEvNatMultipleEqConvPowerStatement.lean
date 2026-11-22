module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPower
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct WithConv Coalgebra

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
      [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
      ∀ (G : GlobalTheory.PDivGroup p O) (d : ℕ) (c : GlobalTheory.QLog.Chart G d)
        (n k : ℕ) (i : Fin d),
        c.ev n (nmul c.μ k i) = PDiv.mulBy (R := O) (A := G.A n) k (c.x n i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n k
  have : IsAdicComplete (Ideal.span {(p : O)}) (G.A n) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  have : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) :=
    GlobalTheory.NMul.isAdicComplete_ring_of_module (O := O) p
  have heval := ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural
    p O (G.A n) (Fin d) (c.x n) (c.nil n)).2 (c.ev n) (c.isEval n)).1
  have hsucc (k : ℕ) (i : Fin d) : nmul c.μ (k + 1) i =
      subst (Sum.elim (nmul c.μ k) fun j => (X j : MvPowerSeries (Fin d) O)) (c.μ i) := by
    rw [nmul, Function.iterate_succ_apply']
    rfl
  have hconstant (k : ℕ) (i : Fin d) : constantCoeff (nmul c.μ k i) = 0 := by
    induction k generalizing i with
    | zero => rfl
    | succ k ih =>
      rw [hsucc]
      have hzero : ∀ j, constantCoeff
          (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) = 0 := by
        rintro (j | j)
        · exact ih j
        · exact constantCoeff_X j
      exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hzero) hzero
        (c.isLaw.const i)
  have hmul (k : ℕ) : (PDiv.mulBy (R := O) (A := G.A n) k : G.A n →ₐ[O] G.A n) =
      (toConv (AlgHom.id O (G.A n)) ^ k).ofConv :=
    PDiv.comp_mulBy_pts (AlgHom.id O (G.A n)) k
  induction k with
  | zero =>
    intro i
    have hzero : nmul c.μ 0 i = 0 := rfl
    change c.ev n (nmul c.μ 0 i) =
      (PDiv.mulBy (R := O) (A := G.A n) 0 : G.A n →ₐ[O] G.A n) (c.x n i)
    rw [hzero, map_zero, hmul]
    simp [c.aug n i]
  | succ k ih =>
    intro i
    let u := Sum.elim (nmul c.μ k) fun j => (X j : MvPowerSeries (Fin d) O)
    let lift : G.A n ⊗[O] G.A n →ₐ[O] G.A n :=
      Algebra.TensorProduct.lift (PDiv.mulBy (R := O) (A := G.A n) k : G.A n →ₐ[O] G.A n)
        (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _
    have hu : ∀ j, constantCoeff (u j) = 0 := by
      rintro (j | j)
      · exact hconstant k j
      · exact constantCoeff_X j
    have hlift : IsEval p (fun j => c.ev n (u j)) (lift.comp (c.ev₂ n)) := by
      constructor
      · rintro (j | j)
        · simp only [lift, u, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inl j), Sum.elim_inl,
            Algebra.TensorProduct.lift_tmul, map_one, mul_one]
          exact (ih j).symm
        · simp only [lift, u, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inr j), Sum.elim_inr,
            Algebra.TensorProduct.lift_tmul, map_one, one_mul, (c.isEval n).1 j]
          rfl
      · intro m
        obtain ⟨N, hN⟩ := (c.isEval₂ n).2 m
        refine ⟨N, fun f hf => ?_⟩
        simpa only [AlgHom.comp_apply, map_pow, map_natCast] using map_dvd lift (hN f hf)
    rw [hsucc, heval _ u _ hu hlift, AlgHom.comp_apply, c.comul n i]
    change lift (comul (R := O) (c.x n i)) =
      (PDiv.mulBy (R := O) (A := G.A n) (k + 1) : G.A n →ₐ[O] G.A n) (c.x n i)
    rw [hmul, pow_succ, AlgHom.convMul_apply]
    simp only [lift, hmul]
