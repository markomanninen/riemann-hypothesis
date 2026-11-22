module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulMemMMOfEqLphiUAdd

@[expose] public section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Matrix

theorem PhiMod.mem_MM_of_series (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι) :
    ∀ (w : Vec K a ι) (t : ℕ → Vec K a ι), (∀ n, ∃ v ∈ P.MM, t n = (l : K) ^ n • v) →
      (∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow (K := K) (a := a) (ι := ι) m) → w ∈ P.MM := by
  intro w t ht hw
  choose v hv htv using ht
  have h2 (k : ℕ) : ∃ s ∈ P.MM, ∀ m, ∃ g ∈ P.MM,
      w - (s + (l : K) ^ k • g) ∈ uPow (K := K) (a := a) (ι := ι) m := by
    refine ⟨∑ n ∈ Finset.range k, t n,
      sum_mem fun n _ => (htv n) ▸ P.l_pow_smul_mem_MM n (hv n), fun m => ?_⟩
    refine ⟨∑ n ∈ Finset.range m, (l : K) ^ n • v (k + n),
      sum_mem fun n _ => P.l_pow_smul_mem_MM n (hv _), uPow_anti (Nat.le_add_left m k) ?_⟩
    have := hw (k + m)
    rw [Finset.sum_range_add] at this
    simpa only [Finset.smul_sum, smul_smul, ← pow_add, ← htv] using this
  have hext {τ : ZMod a} {v : ι → K⟦X⟧} :
      v ∈ P.extc (S O K e) τ ↔ P.mxInv τ *ᵥ v ∈ vecs ι (S O K e) := by
    have hmem {v : ι → K⟦X⟧} : v ∈ P.extc (S O K e) τ ↔
        ∃ m ∈ vecs ι (S O K e), v = P.mx τ *ᵥ m := by
      rw [PhiMod.extc, Submodule.mem_span_range_iff_exists_fun]
      have key (c : ι → S O K e) : ∑ i, c i • (P.mx τ).col i =
          P.mx τ *ᵥ fun i => (c i : K⟦X⟧) := by
        ext1 j
        simp [Matrix.mulVec, dotProduct, Subalgebra.smul_def, mul_comm]
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨_, fun i => (c i).2, key c⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨fun i => ⟨m i, hm i⟩, key _⟩
    rw [hmem]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rwa [Matrix.mulVec_mulVec, P.mxInv_mul_mx, Matrix.one_mulVec]
    · intro h
      exact ⟨_, h, by rw [Matrix.mulVec_mulVec, P.mx_mul_mxInv, Matrix.one_mulVec]⟩
  refine mem_tot.2 fun τ => hext.2 fun i => mem_S_of_approx (l := l) fun k => ?_
  obtain ⟨s, hs, H⟩ := h2 k
  refine ⟨_, hext.1 (mem_tot.1 hs τ) i, fun m => ?_⟩
  obtain ⟨g, hg, H'⟩ := H m
  refine ⟨_, hext.1 (mem_tot.1 hg τ) i, ?_⟩
  have := dvd_mulVec (P.mxInv τ) (H' τ) i
  simpa only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_smul] using this

end GlobalTheory.BK
