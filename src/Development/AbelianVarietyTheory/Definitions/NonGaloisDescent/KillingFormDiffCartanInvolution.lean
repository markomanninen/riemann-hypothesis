module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.QuotIntegrableIffCutoff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemCentIffTwConj

@[expose] public section

open Matrix MeasureTheory Topology
open scoped Kronecker ContDiff

noncomputable section

namespace GlobalTheory.Tw

section Alg
variable {a b : ℕ} {R : Type} [CommRing R] [StarRing R]

end Alg

variable {a b : ℕ}

theorem isCompact_unitary_GL (n : ℕ) : IsCompact {k : GL (Fin n) ℂ | k.val ∈ unitaryGroup (Fin n) ℂ} := by
  have hU : IsCompact (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    have hcl : IsClosed (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
      have e : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
          (fun A : Matrix (Fin n) (Fin n) ℂ => A * star A) ⁻¹' {1} := by
        ext A; exact Matrix.mem_unitaryGroup_iff
      rw [e]
      exact isClosed_singleton.preimage (continuous_id.mul continuous_star)
    have hbd : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ⊆
        Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 1 := by
      intro A hA i _ j _
      have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hA) i) i
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
      simp only [Matrix.star_apply, Complex.star_def, Complex.mul_conj] at h
      have h2 : ∑ k, Complex.normSq (A i k) = 1 := by exact_mod_cast h
      have h3 : Complex.normSq (A i j) ≤ 1 :=
        h2 ▸ Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (A i k)) (Finset.mem_univ j)
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [Complex.normSq_eq_norm_sq] at h3
      nlinarith [norm_nonneg (A i j)]
    exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1).of_isClosed_subset hcl hbd
  have : CompactSpace (unitaryGroup (Fin n) ℂ) := isCompact_iff_compactSpace.1 hU
  let φ : unitaryGroup (Fin n) ℂ → GL (Fin n) ℂ := fun u =>
    ⟨u.1, star u.1, Unitary.mul_star_self_of_mem u.2, Unitary.star_mul_self_of_mem u.2⟩
  have hφ : Continuous φ :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  have hr : Set.range φ = {k : GL (Fin n) ℂ | k.val ∈ unitaryGroup (Fin n) ℂ} := by
    ext k
    constructor
    · rintro ⟨u, rfl⟩
      exact u.2
    · intro hk
      exact ⟨⟨k.val, hk⟩, Units.ext rfl⟩
  rw [← hr]
  exact isCompact_range hφ

end GlobalTheory.Tw
