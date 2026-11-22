module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceStabilizerTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply

@[expose] public section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_stabilizer_trivial : ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a d : ℕ) (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k),
    Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1 := by
  rintro k _ _ _ _ a d Z g ⟨J, hJ, hZ⟩ ⟨J', hJ', hgZ⟩
  have hminor : minor Z J = 1 := by rw [minor, hJ, det_one]
  have hminor' : minor (g.val * Z) J' = 1 := by rw [minor, hJ', det_one]
  have hproduct : valuation k (g.val.det) * valuation k (minor Z J') = 1 := by
    rw [← map_mul, ← minor_mul, hminor', map_one]
  have hdet_le : valuation k (g.val.det) ≤ 1 := by
    have h := (hgZ J).1
    rwa [minor_mul, hminor, mul_one] at h
  have hslice : valuation k (minor Z J') = 1 := by
    refine le_antisymm (hZ J').1 ?_
    calc
      (1 : ValueGroupWithZero k) = valuation k (g.val.det) * valuation k (minor Z J') :=
        hproduct.symm
      _ ≤ 1 * valuation k (minor Z J') := mul_le_mul_of_nonneg_right hdet_le zero_le
      _ = valuation k (minor Z J') := one_mul _
  have hdet : valuation k (g.val.det) = 1 := by rwa [hslice, mul_one] at hproduct
  have hindices : J = J' := by
    rcases lt_trichotomy (idx J') (idx J) with h | h | h
    · exact absurd ((hZ J').2 h) (by rw [hslice]; exact lt_irrefl _)
    · exact (idx.injective h).symm
    · have hlt := (hgZ J).2 h
      rw [minor_mul, hminor, mul_one, hdet] at hlt
      exact absurd hlt (lt_irrefl _)
  subst J'
  have hsub : (g.val * Z).submatrix id J = g.val * Z.submatrix id J := by
    ext i j
    simp [Matrix.mul_apply, submatrix_apply]
  rw [hsub, hJ, Matrix.mul_one] at hJ'
  exact Units.ext hJ'
