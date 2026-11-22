module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.ModCore

@[expose] public section

open MeasureTheory Matrix Topology
open scoped ENNReal NNReal

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI ModW ModW.MG

open scoped Classical in
open Classical in
def modFun {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) (hG : IsMatGroup G)
    (g : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  if h : g ∈ G then (Measure.modularCharacterFun (mk hG g h) : ℝ) else 1

theorem exists_modular_function : ModExists := by
  intro m G hG
  refine ⟨modFun G hG, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro g hg
    simp only [modFun, dite_eq_left hg]
    exact_mod_cast Measure.modularCharacterFun_pos (mk hG g hg)
  ·
    intro a ha b hb
    have hab : a * b ∈ G := hG.2.2.1 a ha b hb
    simp only [modFun, dite_eq_left ha, dite_eq_left hb, dite_eq_left hab]
    have hmk : mk hG (a * b) hab = mk hG a ha * mk hG b hb := by
      apply toM_injective
      simp only [toM_mk, toM_mul]
    rw [hmk]
    have h := (Measure.modularCharacter (G := MG G hG)).map_mul (mk hG a ha) (mk hG b hb)
    exact_mod_cast h
  ·
    intro c hc hcG g hg
    have hcg : c * g * c⁻¹ ∈ G := (hcG g).2 hg
    simp only [modFun, dite_eq_left hg, dite_eq_left hcg]
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    have hConj : ∃ φ : MG G hG ≃ₜ* MG G hG,
        ∀ x, (φ x).toM = c * x.toM * c⁻¹ := by
      refine ⟨{
        toFun := fun x => mk hG (c * x.toM * c⁻¹) ((hcG _).2 x.toM_mem)
        invFun := fun x => mk hG (c⁻¹ * x.toM * c) (by
          apply (hcG _).1
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
            Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
          exact x.toM_mem)
        left_inv := fun x => by
          apply toM_injective
          simp only [toM_mk]
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd,
            Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
        right_inv := fun x => by
          apply toM_injective
          simp only [toM_mk]
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
            Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
        map_mul' := fun x y => by
          apply toM_injective
          simp only [toM_mk, toM_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc c⁻¹ c, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
        continuous_toFun := by
          rw [continuous_iff_toM]
          simp only [toM_mk]
          exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const
        continuous_invFun := by
          rw [continuous_iff_toM]
          simp only [toM_mk]
          exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const
      }, fun x => toM_mk _ ((hcG _).2 x.toM_mem)⟩
    obtain ⟨φ, hφ⟩ := hConj
    have hmk : mk hG (c * g * c⁻¹) hcg = φ (mk hG g hg) := by
      apply toM_injective
      simp only [hφ, toM_mk]
    rw [hmk, modF_conj]
  ·
    intro V hVG hV
    have hK : IsCompact ((fun y : MtM m => Matrix.of y) ⁻¹' V) := hV
    have hW : IsCompact ((val : MG G hG → MtM m) ⁻¹' ((fun y : MtM m => Matrix.of y) ⁻¹' V)) :=
      isClosedEmbedding_val.isCompact_preimage hK
    obtain ⟨M, hM⟩ := modF_bdd _ hW
    refine ⟨M, fun v hv => ?_⟩
    have hvG : v ∈ G := hVG hv
    simp only [modFun, dite_eq_left hvG]
    apply hM
    show Matrix.of (mk hG v hvG).1 ∈ V
    exact hv
  ·
    intro h1 μ hμ
    refine rightInv_of (hG := hG) μ hμ (fun g => ?_)
    have hg := h1 g.toM g.toM_mem
    simp only [modFun, dite_eq_left g.toM_mem, mk_toM] at hg
    exact_mod_cast hg

end PI.QuotSetU.UnitaryGroupMassFormula
