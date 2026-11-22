module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomImageXDeltaZeroLiftsUniformizer
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinHom_image_X_delta_zero_lifts_uniformizer :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K))
      (g : Hom bk.prism C), C.D.δ (BK.hf (bk := bk) g X) = 0 ∧
      Ideal.Quotient.mk C.I (BK.hf (bk := bk) g X) = C.str (bk.str.symm (Ideal.Quotient.mk _ X)) := by
  intro l _ K bk C g
  have hδX : (deltaS l bk.a).δ (X : bk.S) = 0 := by
    have h := (deltaS l bk.a).φ_eq (X : bk.S)
    have hφ : (deltaS l bk.a).φ (X : bk.S) = X ^ l := frobS_X l bk.a
    rw [hφ] at h
    have hmul : (l : bk.S) * (deltaS l bk.a).δ X = 0 := by linear_combination -h
    exact (mul_eq_zero.1 hmul).resolve_left (l_ne_zero l bk.a)
  refine ⟨?_, ?_⟩
  · have h := g.f_δ (X : bk.S)
    change C.D.δ (g.f X) = 0
    rw [← h]
    change g.f ((deltaS l bk.a).δ X) = 0
    rw [hδX]
    exact g.f.map_zero
  · refine g.f_str (bk.str.symm (Ideal.Quotient.mk _ X)) X ?_
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str (bk.str.symm (Ideal.Quotient.mk _ X))
    rw [RingEquiv.apply_symm_apply]
