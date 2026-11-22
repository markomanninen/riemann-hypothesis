module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace Tw.SchrLoc
open _root_.GlobalTheory

open GlobalTheory.VacAny

theorem eq_atPlace_of_at {F : Type} [Field F] [NumberField F] {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {z : AF F}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z) :
    z = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v z) := by
  have h1 := hz (1 - GlobalTheory.EmbChart.atPlace v 1)
    (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
  conv_lhs => rw [h1]
  rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul]

theorem schr_tens_of_at : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 i)) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 i)) → ∀ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ),
    (∀ x z : κ → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z → r (x + z) = r x) →
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) φ r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v)
        (GlobalTheory.WeilM.schr (GlobalTheory.VacAny.psiV ψ v) (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i), fun i => GlobalTheory.AdelicU.evFin F v (w.2 i)) φ) r := by
  intro F _ _ ψ v κ _ w h1 h2 φ r hr
  funext x
  have hr' : r (x + w.1) = r x := hr x w.1 (fun u hu => funext fun i => h1 i u hu)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) :=
    fun u hu => by
      simp only [smul_eq_mul, mul_add, dotProduct, Finset.mul_sum]
      have hzero (i : κ) : u * w.2 i = 0 := h2 i u hu
      suffices (∑ i, u * (x i * w.2 i)) = 0 ∧
          (∑ i, u * (⅟(2 : AF F) * (w.1 i * w.2 i))) = 0 by
        rw [this.1, this.2, add_zero]
      constructor <;> apply Finset.sum_eq_zero <;> intro i hi
      · calc
          u * (x i * w.2 i) = x i * (u * w.2 i) := by ring
          _ = 0 := by rw [hzero, mul_zero]
      · calc
          u * (⅟(2 : AF F) * (w.1 i * w.2 i)) = (⅟(2 : AF F) * w.1 i) * (u * w.2 i) := by ring
          _ = 0 := by rw [hzero, mul_zero]
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  rw [hr', eq_atPlace_of_at hz, ← psiV_apply]
  have hinv : GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    have h : GlobalTheory.AdelicU.evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
    rwa [map_mul, map_ofNat] at h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_add (f := _), map_mul, map_sum, hinv, Pi.add_apply]
  simp only [mul_comm (⅟(2 : Fv F v))]
  rw [show (fun i => GlobalTheory.AdelicU.evFin F v (x i) + GlobalTheory.AdelicU.evFin F v (w.1 i)) =
    (fun i => GlobalTheory.AdelicU.evFin F v (x i)) + (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i)) from rfl]
  ring

end Tw.SchrLoc
