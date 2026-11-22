module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpecialLinearMap

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.SpecialLinearTensor.sl :
    {I : Type} →
      [Fintype I] →
        [dI : DecidableEq I] →
          {W : I → Type} →
            [inst : (i : I) → AddCommGroup (W i)] →
              [inst_1 : (i : I) → _root_.Module ℂ (W i)] →
                (v : I) → ((i : I) → Module.Dual ℂ (W i)) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] W v :=
  fun {I} _ dI {W} _ _ v f => by
    have prod_update_self (m : (i : I) → W i) (x : W v) :
        ∏ j ∈ Finset.univ.erase v, f j (Function.update m v x j) =
          ∏ j ∈ Finset.univ.erase v, f j (m j) := by
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have prod_update_ne {i : I} (h : i ≠ v) (m : (j : I) → W j) (x : W i) :
        ∏ j ∈ Finset.univ.erase v, f j (Function.update m i x j) =
          f i x * ∏ j ∈ (Finset.univ.erase v).erase i, f j (m j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨h, Finset.mem_univ i⟩),
        Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    exact PiTensorProduct.lift
      { toFun := fun m => (∏ j ∈ Finset.univ.erase v, f j (m j)) • m v
        map_update_add' := by
          intro d m i x y
          obtain rfl : d = dI := Subsingleton.elim _ _
          by_cases h : i = v
          · subst i
            simp only [prod_update_self, Function.update_self, smul_add]
          · simp only [prod_update_ne h, Function.update_of_ne (Ne.symm h),
              map_add, add_mul, add_smul]
        map_update_smul' := by
          intro d m i c x
          obtain rfl : d = dI := Subsingleton.elim _ _
          by_cases h : i = v
          · subst i
            simp only [prod_update_self, Function.update_self, RingHom.id_apply]
            exact smul_comm _ _ _
          · simp only [prod_update_ne h, Function.update_of_ne (Ne.symm h),
              RingHom.id_apply, map_smul, smul_eq_mul, mul_assoc, mul_smul] }

theorem UpperTheory.Reformulated.B.SpecialLinearTensor.sl_tprod :
    ∀ {I : Type} [inst : Fintype I] [dI : DecidableEq I] {W : I → Type} [inst_1 : (i : I) → AddCommGroup (W i)]
      [inst_2 : (i : I) → _root_.Module ℂ (W i)] (v : I) (f : (i : I) → Module.Dual ℂ (W i)) (m : (i : I) → W i),
      (UpperTheory.Reformulated.B.SpecialLinearTensor.sl v f : (PiTensorProduct ℂ fun (i : I) ↦ W i) → W v)
          ((PiTensorProduct.tprod ℂ : ((i : I) → W i) → PiTensorProduct ℂ fun (i : I) ↦ W i) m) =
        (∏ i ∈ Finset.univ.erase v, (f i : W i → ℂ) (m i)) • m v := by
  intro I _ _ W _ _ v f m
  rw [UpperTheory.Reformulated.B.SpecialLinearTensor.sl, PiTensorProduct.lift.tprod]
  rfl
