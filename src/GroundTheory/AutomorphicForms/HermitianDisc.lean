module

public import Mathlib
public import GroundTheory.AutomorphicForms.HermitianWitt
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix GroundTheory.LocalField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']

namespace HermitianForm

variable [Algebra.IsSeparable F E]

def detUnit (h : HermitianForm F E V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι E V) : Fˣ := by
  have hdet : (gram h.toSesq b).det ∈ Set.range (algebraMap F E) := by
    apply conj_eq_self_iff.1
    rw [← conjHom_apply, RingHom.map_det, RingHom.mapMatrix_apply, ← det_transpose,
      isHermitianFor_gram h b]
  exact Units.mk0 hdet.choose (by
    intro h0
    have heq := hdet.choose_spec
    rw [h0, map_zero] at heq
    exact (isUnit_det_gram h b).ne_zero heq.symm)

end HermitianForm

def diagForm {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → Fˣ) :
    HermitianForm F E (ι → E) where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E)
    (fun x y => ∑ i, conj F E (x i) * algebraMap F E (a i) * y i)
    (fun x x' y => by simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, conjHom_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
  isSymm := ⟨fun x y => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.mk₂'ₛₗ_apply, conjHom_apply, map_sum, map_mul, conj_conj,
      conj_algebraMap]
    exact Finset.sum_congr rfl fun i _ => by ring⟩
  nonsingular := by
    have ha : ∀ i, algebraMap F E (a i) ≠ 0 := fun i => by simp
    have key : ∀ (x : ι → E) (j : ι),
        (∑ i, conj F E (x i) * algebraMap F E (a i) * (Pi.single j 1 : ι → E) i) =
          conj F E (x j) * algebraMap F E (a j) := by
      intro x j
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [Pi.single_apply, hij]
      · simp
    constructor
    · intro x y hxy
      funext j
      have h1 := LinearMap.congr_fun hxy (Pi.single j 1)
      simp only [LinearMap.mk₂'ₛₗ_apply, key] at h1
      have h2 := mul_right_cancel₀ (ha j) h1
      rw [← conj_conj (F := F) (x j), h2, conj_conj]
    · intro f
      refine ⟨fun j => conj F E (f (Pi.single j 1) * (algebraMap F E (a j))⁻¹),
        LinearMap.ext fun y => ?_⟩
      simp only [LinearMap.mk₂'ₛₗ_apply, conj_conj]
      conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ f y]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : (fun j => if i = j then (1 : E) else 0) = Pi.single i 1 := by
        funext j; simp [Pi.single_apply, eq_comm]
      rw [this, smul_eq_mul]
      field_simp [ha i]

end GroundTheory.Automorphic

end
