module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalRationalTranslate

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

theorem mem_unipRad_iff_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u : GAd σ J, u ∈ unipRad σ J C ↔ ((matHom _ σ J u).1 * adMat F C = adMat F C ∧ ∃ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (matHom _ σ J u).1 * adMat F Z = adMat F Z + adMat F C * b) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ fr u
  have hmap : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin c) E),
      adMat F (X * Y) = adMat F X * adMat F Y := fun X Y => by
    simp only [adMat]; exact Matrix.map_mul
  have hsub : adMat F ((1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J)) =
      adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) := by
    have e : (1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J) =
        C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) := by
      rw [← fr.sum]; abel
    rw [e, ← hmap, ← hmap]
    simp only [adMat]; exact Matrix.map_add _ (map_add _) _ _
  have hZ : ((1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J)) * Z = Z := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, fr.cz, Matrix.mul_zero, sub_zero]
  have hdual : u ∈ unipRad σ J C ↔ ((matHom _ σ J u).1 - 1) * adMat F C = 0 ∧
      ∃ B : Matrix (Fin j) (Fin n) (AF F ⊗[F] E),
        ((matHom _ σ J u).1 - 1) * adMat F (1 - D * (cT (σ : E →+* E) C * J)) = adMat F C * B := by
    constructor
    · intro hg
      simp only [Matrix.sub_mul _ (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Matrix.one_mul,
        sub_eq_iff_eq_add, zero_add]
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨h1, -, h3⟩ := hg
        rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
        have hT : cT (σ : E →+* E) C * J * (1 - D * (cT (σ : E →+* E) C * J)) = 0 := by
          rw [Matrix.mul_sub, ← Matrix.mul_assoc _ D, fr.cd, Matrix.mul_one, Matrix.one_mul, sub_self]
        choose a ha using fun k => h3 (fun j => (1 - D * (cT (σ : E →+* E) C * J) : Matrix (Fin n) (Fin n) E) j k)
          (funext fun j => congrFun (congrFun hT j) k)
        refine ⟨h1, Matrix.of fun i k => a k i, ?_⟩
        rw [← sub_eq_iff_eq_add, ← Matrix.one_mul (adMat F (1 - _)), ← Matrix.mul_assoc, Matrix.mul_one, ← Matrix.sub_mul]
        ext i k
        exact congrFun (ha k) i
      | one => exact ⟨by simp, 0, by simp⟩
      | mul a b _ _ ha hb =>
        obtain ⟨a1, A, a2⟩ := ha
        obtain ⟨b1, B, b2⟩ := hb
        refine ⟨by rw [map_mul, Units.val_mul, Matrix.mul_assoc, b1, a1], B + A, ?_⟩
        rw [map_mul, Units.val_mul, Matrix.mul_assoc, b2, Matrix.mul_add, ← Matrix.mul_assoc, a1, a2, Matrix.mul_add,
          add_assoc]
      | inv a _ ha =>
        obtain ⟨a1, A, a2⟩ := ha
        have i1 : (matHom _ σ J a⁻¹).1 * adMat F C = adMat F C := by
          conv_lhs => rw [← a1]
          rw [map_inv, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        refine ⟨i1, -A, ?_⟩
        have := congrArg ((matHom _ σ J a⁻¹).1 * ·) a2
        rw [Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), i1, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul,
          inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at this
        rw [Matrix.mul_neg]
        conv_rhs => rw [this]
        abel
    · rintro ⟨h1, B, h2⟩
      refine Subgroup.subset_closure ⟨h1, ?_, fun x hx => ⟨B *ᵥ fun i => inclR (F := F) (AF F) (x i), ?_⟩⟩
      · have hg : cT (sigR (AF F) σ) (matHom _ σ J u).1 * adMat F J * (matHom _ σ J u).1 = adMat F J := u.2
        have c1 : cT (sigR (AF F) σ) (adMat F C) = adMat F (cT (σ : E →+* E) C) := rfl
        rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
        rw [adMat, Matrix.map_mul, ← adMat, ← c1, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
        conv_lhs => rw [← h1, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ (matHom _ σ J u).1)]
        exact congrArg _ hg
      · have e : adMat F (1 - D * (cT (σ : E →+* E) C * J)) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) =
            fun i => inclR (F := F) (AF F) (x i) := by
          funext i
          have := RingHom.map_mulVec (inclR (F := F) (AF F)) (1 - D * (cT (σ : E →+* E) C * J)) x i
          rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero, Matrix.one_mulVec] at this
          exact this.symm
        rw [Matrix.mulVec_mulVec, ← h2, ← Matrix.mulVec_mulVec, e]
  rw [hdual]
  set M := (matHom _ σ J u).1
  constructor
  · rintro ⟨h1, B, h2⟩
    refine ⟨by rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1; exact h1, B * adMat F Z, ?_⟩
    have := congrArg (· * adMat F Z) h2
    rw [Matrix.mul_assoc, ← hmap, hZ, Matrix.mul_assoc] at this
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add] at this
    rw [this, add_comm]
  · rintro ⟨h1, b, h2⟩
    refine ⟨by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self], b * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)), ?_⟩
    have h1' : (M - 1) * adMat F C = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self]
    have h2' : (M - 1) * adMat F Z = adMat F C * b := by rw [Matrix.sub_mul, Matrix.one_mul, h2]; abel
    rw [hsub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1', h2', Matrix.zero_mul, zero_add, Matrix.mul_assoc]

end GlobalTheory.SphEis
