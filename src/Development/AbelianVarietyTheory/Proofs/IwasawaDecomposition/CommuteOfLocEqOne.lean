module

public import Mathlib
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCompAtEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealAdd

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.SplitLocComm

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem map_compAt_eq_one {n : ℕ} (s : SplitPlace L) (x : GA L n) (hx : s.loc n x = 1) :
    (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = 1 := by
  have hx' : s.loc n x⁻¹ = 1 := by rw [map_inv, hx, inv_one]
  ext i j
  have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
    have hm := x.2
    simp only [GA, UGroup, Subgroup.mem_mk] at hm
    have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
      Units.inv_eq_of_mul_eq_one_right hm
    simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]
  have hz : compAt L s.v ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = 0 := by
    have exists_imag : ∃ θ : L, θ ≠ 0 ∧ IsCMField.complexConj L θ = -θ := by
      have h := IsCMField.complexConj_ne_one L
      obtain ⟨x, hx⟩ : ∃ x : L, IsCMField.complexConj L x ≠ x := by
        by_contra hc
        push Not at hc
        exact h (AlgEquiv.ext hc)
      refine ⟨x - IsCMField.complexConj L x, sub_ne_zero.mpr hx.symm, ?_⟩
      rw [map_sub, IsCMField.complexConj_apply_apply]; ring
    have exists_real_add (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (x : L) :
        ∃ a b : maximalRealSubfield L, x = a • (1 : L) + b • θ := by
      have h2 : IsCMField.complexConj L (2 : L) = 2 := map_ofNat _ 2
      have ha : (x + IsCMField.complexConj L x) / 2 ∈ maximalRealSubfield L := by
        rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, h2]
        ring
      have hb : (x - IsCMField.complexConj L x) / (2 * θ) ∈ maximalRealSubfield L := by
        rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul,
          IsCMField.complexConj_apply_apply, h2, hθ]
        field_simp
        ring
      refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
      change x = (x + IsCMField.complexConj L x) / 2 * 1 + (x - IsCMField.complexConj L x) / (2 * θ) * θ
      field_simp
      ring
    have exists_tmul_add (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (z : AL L) :
        ∃ a b : AFplus L, z = (1 : L) ⊗ₜ[maximalRealSubfield L] a + θ ⊗ₜ[maximalRealSubfield L] b := by
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, 0, by simp⟩
      | tmul x c =>
        obtain ⟨a, b, rfl⟩ := exists_real_add θ h0 hθ x
        exact ⟨a • c, b • c, by rw [TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul]⟩
      | add x y hx hy =>
        obtain ⟨a, b, rfl⟩ := hx
        obtain ⟨a', b', rfl⟩ := hy
        exact ⟨a + a', b + b', by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel⟩
    have compAt_eq_zero (z : AL L) (h1 : s.proj z = 0) (h2 : s.proj (conjAL L z) = 0) : compAt L s.v z = 0 := by
      obtain ⟨θ, h0, hθ⟩ := exists_imag
      obtain ⟨a, b, rfl⟩ := exists_tmul_add θ h0 hθ z
      have e1 : evalAt L s.v a + s.i θ * evalAt L s.v b = 0 := by
        simpa [SplitPlace.proj] using h1
      have e2 : evalAt L s.v a - s.i θ * evalAt L s.v b = 0 := by
        simpa [SplitPlace.proj, conjAL, hθ, TensorProduct.neg_tmul, sub_eq_add_neg] using h2
      have hi : s.i θ ≠ 0 := (map_ne_zero s.i).mpr h0
      have : CharZero (s.v.adicCompletion (maximalRealSubfield L)) := algebraRat.charZero _
      have ha : evalAt L s.v a = 0 := by linear_combination (e1 + e2) / 2
      have hb : evalAt L s.v b = 0 := by
        rw [ha, zero_add] at e1
        exact (mul_eq_zero.mp e1).resolve_left hi
      simp [compAt, ha, hb]
    apply compAt_eq_zero
    · have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := rfl
      rw [map_sub, e1, hx]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i := rfl
      rw [map_sub, map_sub, hconj, e1, hx']
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, eq_comm]
  rw [map_sub, sub_eq_zero] at hz
  rw [Matrix.map_apply, hz]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem commute_of_loc_eq_one : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (x y : GAf L n), s.loc n x = 1 → TrivOutside {s.v} y → Commute x y := by
  intro L _ _ _ n s x y hx hy
  refine Subtype.ext (Units.ext ?_)
  change (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) =
    (y.1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L))
  ext i j
  rw [← sub_eq_zero]
  refine GlobalTheory.AdelicComp.eq_zero_of_compAt_eq_zero L _ fun w => ?_
  have h : ((x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L w) =
      ((y.1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L w) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    by_cases hw : w = s.v
    · subst hw
      rw [map_compAt_eq_one s x hx, one_mul, mul_one]
    · rw [hy w (by simpa using hw), one_mul, mul_one]
  rw [map_sub, sub_eq_zero]
  exact congrFun (congrFun h i) j

end GlobalTheory.SplitLocComm
