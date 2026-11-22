module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRootStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubmoduleEqSpanOfPowEqSpanPow

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.Capit

theorem coeSubmodule_pow {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (I : Ideal R) (k : ℕ) :
    IsLocalization.coeSubmodule K (I ^ k) = IsLocalization.coeSubmodule K I ^ k := by
  induction k with
  | zero => simp [IsLocalization.coeSubmodule_top]
  | succ k ih => rw [pow_succ, pow_succ, IsLocalization.coeSubmodule_mul, ih]

variable {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ)

def intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) : 𝓞 E →+* 𝓞 F :=
  RingOfIntegers.mapRingHom (φ.codRestrict F h)

theorem coe_intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) (a : 𝓞 E) :
    ((intMap φ F h a : F) : ℂ) = φ (a : E) := rfl

theorem intMap_injective (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) :
    Function.Injective (intMap φ F h) := by
  intro a b hab
  have h1 : φ (a : E) = φ (b : E) := by rw [← coe_intMap φ F h, ← coe_intMap φ F h, hab]
  exact RingOfIntegers.ext (φ.injective h1)

def intIncl {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) : 𝓞 F →+* 𝓞 K :=
  RingOfIntegers.mapRingHom (IntermediateField.inclusion hFK).toRingHom

theorem map_intMap {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) (h : ∀ x, φ x ∈ F) (I : Ideal (𝓞 E)) :
    I.map (intMap φ K fun x => hFK (h x)) = (I.map (intMap φ F h)).map (intIncl hFK) := by
  rw [Ideal.map_map]; rfl

theorem sz_mono' {F : IntermediateField ℚ ℂ} {a b a' b' : ℝ} (h : Sz F a b) (ha : a ≤ a') (hb : b ≤ b') :
    Sz F a' b' := by
  obtain ⟨i, h1, h2⟩ := h
  exact ⟨i, h1.trans ha, h2.trans hb⟩

theorem step (F : IntermediateField ℚ ℂ) (a b : ℝ) (hF : Sz F a b) (h : ∀ x, φ x ∈ F) (k : ℕ) (hk : 0 < k)
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hp : ((I ^ k).map (intMap φ F h)).IsPrincipal) :
    ∃ (K : IntermediateField ℚ ℂ) (hFK : F ≤ K), Sz K (a + Real.log k) (b + Real.log k) ∧
      (I.map (intMap φ K fun x => hFK (h x))).IsPrincipal := by
  obtain ⟨y, hy⟩ := hp
  have hy' : (I ^ k).map (intMap φ F h) = Ideal.span {y} := hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero, Ideal.map_eq_bot_iff_of_injective (intMap_injective φ F h)] at hy'
    exact pow_ne_zero k hI hy'
  have hyF : (y : F) ≠ 0 := fun h0 => hy0 (RingOfIntegers.ext h0)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((y : F) : ℂ) hk
  have hS := GlobalTheory.T.field_size_adjoin_kth_root F a b k (y : F) (IsLocalization.coeSubmodule F (I.map (intMap φ F h))) z hF hk hyF
    (by rw [← coeSubmodule_pow, ← Ideal.map_pow, hy', IsLocalization.coeSubmodule_span_singleton]) hz
  have hzK : z ∈ F ⊔ ℚ⟮z⟯ := (le_sup_right : ℚ⟮z⟯ ≤ F ⊔ ℚ⟮z⟯) (IntermediateField.mem_adjoin_simple_self ℚ z)
  have hFK : F ≤ F ⊔ ℚ⟮z⟯ := le_sup_left
  generalize F ⊔ ℚ⟮z⟯ = K at hS hzK hFK
  refine ⟨K, hFK, hS, ?_⟩
  haveI := finiteDimensional_of_sz hS
  haveI : NumberField K := NumberField.mk
  rw [← IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) K]
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hz
    exact hyF (by exact_mod_cast hz.symm)
  refine ⟨⟨z, hzK⟩, GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ ⟨z, hzK⟩ k hk
    (fun h0 => hz0 (congrArg Subtype.val h0)) ?_ ?_⟩
  · exact (IsLocalization.coeSubmodule_fg K (RingOfIntegers.coe_injective) _).mpr (IsNoetherian.noetherian _)
  · rw [← coeSubmodule_pow, ← Ideal.map_pow, map_intMap φ hFK h, hy', Ideal.map_span, Set.image_singleton,
      IsLocalization.coeSubmodule_span_singleton]
    congr 2
    apply Subtype.ext
    exact hz.symm

end GlobalTheory.FieldSize.Capit

namespace GlobalTheory.FieldSize


end GlobalTheory.FieldSize
