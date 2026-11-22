module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSelfDualClassesRootDiscr

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory

namespace DecoLatticeClasses

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

noncomputable def unitEquiv (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    Sp E n ≃ₗ[E] Sp E n :=
  LinearEquiv.ofLinearMap (Matrix.mulVecLin γ.conjTranspose) (Matrix.mulVecLin γ)
    (by rw [← Matrix.mulVecLin_mul, mul_eq_one_comm.1 h, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_one])

theorem unitEquiv_mem (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    unitEquiv γ h ∈ UF E n := by
  intro x y
  change star (γ.conjTranspose.mulVec x) ⬝ᵥ (γ.conjTranspose.mulVec y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem mem_one_iff [NumberField E] (a : E) :
    a ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ a := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨r, rfl⟩
    exact r.isIntegral_coe
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

end DecoLatticeClasses


open DecoLatticeClasses in
theorem exists_finset_decoSet_lattice_reps :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing E],
    (∀ x : E, star x = IsCMField.complexConj E x) → ∀ n : ℕ,
    ∃ Rs : Finset (Submodule (𝓞 E) (Sp E n)),
      (Rs.card : ℝ) ≤ (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^
          (3 * Module.finrank ℚ E * n ^ 2) ∧
      ∀ (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)),
        ∃ g : UF E n,
          (((g, (1 : GLG (E := E) (n := n) (SG := SG))) • d :
            DecoSet (E := E) (n := n) (ST := ST) (SG := SG))).1.N ∈ Rs := by
  intro E _ _ _ _ hs n
  obtain ⟨R, hR, H⟩ := GlobalTheory.exists_finset_selfDual_classes_rootDiscr E n
  refine ⟨R, hR, fun ST SG d => ?_⟩
  have hu : Formalism.HermitianLatticesTheory.dual (hStd E n) d.1.N = d.1.N := d.2.uni
  have hspan : Submodule.span E (d.1.N : Set (Sp E n)) = ⊤ := by
    let W := Submodule.span E (d.1.N : Set (Sp E n))
    change W = ⊤
    by_contra hW
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let g : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    -- Self-duality puts the whole line through the orthogonal vector in the lattice.
    have hsmul (a : E) : a • e x ∈ d.1.N := by
      rw [← hu, mem_dual]
      intro y hy
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩)
          (LinearMap.mem_ker.mp hx)
      rw [map_smul, hStd_isSymm.isRefl (e x) y hxy, smul_zero]
      exact Submodule.zero_mem _
    let i : E →ₗ[𝓞 E] d.1.N :=
      ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict d.1.N hsmul
    let : Module.Finite (𝓞 E) d.1.N := Module.Finite.iff_fg.mpr d.2.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := H d.1.N d.2.lat.fg hspan (fun y => by
    conv_lhs => rw [← hu, mem_dual]
    simp only [mem_one_iff, hStd_apply, hs])
  have hγ' : γ * γ.conjTranspose = 1 := by
    rw [← hγ]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply, hs]
  refine ⟨⟨unitEquiv γ hγ', unitEquiv_mem γ hγ'⟩, ?_⟩
  have e : Formalism.HermitianLatticesTheory.gmap (unitEquiv γ hγ') d.1.N = L₀ := by
    ext x
    rw [mem_gmap, hm]
    rfl
  rw [← e] at hL₀
  exact hL₀

end GlobalTheory
