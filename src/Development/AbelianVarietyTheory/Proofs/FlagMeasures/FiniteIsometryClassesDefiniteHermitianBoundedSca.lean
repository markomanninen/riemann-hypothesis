module

public import Mathlib
public import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound

@[expose] public section

open NumberField

namespace GlobalTheory

theorem hermLat_boundedScaleDual_finite {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) (d c : ℕ) (hd : 0 < d) (hc : 0 < c) :
    ∃ s : Finset (Submodule (𝓞 K) V), (∀ M₀ ∈ s, Submodule.IsLattice K M₀) ∧
      ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M →
        (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ Set.range (algebraMap (𝓞 K) K)) →
        (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M) →
        ∃ M₀ ∈ s, ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g M₀ = M := by
  classical
  let iQ : Module ℚ V := Module.compHom V (algebraMap ℚ K)
  have hQs : ∀ (q : ℚ) (x : V), q • x = (algebraMap ℚ K q) • x := fun _ _ => rfl
  have : IsScalarTower ℚ K V := ⟨fun q a x => by rw [hQs, Algebra.smul_def, mul_smul]⟩
  have : FiniteDimensional ℚ V := Module.Finite.trans K V
  let B : LinearMap.BilinForm ℚ V := LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ K (h x y))
    (fun x₁ x₂ y => by simp only [map_add (f := _), LinearMap.add_apply])
    (fun q x y => by
      simp only [hQs, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        Formalism.HermitianLatticesTheory.traceReal_star_rat,
        Formalism.HermitianLatticesTheory.traceReal_trace_smul])
    (fun x y₁ y₂ => by simp only [map_add (f := _)])
    (fun q x y => by simp only [hQs, map_smul, smul_eq_mul,
      Formalism.HermitianLatticesTheory.traceReal_trace_smul])
  have hBS : LinearMap.IsSymm B := ⟨fun x y => by
    change Algebra.trace ℚ K (h x y) = Algebra.trace ℚ K (h y x)
    rw [← hs.eq x y, Formalism.HermitianLatticesTheory.traceReal_star]⟩
  have hfull : ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M →
      (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M) →
      Submodule.IsFullLattice K M := by
    intro M hM hdual
    let : Submodule.IsLattice K M := hM
    let W : Submodule K V := Submodule.span K (M : Set V)
    let WQ : Submodule ℚ V := W.restrictScalars ℚ
    have hrestrict : (B.restrict WQ).Nondegenerate := by
      constructor
      · intro x hx
        apply Subtype.ext
        by_contra hn
        have hp := hpos (x : V) hn
        have hz := hx x
        change Algebra.trace ℚ K (h (x : V) (x : V)) = 0 at hz
        linarith
      · intro x hx
        apply Subtype.ext
        by_contra hn
        have hp := hpos (x : V) hn
        have hz := hx x
        change Algebra.trace ℚ K (h (x : V) (x : V)) = 0 at hz
        linarith
    have hortho : B.orthogonal WQ = ⊥ := by
      apply eq_bot_iff.mpr
      intro y hy
      have hyzero : ∀ x ∈ M, h x y = 0 := by
        intro x hx
        apply (traceForm_nondegenerate ℚ K).1
        intro a
        have hz := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) (star a • x)
          (show star a • x ∈ WQ from W.smul_mem _ (Submodule.subset_span hx))
        change Algebra.trace ℚ K (h (star a • x) y) = 0 at hz
        simpa only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
          starRingEnd_apply, star_star, Algebra.traceForm_apply, mul_comm] using hz
      have hcy : (c : K) • y ∈ M := hdual y (fun x hx => ⟨0, by simp [hyzero x hx]⟩)
      have hz := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) ((c : K) • y)
        (show (c : K) • y ∈ WQ from Submodule.subset_span hcy)
      change Algebra.trace ℚ K (h ((c : K) • y) y) = 0 at hz
      simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply, star_natCast] at hz
      rw [← map_natCast (algebraMap ℚ K) c, ← Algebra.smul_def, map_smul, smul_eq_mul] at hz
      have hcQ : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc)
      have hz' : Algebra.trace ℚ K (h y y) = 0 := (mul_eq_zero.mp hz).resolve_left hcQ
      have : y = 0 := by by_contra hn; have := hpos y hn; linarith
      simp [this]
    have htop : WQ = ⊤ := B.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot hBS.isRefl hrestrict hortho
    exact ⟨by apply eq_top_iff.mpr; intro x hx; exact (eq_top_iff.mp htop) (by trivial)⟩
  obtain ⟨N, ι, hι, hmul, hlat⟩ := Formalism.HermitianLatticesTheory.final_traceReal K V h hs hpos
  set e : ℤ := NumberField.discr K with he
  have he0 : e ≠ 0 := NumberField.discr_ne_zero K
  have ecast : ((e.natAbs ^ 2 : ℕ) : K) = ((e : K)) * (e : K) := by
    have h0 : ((e.natAbs ^ 2 : ℕ) : ℤ) = e * e := by rw [Nat.cast_pow, Int.natAbs_sq, sq]
    rw [← Int.cast_natCast, h0, Int.cast_mul]
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    fun r => ⟨⟨star (algebraMap (𝓞 K) K r), r.isIntegral_coe.map (starRingEnd K).toIntAlgHom⟩, rfl⟩
  let S : Set (Submodule (𝓞 K) V) := {M | Submodule.IsLattice K M ∧
    (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ Set.range (algebraMap (𝓞 K) K)) ∧
    (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M)}
  obtain ⟨s, hs1, hs2⟩ := Formalism.HermitianLatticesTheory.classSetFinite_core Formalism.HermitianLatticesTheory.final_shortVectors
    Formalism.HermitianLatticesTheory.final_finIntermediate Formalism.HermitianLatticesTheory.final_isomOfTrace h hpos N ι hι hmul d hd
    (Real.sqrt (((c * e.natAbs ^ 2 : ℕ) : ℝ) ^ N)) S
    (fun M hM x hx y hy => Submodule.mem_one.mpr (hM.2.1 x hx y hy))
    (fun M hM => hlat M (hfull M hM.1 hM.2.2))
    (by
      intro M hM _ _
      apply Formalism.HermitianLatticesTheory.genusCovolBound_covol_le h N ι hι M (c * e.natAbs ^ 2)
        (Nat.mul_pos hc (pow_pos (Int.natAbs_pos.mpr he0) 2))
      have hdual : ∀ y, (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z) →
          ∀ x ∈ M, h x ((e : K) • y) ∈ Set.range (algebraMap (𝓞 K) K) := by
        intro y hy x hx
        rw [LinearMap.map_smul, smul_eq_mul]
        have hm : ((e : ℤ) : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
          apply Formalism.HermitianLatticesTheory.genusCovolBound_discr
          intro r
          obtain ⟨s, hs'⟩ := hstar r
          obtain ⟨z, hz⟩ := hy (s • x) (M.smul_mem s hx)
          refine ⟨z, ?_⟩
          rw [← hz]
          congr 1
          rw [← algebraMap_smul K s x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
            starRingEnd_apply, hs', star_star, mul_comm]
        exact Submodule.mem_one.mp hm
      intro y y' hy hy'
      have h1 : (c : K) • ((e : K) • y) ∈ M := hM.2.2 _ (hdual y hy)
      have h2 := hdual y' hy' _ h1
      have key : h ((c : K) • ((e : K) • y)) ((e : K) • y') =
          algebraMap ℚ K ((c * e.natAbs ^ 2 : ℕ) : ℚ) * h y y' := by
        rw [map_natCast, Nat.cast_mul, ecast]
        simp only [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply, star_intCast,
          star_natCast, smul_eq_mul]
        ring
      rw [key] at h2
      obtain ⟨r, hr⟩ := h2
      obtain ⟨z, hz⟩ := Formalism.HermitianLatticesTheory.genusCovolBound_trace_int (K := K) r
      refine ⟨z, ?_⟩
      rw [← hz, hr, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul])
  exact ⟨s, fun M₀ hM₀ => (hs1 M₀ hM₀).1, fun M hL hd' hc' => hs2 M ⟨hL, hd', hc'⟩⟩

end GlobalTheory
