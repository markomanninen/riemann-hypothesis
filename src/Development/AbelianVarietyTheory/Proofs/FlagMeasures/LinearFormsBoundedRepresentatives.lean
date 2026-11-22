module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRetractionOfProjective
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFramesPerpendicularVectors

@[expose] public section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.FunIdx

section Gen

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_retraction (M0 L : Submodule (𝓞 E) V) (hL : L.FG) (h : IsPrimitiveSub M0 L) :
    ∃ r : L →ₗ[𝓞 E] M0, ∀ x : M0, r ⟨x, h.1 x.2⟩ = x := by
  exact _root_.GlobalTheory.ProjectiveRetraction.exists_retraction M0 L hL h

theorem exists_extend_fun (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤)
    (ψ : L →ₗ[𝓞 E] 𝓞 E) : ∃ φ : V →ₗ[E] E, ∀ x : L, φ x = (ψ x : E) := by
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 E)) L.subtype := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      rw [Module.End.isUnit_iff]
      have ha0 : ((a : 𝓞 E) : E) ≠ 0 := by
        have := nonZeroDivisors.ne_zero a.2
        exact_mod_cast this
      have e : ⇑(algebraMap (𝓞 E) (Module.End (𝓞 E) V) a) = fun v => ((a : 𝓞 E) : E) • v := by
        funext v
        exact (algebraMap_smul E (a : 𝓞 E) v).symm
      rw [e]
      exact MulAction.bijective (Units.mk0 _ ha0)
    · intro y
      have hy : y ∈ Submodule.span E (L : Set V) := hL ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
    · intro x y hxy
      exact ⟨1, by rw [Subtype.ext hxy]⟩
  let g : L →ₗ[𝓞 E] E := Algebra.linearMap (𝓞 E) E ∘ₗ ψ
  have hu : ∀ a : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) a) :=
    fun a => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) a
  refine ⟨(IsLocalizedModule.lift (nonZeroDivisors (𝓞 E)) L.subtype g hu).extendScalarsOfIsLocalization
    (nonZeroDivisors (𝓞 E)) E, fun x => ?_⟩
  exact IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E)) L.subtype g hu x

end Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem exists_vec (S : HSpace E) (φ : S.V →ₗ[E] E) : ∃ w, ∀ x, φ x = S.hT w x := by
  let G : S.V →ₗ[E] (Fin S.rank → E) := LinearMap.pi fun i => S.hT (S.frame i)
  have hG : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply S.nondeg.2 y
    intro x
    have : S.hT.flip y = 0 := S.frame.ext fun i => congrFun hy i
    exact LinearMap.congr_fun this x
  have hs : Function.Surjective G :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [S.rank_eq])).1 hG
  obtain ⟨w, hw⟩ := hs fun i => star (φ (S.frame i))
  refine ⟨w, fun x => LinearMap.congr_fun (S.frame.ext fun i => ?_ : φ = S.hT w) x⟩
  have h1 : S.hT (S.frame i) w = star (φ (S.frame i)) := congrFun hw i
  have h2 : star (S.hT (S.frame i) w) = S.hT w (S.frame i) := S.herm.eq _ _
  rw [← h2, h1, star_star]

theorem span_eq_top_of_unimodular {S : HSpace E} (L : Submodule (𝓞 E) S.V)
    (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT L) :
    Submodule.span E (L : Set S.V) = ⊤ := by
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨μ, hμ⟩ := exists_vec S φ
  have hμ₀ : μ ≠ 0 := by
    intro h
    apply hφ₀
    ext y
    simpa [h] using hμ y
  have hline (a : E) : a • μ ∈ L := by
    rw [← hU]
    change a • μ ∈ Formalism.E.hdual S.hT L
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← S.herm.eq (a • μ) y, LinearMap.map_smulₛₗ, ← hμ, hy₀]
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
    (show μ ∉ (⊥ : Submodule E S.V) by simpa using hμ₀)
  let f := ψ.restrictScalars (𝓞 E)
  have hmap (x : E) : x ∈ L.map f := by
    refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
    change ψ ((x / ψ μ) • μ) = x
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
  obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors (𝓞 E)) (hL.fg.map f)
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hne {a : 𝓞 E} (ha : a ≠ 0) : algebraMap (𝓞 E) E a ≠ 0 :=
    fun h => ha (hinj (h.trans (map_zero _).symm))
  have hinteger (x : E) : IsLocalization.IsInteger (𝓞 E) x := by
    have hx := hd _ (hmap ((algebraMap (𝓞 E) E d)⁻¹ * x))
    rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
      one_mul] at hx
  apply RingOfIntegers.not_isField E
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 E) E a)⁻¹)
  refine ⟨b, hinj ?_⟩
  rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]


theorem exists_dual_vec (S : HSpace E) (M0 L : Submodule (𝓞 E) S.V) (hL : Submodule.IsFullLattice E L)
    (h : IsPrimitiveSub M0 L) (ψ : M0 →ₗ[𝓞 E] 𝓞 E) :
    ∃ w : dualInH S.hT L, ∀ x : M0, (ψ x : E) = S.hT w x := by
  obtain ⟨r, hr⟩ := exists_retraction M0 L hL.fg h
  obtain ⟨φ, hφ⟩ := exists_extend_fun L (Submodule.IsFullLattice.span_eq_top (self := hL)) (ψ ∘ₗ r)
  obtain ⟨w, hw⟩ := exists_vec S φ
  refine ⟨⟨w, ?_, ?_⟩, fun x => ?_⟩
  · refine (Submodule.mem_iInf _).2 fun y => (Submodule.mem_iInf _).2 fun hy => ?_
    change S.hT y w ∈ (1 : Submodule (𝓞 E) E)
    have h2 : star (S.hT w y) = S.hT y w := S.herm.eq _ _
    have h3 : IsIntegral ℤ (S.hT y w) := by
      rw [← h2, ← hw, hφ ⟨y, hy⟩]
      exact (RingOfIntegers.isIntegral_coe _).map (starRingEnd E).toIntAlgHom
    exact Submodule.mem_one.2 ⟨⟨_, h3⟩, rfl⟩
  · change w ∈ Submodule.span E (L : Set S.V)
    rw [(Submodule.IsFullLattice.span_eq_top (self := hL))]; trivial
  · have := hφ ⟨x, h.1 x.2⟩
    rw [LinearMap.comp_apply, hr] at this
    rw [← this, hw]

theorem exists_reps (S : HSpace E) (M0 L : Submodule (𝓞 E) S.V) (hL : Submodule.IsFullLattice E L)
    (h : IsPrimitiveSub M0 L)
    (hfin : 1 ≤ Nat.card (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype)) :
    ∃ reps : Finset (M0 →ₗ[𝓞 E] 𝓞 E),
      reps.card ≤ Nat.card (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype) ∧
      ∀ ψ : M0 →ₗ[𝓞 E] 𝓞 E, ∃ ψ₀ ∈ reps, ∃ v ∈ L, ∀ x : M0, ((ψ x - ψ₀ x : 𝓞 E) : E) = S.hT v x := by
  choose w hw using exists_dual_vec S M0 L hL h
  haveI : Finite (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype) :=
    Nat.finite_of_card_ne_zero (by omega)
  letI := Fintype.ofFinite (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype)
  let g : (M0 →ₗ[𝓞 E] 𝓞 E) → (dualInH S.hT L ⧸ L.comap (dualInH S.hT L).subtype) :=
    fun ψ => Submodule.Quotient.mk (w ψ)
  refine ⟨Finset.univ.image (Function.invFun g), ?_, fun ψ => ?_⟩
  · rw [Nat.card_eq_fintype_card]; exact Finset.card_image_le
  · refine ⟨Function.invFun g (g ψ), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h1 : g ψ = g (Function.invFun g (g ψ)) := (Function.invFun_eq ⟨ψ, rfl⟩).symm
    have h2 := (Submodule.Quotient.eq _).1 h1
    refine ⟨_, h2, fun x => ?_⟩
    rw [Submodule.subtype_apply, Submodule.coe_sub, map_sub, LinearMap.sub_apply, ← hw, ← hw]
    push_cast
    rfl

theorem funIdx : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ M0 : LatW D, IsPrimitiveSub M0 (L0X D Λ (lf D F0)) → ∃ reps : Finset (M0 →ₗ[𝓞 D.host.E] 𝓞 D.host.E), (reps.card : ℝ) ≤ NT D u ^ 2 ∧ ∀ ψ : M0 →ₗ[𝓞 D.host.E] 𝓞 D.host.E, ∃ ψ₀ ∈ reps, ∃ v ∈ L0X D Λ (lf D F0), ∀ x : M0, ((ψ x - ψ₀ x : 𝓞 D.host.E) : D.host.E) = (D.sp.X 0).hT v x := by
  intro D u u' F0 Λ hStand hB hR M0 hM
  obtain ⟨hWH, -, hpd, hlat, hint, hdet, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ hStand hB hR
  have hfull : Submodule.IsFullLattice D.host.E (L0X D Λ (lf D F0)) := by
    refine { toIsLattice := hlat, span_eq_top := ?_ }
    apply eq_top_iff.mpr
    intro w _
    have hΛ : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ :=
      span_eq_top_of_unimodular Λ hR.2.1.1 hR.2.1.2.1
    have hw : D.sp.iXY 0 w ∈ orth (hS D) F0.Xplus :=
      hWH.1.le (Submodule.mem_sup_left ⟨w, rfl⟩)
    have hwX : D.sp.iXY 0 w ∈ orth (hS D) F0.X :=
      (Formalism.MainNotions.mem_orth_iff _ _).2 fun x hx =>
        (Formalism.MainNotions.mem_orth_iff _ _).1 hw x (Submodule.mem_sup_left hx)
    have hwz : (hS D).hT F0.z (D.sp.iXY 0 w) = 0 :=
      (Formalism.MainNotions.mem_orth_iff _ _).1 hw _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 D.host.E)) D.host.E Λ (D.sp.iXY 0 w) (hΛ ▸ Submodule.mem_top)
    rw [Submodule.span_eq] at ht
    have ht0 : (algebraMap (𝓞 D.host.E) D.host.E t) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
    have hmem : (t : 𝓞 D.host.E) • w ∈ L0X D Λ (lf D F0) := by
      change D.sp.iXY 0 ((t : 𝓞 D.host.E) • w) ∈ L0sub Λ (lf D F0)
      rw [← algebraMap_smul D.host.E, map_smul, algebraMap_smul]
      have hort : (t : 𝓞 D.host.E) • D.sp.iXY 0 w ∈ toO (hS D) (orth (hS D) F0.X) := by
        change (t : 𝓞 D.host.E) • D.sp.iXY 0 w ∈ (orth (hS D) F0.X).restrictScalars (𝓞 D.host.E)
        exact Submodule.smul_mem _ _ hwX
      refine ⟨⟨Submodule.mem_sup_left ⟨ht, hort⟩, hort⟩, ?_⟩
      change (hS D).hT F0.z ((t : 𝓞 D.host.E) • D.sp.iXY 0 w) = 0
      rw [← algebraMap_smul D.host.E, map_smul, hwz, smul_zero]
    have hspan : (t : 𝓞 D.host.E) • w ∈ Submodule.span D.host.E ((L0X D Λ (lf D F0)) : Set (D.sp.X 0).V) :=
      Submodule.subset_span hmem
    have hspan' : (algebraMap (𝓞 D.host.E) D.host.E t) • w ∈
        Submodule.span D.host.E ((L0X D Λ (lf D F0)) : Set (D.sp.X 0).V) := by
      rw [algebraMap_smul]
      exact hspan
    have := (Submodule.span D.host.E ((L0X D Λ (lf D F0)) : Set (D.sp.X 0).V)).smul_mem (algebraMap (𝓞 D.host.E) D.host.E t)⁻¹ hspan'
    rw [smul_smul, inv_mul_cancel₀ ht0, one_smul] at this
    exact this
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LoopC.DetCard.main D _ hlat.fg hpd hint
  obtain ⟨reps, hc, hr⟩ := exists_reps (D.sp.X 0) M0 _ hfull hM h1
  refine ⟨reps, ?_, hr⟩
  rw [← hdet, ← h2]
  exact_mod_cast hc

end GlobalTheory.LoopC.FunIdx
