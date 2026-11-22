module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MulEqZeroIff

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

omit [FiniteDimensional K V] in
theorem isIntegralLat_smul {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (c : 𝓞 F) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (algebraMap F K (c : F) • h) L := by
  intro x hx y hy
  have h1 : algebraMap F K (c : F) ∈ (1 : Submodule (𝓞 K) K) :=
    Submodule.mem_one.2 ⟨algebraMap (𝓞 F) (𝓞 K) c, rfl⟩
  have h2 := Submodule.mul_mem_mul h1 (hLi x hx y hy)
  rw [one_mul] at h2
  exact h2

theorem akCount_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ} (hk : vF 𝔭 c ≤ k) :
    akCount (algebraMap F K (c : F) • h) L 𝔭 k =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * finrank K V ^ 2) * akCount h L 𝔭 (k - vF 𝔭 c) := by
  have : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hL h𝔭
  obtain ⟨H, hH, _⟩ := LocF.exists_gram hLi b hbL
  have hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) =
      (algebraMap F K (c : F) • h) (b i) (b j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]
    rfl
  rw [integralBasisSpans.akCount_eq _ h𝔭 b hb hH', integralBasisSpans.akCount_eq h h𝔭 b hb hH, PinAA.akM_smul hK h𝔭 hc hk,
    Fintype.card_fin]

theorem nkCount_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (n : 𝓞 F) {k : ℕ} (hk : vF 𝔭 c ≤ k) :
    nkCount (algebraMap F K (c : F) • h) L 𝔭 k (c * n) =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * finrank K V) * nkCount h L 𝔭 (k - vF 𝔭 c) n := by
  have : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hL h𝔭
  obtain ⟨H, hH, _⟩ := LocF.exists_gram hLi b hbL
  have hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) =
      (algebraMap F K (c : F) • h) (b i) (b j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]
    rfl
  rw [integralBasisSpans.nkCount_eq _ h𝔭 b hb hH', integralBasisSpans.nkCount_eq h h𝔭 b hb hH, PinAA.nkM_smul hK h𝔭 hc n hk,
    Fintype.card_fin]

omit [NumberField K] [StarRing K] [Algebra F K] in
theorem pow_notMem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} {j : ℕ} (hc : c ∉ 𝔭 ^ (j + 1))
    (m : ℕ) : c ^ m ∉ 𝔭 ^ (m * j + 1) := by
  induction m with
  | zero =>
    rw [pow_zero, zero_mul, zero_add, pow_one]
    exact fun e => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 e)
  | succ m ih =>
    rw [show (m + 1) * j + 1 = m * j + j + 1 by ring, pow_succ c]
    exact idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) ih hc

theorem gram_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 F) (x : Fin (finrank K V) → V) :
    (Matrix.of fun i j => (algebraMap F K (c : F) • h) (x i) (x j)).det =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V)) *
        (Matrix.of fun i j => h (x i) (x j)).det := by
  have e : (Matrix.of fun i j => (algebraMap F K (c : F) • h) (x i) (x j)) =
      algebraMap F K (c : F) • Matrix.of fun i j => h (x i) (x j) := by
    ext i j
    rfl
  rw [e, Matrix.det_smul, Fintype.card_fin]
  congr 1
  simp only [map_pow]
  rfl

theorem discrIdeal_smul_le_iff {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0)
    (e : ℕ) :
    discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ (finrank K V * vF 𝔭 c + e) ↔
      discrIdeal h L ≤ extP K 𝔭 ^ e := by
  constructor
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    let d := c ^ finrank K V
    let v := finrank K V * vF 𝔭 c
    have hd : d ∉ 𝔭 ^ (v + 1) :=
      pow_notMem h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hc) (finrank K V)
    have hz : algebraMap (𝓞 F) (𝓞 K) d * z ∈ extP K 𝔭 ^ (v + e) := by
      apply hle
      exact Ideal.subset_span ⟨x, hx, by rw [gram_smul, map_mul, ez]⟩
    have hspan : extP K 𝔭 ^ v ≤
        Ideal.span {algebraMap (𝓞 F) (𝓞 K) d} ⊔ extP K 𝔭 ^ (v + e) := by
      have h := idealPowerSpanBounds.pow_le_span_sup h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) hd (v + e)
      simpa only [extP, Ideal.map_pow, Ideal.map_sup, Ideal.map_span, Set.image_singleton] using
        (Ideal.map_mono (f := algebraMap (𝓞 F) (𝓞 K)) h)
    have hmul : extP K 𝔭 ^ v * Ideal.span {z} ≤ extP K 𝔭 ^ (v + e) := by
      refine (Ideal.mul_mono_left hspan).trans ?_
      rw [Ideal.sup_mul, Ideal.span_singleton_mul_span_singleton]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hz) Ideal.mul_le_left
    have hne : extP K 𝔭 ^ v ≠ 0 :=
      pow_ne_zero _ (idealPowerSpanBounds.map_ne_bot_of_isMaximal (K := K) h𝔭)
    have hdiv : extP K 𝔭 ^ v * extP K 𝔭 ^ e ∣ extP K 𝔭 ^ v * Ideal.span {z} := by
      rw [← pow_add]
      exact Ideal.dvd_iff_le.mpr hmul
    exact Ideal.dvd_span_singleton.mp ((mul_dvd_mul_iff_left hne).mp hdiv)
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    obtain ⟨g, -, hdet⟩ := LocF.exists_gram hLi x hx
    have hz : z = algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) * g.det := by
      apply RingOfIntegers.coe_injective
      show algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K _
      rw [ez, gram_smul, map_mul, hdet]
    have h1 : g.det ∈ extP K 𝔭 ^ e := hle (Ideal.subset_span ⟨x, hx, hdet⟩)
    have h2 : algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) ∈ extP K 𝔭 ^ (finrank K V * vF 𝔭 c) := by
      rw [extP, ← Ideal.map_pow]
      apply Ideal.mem_map_of_mem
      rw [mul_comm, pow_mul]
      exact Ideal.pow_mem_pow (localValuationFiltration.mem_pow_vF h𝔭 hc) _
    show z ∈ _
    rw [hz, pow_add]
    exact Ideal.mul_mem_mul h2 h1

theorem vd_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) :
    vd (algebraMap F K (c : F) • h) L 𝔭 = vd h L 𝔭 + finrank K V * vF 𝔭 c := by
  have hD : discrIdeal h L ≠ ⊥ := by
    obtain ⟨b, hbL, _⟩ := LocalSpans.exists_basis_locF hL h𝔭
    obtain ⟨g, _, hdet⟩ := LocF.exists_gram hLi b hbL
    intro hbot
    have hmem : g.det ∈ discrIdeal h L := Ideal.subset_span ⟨b, hbL, hdet⟩
    rw [hbot, Ideal.mem_bot] at hmem
    apply LocF.gram_det_ne_zero h (LocF.aniso_of_totPosDef hd) b b.linearIndependent
    rw [← hdet, hmem, map_zero]
  have hE : extP K 𝔭 ≠ ⊤ := by
    intro e
    apply h𝔭.ne_top
    have h : Ideal.comap (algebraMap (𝓞 F) (𝓞 K)) (extP K 𝔭) = 𝔭 :=
      Ideal.comap_map_eq_self_of_faithfullyFlat 𝔭
    rw [e, Ideal.comap_top] at h
    exact h.symm
  have hb : BddAbove {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    apply hD
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isDomain (extP K 𝔭) hE]
    refine le_iInf fun k => ?_
    obtain ⟨e, he, hke⟩ := hnb k
    exact he.trans (Ideal.pow_le_pow_right hke.le)
  have hmem : vd h L 𝔭 ∈ {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} :=
    Nat.sSup_mem ⟨0, by simp⟩ hb
  have hg : IsGreatest {e : ℕ | discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ e}
      (vd h L 𝔭 + finrank K V * vF 𝔭 c) := by
    constructor
    · rw [add_comm]
      exact (discrIdeal_smul_le_iff hLi h𝔭 hc _).2 hmem
    · intro e' he'
      by_cases hlt : e' ≤ finrank K V * vF 𝔭 c
      · omega
      · obtain ⟨e, rfl⟩ : ∃ e, e' = finrank K V * vF 𝔭 c + e := ⟨e' - finrank K V * vF 𝔭 c, by omega⟩
        have h1 : e ≤ vd h L 𝔭 := le_csSup hb ((discrIdeal_smul_le_iff hLi h𝔭 hc e).1 he')
        omega
  exact hg.csSup_eq

end Formalism.HermitianLattices.Ext.L3.PinA
