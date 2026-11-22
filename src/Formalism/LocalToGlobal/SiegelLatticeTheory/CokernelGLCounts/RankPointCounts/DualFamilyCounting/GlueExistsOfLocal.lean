module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfOf
public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G7

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem zmult_of_span (M : Submodule (𝓞 K) V) (x : V) (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hnx m
    · rw [mul_smul]; exact zsmul_mem hmy n
  | smul a x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨k, hk, α, hα⟩ := Formalism.HermitianLatticesTheory.traceReal_den a
    refine ⟨k * n, mul_ne_zero hk hn, ?_⟩
    have e1 : (k * n) • (a • x) = α • (n • x) := by
      rw [← Int.cast_smul_eq_zsmul K (k * n), ← algebraMap_smul K α (n • x),
        ← Int.cast_smul_eq_zsmul K n, smul_smul, smul_smul]
      congr 1
      rw [show algebraMap (NumberField.RingOfIntegers K) K α = (α : K) from rfl, ← hα]
      push_cast
      ring
    rw [e1]
    exact M.smul_mem α hnx

def zdiv (B : Submodule (𝓞 K) V) (n : ℤ) : Submodule (𝓞 K) V where
  carrier := {x | n • x ∈ B}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    show n • (a + b) ∈ B
    rw [smul_add]
    exact B.add_mem ha hb
  smul_mem' := by
    intro c x hx
    show n • (c • x) ∈ B
    rw [smul_comm]
    exact B.smul_mem c hx

theorem exists_zsmul_of_fg {A B : Submodule (𝓞 K) V} (hA : A.FG)
    (hAB : ∀ y ∈ A, ∃ n : ℤ, n ≠ 0 ∧ n • y ∈ B) : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ A, n • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! m hm hmy using fun y (hy : y ∈ S) => hAB y (Submodule.subset_span hy)
  refine ⟨∏ y ∈ S, m y, Finset.prod_ne_zero_iff.2 hm, fun x hx => ?_⟩
  show x ∈ zdiv B (∏ y ∈ S, m y)
  refine (Submodule.span_le.2 ?_) hx
  intro y hy
  show (∏ y ∈ S, m y) • y ∈ B
  rw [← Finset.prod_erase_mul S m hy, mul_smul]
  exact zsmul_mem (hmy y hy) _

theorem locF_le_of_zsmul {A B : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (n : ℤ)
    (hn : (n : 𝓞 F) ∉ 𝔭) (hAB : ∀ x ∈ A, n • x ∈ B) : locF 𝔭 A ≤ locF 𝔭 B := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp A x).1 hx
  refine (LocF.mem_locF_iff hp B x).2 ⟨(n : 𝓞 F) * t, fun hm => (hp.mem_or_mem hm).elim hn ht, ?_⟩
  rw [map_mul, map_intCast, mul_smul, Int.cast_smul_eq_zsmul]
  exact hAB _ htx

theorem badFinite {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Submodule.IsFullLattice K Λ₀)
    {U : Submodule K V} {M : Submodule (𝓞 K) V} (hM : IsLatIn U M) :
    ∃ s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∀ 𝔭 ∉ s,
      locF 𝔭.1 (Λ₀ ⊓ U.restrictScalars (𝓞 K)) = locF 𝔭.1 M := by
  classical
  set N : Submodule (𝓞 K) V := Λ₀ ⊓ U.restrictScalars (𝓞 K) with hN
  have hMU : ∀ y ∈ M, y ∈ U := fun y hy => by
    rw [← hM.2]; exact Submodule.subset_span hy
  obtain ⟨n₁, hn₁, h₁⟩ : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ M, n • x ∈ N := by
    refine exists_zsmul_of_fg hM.1 fun y hy => ?_
    obtain ⟨m, hm, hmy⟩ := Formalism.HermitianLatticesTheory.traceReal_mult Λ₀ hΛ₀ y
    exact ⟨m, hm, Submodule.mem_inf.2 ⟨hmy, zsmul_mem (hMU y hy) m⟩⟩
  have hNfg : N.FG := Submodule.FG.of_le hΛ₀.fg inf_le_left
  obtain ⟨n₂, hn₂, h₂⟩ : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ N, n • x ∈ M := by
    refine exists_zsmul_of_fg hNfg fun y hy => zmult_of_span M y ?_
    rw [hM.2]
    exact (Submodule.mem_inf.1 hy).2
  set a : 𝓞 F := ((n₁ * n₂ : ℤ) : 𝓞 F) with ha
  have ha0 : a ≠ 0 := by
    rw [ha, Int.cast_ne_zero]
    exact mul_ne_zero hn₁ hn₂
  have hD : Ideal.span {a} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hfin : {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | a ∈ 𝔭.1}.Finite := by
    refine ((Ideal.finite_factors hD).image (fun v =>
      (⟨v.asIdeal, v.isMaximal⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}))).subset ?_
    intro 𝔭 h𝔭
    have hne : 𝔭.1 ≠ ⊥ := fun e => ha0 (by
      have : a ∈ 𝔭.1 := h𝔭
      rwa [e, Ideal.mem_bot] at this)
    refine ⟨⟨𝔭.1, 𝔭.2.isPrime, hne⟩, ?_, rfl⟩
    show 𝔭.1 ∣ Ideal.span {a}
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact h𝔭
  refine ⟨hfin.toFinset, fun 𝔭 h𝔭 => ?_⟩
  have haP : a ∉ 𝔭.1 := fun h => h𝔭 (hfin.mem_toFinset.2 h)
  have e : a = (n₁ : 𝓞 F) * (n₂ : 𝓞 F) := by rw [ha]; push_cast; ring
  have h1P : (n₁ : 𝓞 F) ∉ 𝔭.1 := fun h => haP (e ▸ Ideal.mul_mem_right _ _ h)
  have h2P : (n₂ : 𝓞 F) ∉ 𝔭.1 := fun h => haP (e ▸ Ideal.mul_mem_left _ _ h)
  exact le_antisymm (locF_le_of_zsmul 𝔭.2.isPrime n₂ h2P h₂)
    (locF_le_of_zsmul 𝔭.2.isPrime n₁ h1P h₁)

private theorem span_dual_eq_top (h : V →ₗ⋆[K] V →ₗ[K] K)
    {L : Submodule (𝓞 K) V} (hL : L.FG) :
    Submodule.span K (Formalism.HermitianLatticesTheory.dual h L : Set V) = ⊤ := by
  classical
  obtain ⟨S, rfl⟩ := hL
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨n, hn, hint⟩ :=
    exists_integral_multiples ℤ ℚ (L := K) (S.image fun y => h y x)
  have hx : n • x ∈ Formalism.HermitianLatticesTheory.dual h (Submodule.span (𝓞 K) (S : Set V)) := by
    rw [mem_dual_iff]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rw [map_zsmul]
      exact Submodule.mem_one.mpr ⟨⟨_, hint _ (Finset.mem_image_of_mem _ hy)⟩, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range c
      rw [← algebraMap_smul K c y, map_smulₛₗ h (algebraMap (𝓞 K) K c) y, LinearMap.smul_apply,
        smul_eq_mul, starRingEnd_apply, ← hr, ← smul_eq_mul, algebraMap_smul]
      exact Submodule.smul_mem _ r hy
  refine (Submodule.smul_mem_iff _ (Int.cast_ne_zero.mpr hn : (n : K) ≠ 0)).mp ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Submodule.subset_span hx

private theorem span_locF_eq (L : Submodule (𝓞 K) V) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) :
    Submodule.span K (locF 𝔭 L : Set V) = Submodule.span K (L : Set V) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono (LocF.le_locF 𝔭 L))
  show locF 𝔭 L ≤ (Submodule.span K (L : Set V)).restrictScalars (𝓞 K)
  rw [← locF_subspace (Submodule.span K (L : Set V)) hp]
  exact LocF.locF_mono 𝔭 (fun _ hx => Submodule.subset_span hx)

theorem glueExists_of_local (hloc : GlueLocal) : GlueExists := by
  classical
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀' M hM hMi hc
  obtain ⟨Λ₀, hΛ₀, hΛ₀u⟩ := hΛ₀'
  have hΛ₀full : Submodule.IsFullLattice K Λ₀ :=
    { toIsLattice := hΛ₀, span_eq_top := hΛ₀u ▸ span_dual_eq_top h hΛ₀.fg }
  obtain ⟨s, hsM⟩ := badFinite (F := F) hΛ₀full hM
  choose T hT hTd hTm using fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
    hloc K F V hK hF h hs hnd U hUc hpos ⟨Λ₀, hΛ₀, hΛ₀u⟩ M hM hMi 𝔭.1 𝔭.2 (hc 𝔭.1 𝔭.2)
  choose A hA hAT using hT
  have hAfull (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) : Submodule.IsFullLattice K (A 𝔭) := by
    refine { toIsLattice := hA 𝔭, span_eq_top := ?_ }
    rw [← span_locF_eq (A 𝔭) 𝔭.2.isPrime, hAT 𝔭, ← hTd 𝔭, ← hAT 𝔭,
      ← locF_dual hF h (hA 𝔭).fg 𝔭.2.isPrime, span_locF_eq _ 𝔭.2.isPrime]
    exact span_dual_eq_top h (hA 𝔭).fg
  let B := fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => if 𝔭 ∈ s then A 𝔭 else Λ₀
  have hB (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) : Submodule.IsFullLattice K (B 𝔭) := by
    by_cases hp : 𝔭 ∈ s
    · simpa only [B, ite_eq_left hp] using hAfull 𝔭
    · simpa only [B, ite_eq_right hp] using hΛ₀full
  have hBs : ∀ 𝔭 ∉ s, B 𝔭 = Λ₀ := fun 𝔭 hp => ite_eq_right hp
  let Λ := ⨅ 𝔭, locF 𝔭.1 (B 𝔭)
  obtain ⟨hΛ, hΛloc⟩ : Submodule.IsLattice K Λ ∧ ∀ 𝔭, locF 𝔭.1 Λ = locF 𝔭.1 (B 𝔭) :=
    LocF.patch hΛ₀full s B hB hBs
  have key (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
      locF 𝔭.1 Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭.1 M ∧
        dualF h 𝔭.1 (locF 𝔭.1 Λ) = locF 𝔭.1 Λ := by
    rw [hΛloc 𝔭]
    by_cases hp : 𝔭 ∈ s
    · rw [show B 𝔭 = A 𝔭 from ite_eq_left hp, hAT 𝔭]
      exact ⟨hTm 𝔭, hTd 𝔭⟩
    · rw [hBs 𝔭 hp]
      refine ⟨?_, ?_⟩
      · rw [← hsM 𝔭 hp, LIOrb.locF_inf_locF 𝔭.2, locF_subspace U 𝔭.2.isPrime]
      · rw [← locF_dual hF h hΛ₀.fg 𝔭.2.isPrime]
        exact congrArg (locF 𝔭.1) hΛ₀u
  refine ⟨Λ, hΛ, ?_, ?_⟩
  · show Formalism.HermitianLatticesTheory.dual h Λ = Λ
    apply eq_of_locF (F := F)
    intro 𝔭 h𝔭
    rw [locF_dual hF h hΛ.fg h𝔭.isPrime]
    exact (key ⟨𝔭, h𝔭⟩).2
  · apply eq_of_locF (F := F)
    intro 𝔭 h𝔭
    rw [LIOrb.locF_inf_locF h𝔭, locF_subspace U h𝔭.isPrime]
    exact (key ⟨𝔭, h𝔭⟩).1

end Formalism.L2.SG.Pf.G7
