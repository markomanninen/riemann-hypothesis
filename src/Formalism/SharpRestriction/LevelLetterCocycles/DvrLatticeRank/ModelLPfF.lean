module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfE
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.TmulMkLMemInvLOfValAtMemFilC

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

def WD : Prop :=
  ∀ τ ζ, Pt c ζ τ → ∀ {m m' : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T)
    (hy : ∀ j, y j ∈ NcS W T (c - 1)) (b : Fin m' → LetA O n) (z : Fin m' → W.DD T)
    (hz : ∀ k, z k ∈ NcS W T (c - 1)),
    ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ[O] mkL W T π' c (y j) (hy j) =
      ∑ k, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * b k) ⊗ₜ[O] mkL W T π' c (z k) (hz k) →
    expS W T c ζ a y = expS W T c ζ b z

theorem expS_alg_mul (ζ : LL) (o : O) {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) :
    expS W T c ζ (fun j => algebraMap O (LetA O n) o * a j) y = algebraMap O LL o • expS W T c ζ a y := by
  funext i
  simp only [expS, serC, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [map_mul, AlgHom.commutes, PowerSeries.algebraMap_apply, PowerSeries.coeff_C_mul, mul_smul]
  · rw [smul_zero]

theorem good_all (hwd : WD W T Pt π' c) {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c)
    {m : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T} (hr : IsRepL W T π' Eπ h' c x a y) :
    ∀ τ ζ, Pt c ζ τ → ∀ i : ℤ, expS W T c ζ (fun j => (a j : LetA O n)) y i ∈
      Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (h' - i) := by
  have hrep : x ∈ NLset W T Pt π' Eπ h' c := by
    clear hr
    induction hx using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      refine ⟨0, Fin.elim0, Fin.elim0, ⟨fun j => j.elim0, by simp⟩, fun τ ζ _ i => ?_⟩
      simp [expS]
    | add x₁ x₂ _ _ h₁ h₂ =>
      obtain ⟨m₁, a₁, y₁, ⟨hy₁, he₁⟩, hg₁⟩ := h₁
      obtain ⟨m₂, a₂, y₂, ⟨hy₂, he₂⟩, hg₂⟩ := h₂
      let z : Fin (m₁ + m₂) → ↥(NcS W T (c - 1)) :=
        Fin.append (fun j => ⟨y₁ j, hy₁ j⟩) (fun j => ⟨y₂ j, hy₂ j⟩)
      refine ⟨m₁ + m₂, Fin.append a₁ a₂, fun j => z j, ⟨fun j => (z j).2, ?_⟩, fun τ ζ hpt i => ?_⟩
      · rw [map_add (f := _), he₁, he₂, Fin.sum_univ_add]
        simp only [z, Fin.append_left, Fin.append_right]
      · simpa only [expS, Fin.sum_univ_add, z, Fin.append_left, Fin.append_right] using
          Submodule.add_mem _ (hg₁ τ ζ hpt i) (hg₂ τ ζ hpt i)
    | smul o x _ hx =>
      obtain ⟨m, a, y, ⟨hy, he⟩, hg⟩ := hx
      refine ⟨m, fun j => o • a j, y, ⟨hy, ?_⟩, fun τ ζ hpt i => ?_⟩
      · rw [map_smul, he, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [TensorProduct.smul_tmul', Subalgebra.coe_smul, mul_smul_comm]
        simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
      · simp only [Subalgebra.coe_smul]
        simpa only [Algebra.smul_def, expS_alg_mul, Pi.smul_apply] using
          Submodule.smul_mem _ (algebraMap O LL o) (hg τ ζ hpt i)
  obtain ⟨m', a', y', ⟨hy', hx'⟩, hg⟩ := hrep
  obtain ⟨hy, hxr⟩ := hr
  intro τ ζ hpt i
  rw [hwd τ ζ hpt _ y hy _ y' hy' (hxr.symm.trans hx')]
  exact hg τ ζ hpt i

theorem nl_le : NL W T Pt π' Eπ h' c ≤ LamLA W T π' Eπ h' c ⊤ := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨m, a, y, ⟨hy, hx⟩, -⟩
  refine ⟨∑ j, a j ⊗ₜ ⟨mkL W T π' c (y j) (hy j), Submodule.mem_top⟩, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, hx]
  rfl

theorem nl_smulA {b : LetA O n} (hb : b ∈ W.AΔ) {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c) :
    smulLA W T π' c b x ∈ NL W T Pt π' Eπ h' c := by
  have htmul (a : LetA O n) (e : W.EE) (z : LcQ W T π' c) :
      smulLA W T π' c a (e ⊗ₜ z) = (algebraMap (LetA O n) W.EE a * e) ⊗ₜ z := rfl
  have hcomm (x : LA W T π' c) :
      smulLA W T π' c (Eπ ^ h') (smulLA W T π' c b x) =
        smulLA W T π' c b (smulLA W T π' c (Eπ ^ h') x) := by
    induction x using TensorProduct.inductionOn with
    | tmul e z => simp only [htmul, mul_left_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, a, y, ⟨hy, he⟩, hg⟩ := hx
    refine Submodule.subset_span
      ⟨m, fun j => ⟨b * a j, W.AΔ.mul_mem hb (a j).2⟩, y, ⟨hy, ?_⟩, fun τ ζ hpt => ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hcomm, he, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [htmul, ← map_mul]
      congr 2
      ring
    · exact MLB.goodF_mul W T c ζ τ h' b _ y (hg τ ζ hpt)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ _ hx

theorem nl_sat (hwd : WD W T Pt π' c) (hp : algebraMap O LL ((PD.p : ℕ) : O) ≠ 0)
    {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (k : ℕ)
    (hk : ((PD.p : ℕ) : O) ^ k • x ∈ NL W T Pt π' Eπ h' c) : x ∈ NL W T Pt π' Eπ h' c := by
  have hrep : ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a y := by
    obtain ⟨t, ht⟩ := hx
    obtain ⟨m, a, s, rfl⟩ := MLE.exists_fin_sum t
    have hs : ∀ j, ∃ z : ↥(NcS W T (c - 1)), Submodule.Quotient.mk z =
        ((s j : ↥(⊤ : Submodule O _)) : LcQ W T π' c) := fun j => Submodule.Quotient.mk_surjective _ _
    choose z hz using hs
    refine ⟨m, a, fun j => z j, ⟨fun j => (z j).2, ?_⟩⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← ht, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ
      ((s j : ↥(⊤ : Submodule O _)) : LcQ W T π' c) = _
    rw [← hz j]
    rfl
  obtain ⟨m, a, y, hy, he⟩ := hrep
  let o : O := ((PD.p : ℕ) : O) ^ k
  have hr' : IsRepL W T π' Eπ h' c (o • x) (fun j => o • a j) y := by
    refine ⟨hy, ?_⟩
    rw [map_smul, he, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul', Subalgebra.coe_smul, mul_smul_comm]
    simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  have hg := good_all W T Pt π' Eπ h' c hwd hk hr'
  refine Submodule.subset_span ⟨m, a, y, ⟨hy, he⟩, fun τ ζ hpt i => ?_⟩
  have h1 := hg τ ζ hpt i
  simp only [Subalgebra.coe_smul] at h1
  simp only [Algebra.smul_def, expS_alg_mul, Pi.smul_apply] at h1
  have ho : algebraMap O LL o ≠ 0 := by simpa only [o, map_pow] using pow_ne_zero k hp
  exact (Submodule.smul_mem_iff _ ho).1 h1

end Generic

end Formalism.MainNotions.N.Ln34.MLF

end
