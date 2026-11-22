module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.JacquetExact

section Abstract

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_finset_of_mem_twKer {τ : Representation ℂ G W} {N : Subgroup G} {w : W}
    (hw : w ∈ twKer τ N 1) :
    ∃ S : Finset G, (∀ u ∈ S, u ∈ N) ∧ ∀ H : Subgroup G, (∀ u ∈ S, u ∈ H) → w ∈ twKer τ H 1 := by
  classical
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, v, rfl⟩ := hx
    refine ⟨{(u : G)}, by simp, fun H hH => ?_⟩
    simpa using GlobalTheory.IwahoriInj.sub_mem_twKer (π := τ) (hH u (by simp)) v
  | zero => exact ⟨∅, by simp, fun _ _ => zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S, hS, hx⟩ := hx
    obtain ⟨T, hT, hy⟩ := hy
    refine ⟨S ∪ T, fun u hu => (Finset.mem_union.1 hu).elim (hS u) (hT u), fun H hH => add_mem
      (hx H fun u hu => hH u (Finset.mem_union_left _ hu))
      (hy H fun u hu => hH u (Finset.mem_union_right _ hu))⟩
  | smul c x _ hx =>
    obtain ⟨S, hS, hx⟩ := hx
    exact ⟨S, hS, fun H hH => Submodule.smul_mem _ c (hx H hH)⟩

theorem map_mem_twKer {σ : Representation ℂ G V} {τ : Representation ℂ G W} (f : σ.IntertwiningMap τ)
    {H : Subgroup G} {v : V} (hv : v ∈ twKer σ H 1) : f v ∈ twKer τ H 1 := by
  have h : twKer σ H 1 ≤ (twKer τ H 1).comap f.toLinearMap := Submodule.span_le.2 (by
    rintro _ ⟨n, v, rfl⟩
    refine Submodule.subset_span ⟨n, f v, ?_⟩
    simp [f.isIntertwining])
  exact h hv

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem mem_twKer_of_compact {σ : Representation ℂ G V} {τ : Representation ℂ G W} (hτ : IsSmooth τ)
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f) {H : Subgroup G} (hH : IsCompact (H : Set G))
    {v : V} (hv : f v ∈ twKer τ H 1) : v ∈ twKer σ H 1 := by
  have hσ : IsSmooth σ := (IsSubquotient.of_injective f hf).isSmooth hτ
  obtain ⟨v', hv', he⟩ := IwahoriOnto.exists_fixed_map_eq hσ hH (twKer σ H 1).mkQ v fun h hh =>
    (Submodule.Quotient.eq _).2 (GlobalTheory.IwahoriInj.sub_mem_twKer hh v)
  have h1 : v' - v ∈ twKer σ H 1 := (Submodule.Quotient.eq _).1 he
  have h2 : f v' ∈ twKer τ H 1 := by
    have := add_mem (map_mem_twKer f h1) hv
    rwa [map_sub, sub_add_cancel] at this
  have h3 : f v' ∈ fixed τ H := GlobalTheory.IwahoriInj.mem_fixed.2 fun h hh => by
    rw [← f.isIntertwining, GlobalTheory.IwahoriInj.mem_fixed.1 hv' h hh]
  have h4 : v' = 0 := hf ((GlobalTheory.IwahoriInj.eq_zero_of_fixed hτ hH h3 h2).trans (map_zero f).symm)
  rw [h4, zero_sub] at h1
  exact neg_mem_iff.1 h1

end Abstract

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {s : ℕ} {d : Fin s → ℕ}

theorem jacMap_injective (e : (Σ a, Fin (d a)) ≃ n) {σ : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (jacMap e f) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : f v ∈ twKer τ (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
  let c : n → ℤ := fun i => (blk e i).val
  have hN : unipRad k e = unipOf k c := unipRad_eq_unipOf k fun i j => by simp [c]
  obtain ⟨S, hS, h2⟩ := exists_finset_of_mem_twKer h1
  have hcompact : ∃ H : Subgroup (GL n k), H ≤ unipOf k c ∧
      IsCompact (H : Set (GL n k)) ∧ ∀ u ∈ S, u ∈ H := by
    let K (m : ℕ) := GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m)
    have hentries {u : GL n k} (hu : u ∈ unipOf k c) :
        ∀ᶠ m : ℕ in Filter.atTop, ∀ i j, Deep ((m : ℤ) * (c i - c j)) (u.val i j) := by
      simp only [Filter.eventually_all]
      intro i j
      by_cases hij : c i < c j
      · filter_upwards [GlobalTheory.IwahoriInj.eventually_deep (u.val i j)] with m hm
        exact hm.mono (by nlinarith [Int.natCast_nonneg m])
      · rw [mem_unipOf.1 hu i j hij]
        refine Filter.Eventually.of_forall fun m => ?_
        by_cases heq : i = j
        · subst j
          simp [GlobalTheory.IwahoriInj.deep_zero_iff]
        · simp [one_apply_ne heq, GlobalTheory.IwahoriInj.deep_zero]
    have hmem : ∀ᶠ m in Filter.atTop, ∀ u ∈ S, u ∈ K m :=
      (Filter.eventually_all_finset S).2 fun u hu => by
        have hu' := hN ▸ hS u hu
        exact (hentries hu').and (hentries (inv_mem hu'))
    obtain ⟨m, hm⟩ := hmem.exists
    refine ⟨K m ⊓ unipOf k c, inf_le_right, ?_, fun u hu => ⟨hm u hu, hN ▸ hS u hu⟩⟩
    obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
    have hclosed : IsClosed (unipOf k c : Set (GL n k)) := by
      have heq : (unipOf k c : Set (GL n k)) =
          ⋂ i, ⋂ j, ⋂ (_ : ¬ c i < c j), {g : GL n k | g.val i j = (1 : Matrix n n k) i j} := by
        ext g
        simp only [SetLike.mem_coe, mem_unipOf, Set.mem_iInter, Set.mem_ofPred_eq]
      rw [heq]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
    rw [Subgroup.coe_inf]
    exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right hclosed
  obtain ⟨H, hle, hH, hSH⟩ := hcompact
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  exact GlobalTheory.IwahoriInj.twKer_mono (hle.trans hN.ge) (mem_twKer_of_compact hτ f hf hH (h2 H hSH))

theorem jacMap_surjective (e : (Σ a, Fin (d a)) ≃ n) {σ : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) : Function.Surjective (jacMap e f) := fun y => by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨Submodule.Quotient.mk v, rfl⟩

theorem isSubquotient_jac (e : (Σ a, Fin (d a)) ≃ n) {π : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (hτ : IsSmooth τ) (h : IsSubquotient π τ) :
    IsSubquotient (jac e π) (jac e τ) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap τ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  exact (IsSubquotient.of_surjective _ (jacMap_surjective e f hf)).trans
    (.of_injective _ (jacMap_injective e hτ ι Subtype.val_injective))

end Local

theorem inSupport_of_isSubquotient (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (V : Type) [AddCommGroup V]
    [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL n k) V)
    (τ : Representation ℂ (GL n k) W) (χ : kˣ →* ℂˣ) (hτ : IsSmooth τ) (h : IsSubquotient π τ)
    (hχ : InSupport π χ) : InSupport τ χ := by
  obtain ⟨s, d, e, a, ha, Y, i1, i2, σ, hσ, hsub, hact⟩ := hχ
  exact ⟨s, d, e, a, ha, Y, i1, i2, σ, hσ, hsub.trans (isSubquotient_jac e hτ h), hact⟩

end GlobalTheory.JacquetExact
