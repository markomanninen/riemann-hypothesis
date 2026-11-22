module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PermOfWeilDeligneSpecialDecompositionEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne.SpSummand GlobalTheory.WeilDeligne.SpUnique in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perm_of_weilDeligne_special_decomposition_eq :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
      (l l' : List (WD h × ℕ)),
      (∀ p ∈ l, IsIrrWD p.1) → (∀ p ∈ l', IsIrrWD p.1) →
      sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp (h := h) (p.2 + 1)))) =
        sumList (l'.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp (h := h) (p.2 + 1)))) →
      l.Perm l' := by
  intro E Ω _ _ _ _ _ A w h l l'
  classical
  let F : WD h × ℕ → WD h := fun p => p.1.lpChar (WD.lpSp (h := h) (p.2 + 1))
  suffices H : ∀ n (l l' : List (WD h × ℕ)), l.length = n → (∀ p ∈ l, IsIrrWD p.1) →
      (∀ p ∈ l', IsIrrWD p.1) → sumList (l.map F) = sumList (l'.map F) → l.Perm l' from
    H _ l l' rfl
  intro n
  induction n with
  | zero =>
    intro l l' hn hl hl' heq
    obtain rfl := List.length_eq_zero_iff.1 hn
    cases l' with
    | nil => exact List.Perm.nil
    | cons q l'' =>
      exfalso
      have hd := congrArg WD.lpDim heq
      change WD.lpDim (WD.lpZero (h := h)) = WD.lpDim (WD.lpSum _ (sumList _)) at hd
      rw [WD.lpDim_zero, WD.lpDim_sum] at hd
      have hpos : 0 < WD.lpDim (F q) := by
        obtain ⟨m, a, ha, hirr⟩ := hl' q List.mem_cons_self
        dsimp only [F]
        rw [WD.lpDim_tensor, WD.lpDim_lpSp, ← ha, WD.lpDim_mk, Module.finrank_fin_fun]
        obtain ⟨v, hv⟩ := SpSummand.exists_ne_zero hirr
        have hm : m ≠ 0 := by
          rintro rfl
          exact hv (Subsingleton.elim _ _)
        exact Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.succ_pos _)
      omega
  | succ n ih =>
    intro l l' hn hl hl' heq
    have hne : l ≠ [] := by
      rintro rfl
      simp at hn
    obtain ⟨⟨y, k⟩, hp, hmax⟩ : ∃ p ∈ l, ∀ q ∈ l, q.2 ≤ p.2 := by
      obtain ⟨p, hp, hmax⟩ := l.toFinset.exists_max_image Prod.snd
        (by obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hne; exact ⟨x, List.mem_toFinset.2 hx⟩)
      exact ⟨p, List.mem_toFinset.1 hp, fun q hq => hmax q (List.mem_toFinset.2 hq)⟩
    obtain ⟨m, a, rfl, ha⟩ := hl _ hp

    have hQ : HasCopyW a.ρ k (lastEig h k) (sumList (l.map F)) := by
      refine hasCopyW_sumList F l _ hp ?_
      show HasCopyW a.ρ k (lastEig h k) ((WD.mk a).lpChar (WD.lpSp (h := h) (k + 1)))
      rw [WD.lpSp, WD.lpChar_mk, hasCopyW_mk]
      exact hasCopy_self a ha k
    have hZ : PowZeroW k (sumList (l.map F)) := by
      refine powZeroW_sumList F l fun q hq => ?_
      rcases q with ⟨y', k'⟩
      obtain ⟨m', a', rfl, ha'⟩ := hl _ hq
      show PowZeroW k ((WD.mk a').lpChar (WD.lpSp (h := h) (k' + 1)))
      rw [WD.lpSp, WD.lpChar_mk, powZeroW_mk]
      exact powZero_of_le a' ha' (hmax _ hq)
    rw [heq] at hQ hZ
    obtain ⟨⟨y', k'⟩, hq', hqQ, hqZ⟩ := exists_mem_of_sumList F l' hQ hZ
    obtain ⟨n', a', rfl, ha'⟩ := hl' _ hq'
    dsimp only [F] at hqQ hqZ
    rw [WD.lpSp, WD.lpChar_mk, hasCopyW_mk] at hqQ
    rw [WD.lpSp, WD.lpChar_mk, powZeroW_mk] at hqZ
    obtain ⟨hm, hiso⟩ := eq_of_hasCopy a ha a' ha' k' k hqQ hqZ
    have hp' : (WD.mk a, k) ∈ l' := by
      have : ((WD.mk a', k') : WD h × ℕ) = (WD.mk a, k) := Prod.ext (WD.sound hiso).symm hm
      rw [← this]
      exact hq'

    let p : WD h × ℕ := (WD.mk a, k)
    have e1 : sumList (l.map F) = (F p).lpSum (sumList ((l.erase p).map F)) :=
      sumList_perm ((List.perm_cons_erase hp).map F)
    have e2 : sumList (l'.map F) = (F p).lpSum (sumList ((l'.erase p).map F)) :=
      sumList_perm ((List.perm_cons_erase hp').map F)
    have hc : sumList ((l.erase p).map F) = sumList ((l'.erase p).map F) := by
      refine WD.lpSum_cancel_right E Ω A w h _ _ (F p) ?_
      rw [WD.lpSum_comm, ← e1, WD.lpSum_comm, ← e2]
      exact heq
    have hlen : (l.erase p).length = n := by
      rw [List.length_erase_of_mem hp, hn]
      rfl
    have := ih (l.erase p) (l'.erase p) hlen (fun q hq => hl q (List.mem_of_mem_erase hq))
      (fun q hq => hl' q (List.mem_of_mem_erase hq)) hc
    exact ((List.perm_cons_erase hp).trans (this.cons p)).trans (List.perm_cons_erase hp').symm
