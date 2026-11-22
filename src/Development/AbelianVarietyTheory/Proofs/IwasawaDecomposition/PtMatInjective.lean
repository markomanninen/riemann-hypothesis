module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob Formalism.MainNotions.S

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

theorem ptEntry_inj : ∀ (bs cs : List (E × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → (∀ b ∈ cs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    (bs.map Prod.snd).sum = (cs.map Prod.snd).sum →
    (∀ a < (bs.map Prod.snd).sum, ∀ b < (bs.map Prod.snd).sum, ptEntry bs a b = ptEntry cs a b) → bs = cs
  | [], [], _, _, _, _ => rfl
  | [], (t, s) :: cs, _, h, e, _ => by
    have := (h (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e
    omega
  | (t, s) :: bs, [], h, _, e, _ => by
    have := (h (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e
    omega
  | (t, s) :: bs, (t', s') :: cs, h, h', e, k => by
    have ht : t ≠ 0 := (h (t, s) (by simp)).1
    have hs : 1 ≤ s := (h (t, s) (by simp)).2
    have hs' : 1 ≤ s' := (h' (t', s') (by simp)).2
    simp only [List.map_cons, List.sum_cons] at e k
    have k0 := k 0 (by omega) (s - 1) (by omega)
    simp only [ptEntry] at k0
    rw [ite_eq_left (by omega), ite_eq_left (by omega)] at k0
    have hss : s = s' ∧ t = t' := by
      split_ifs at k0
      · exact ⟨by omega, k0⟩
      · exact absurd k0 ht
      · omega
      · exact absurd k0 ht
    rcases hss with ⟨rfl, rfl⟩
    apply congrArg (List.cons (t, s))
    refine ptEntry_inj bs cs (fun b hb => h b (by simp [hb])) (fun b hb => h' b (by simp [hb])) (by omega)
      fun a ha b hb => ?_
    have shifted := k (a + s) (by omega) (b + s) (by omega)
    have outside : ¬ (a + s < s ∧ b + s < s) := by omega
    have inside : s ≤ a + s ∧ s ≤ b + s := by omega
    simpa only [ptEntry, ite_eq_right outside, ite_eq_left inside, Nat.add_sub_cancel] using shifted

theorem ptMat_injective {m : ℕ} : Function.Injective (ptMat : Point E m → Matrix (Fin m) (Fin m) E) := by
  intro w w' h
  refine Subtype.ext (ptEntry_inj _ _ w.2.1 w'.2.1 (w.2.2.trans w'.2.2.symm) fun a ha b hb => ?_)
  rw [w.2.2] at ha hb
  exact congrFun (congrFun h ⟨a, ha⟩) ⟨b, hb⟩

variable [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E} {T' : E}
  {P : Matrix (Fin n) (Fin (r + 1)) E}

end GlobalTheory.IntTerm
