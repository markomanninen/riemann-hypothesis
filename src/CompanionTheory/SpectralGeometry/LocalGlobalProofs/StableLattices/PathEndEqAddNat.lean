module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv

@[expose] public section

namespace GlobalTheory.CompanionTheory.RgPath

open CompanionTheory.RgExh

theorem pathEnd_eq_add_nat {n : ℕ} (ss : List (_root_.Fin n)) :
    ∀ χ : _root_.Fin n → ℂ, ∃ m : _root_.Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
      ∀ a, a ∈ ss → 1 ≤ m a := by
  induction ss with
  | nil =>
    intro χ
    refine ⟨0, ?_, by simp⟩
    funext a
    change χ a = χ a + (↑(0 : ℕ) : ℂ)
    simp
  | cons s ss ih =>
    intro χ
    obtain ⟨m', h, hm⟩ := ih (χ + Pi.single s 1)
    refine ⟨m' + Pi.single s 1, ?_, ?_⟩
    · change pathEnd (χ + Pi.single s 1) ss = _
      rw [h]
      funext a
      by_cases e : a = s
      · subst a
        simp only [Pi.add_apply, Pi.single_eq_same, Nat.cast_add, Nat.cast_one]
        ac_rfl
      · simp only [Pi.add_apply, Pi.single_eq_of_ne e, add_zero]
    · intro a ha
      rcases List.mem_cons.1 ha with e | ha
      · subst a
        simpa only [Pi.add_apply, Pi.single_eq_same] using Nat.succ_le_succ (Nat.zero_le (m' s))
      · exact (hm a ha).trans (Nat.le_add_right _ _)

theorem pathEndNat (n : ℕ) (χ : _root_.Fin n → ℂ) (ss : List (_root_.Fin n)) :
    ∃ m : _root_.Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
      ∀ a, a ∈ ss → 1 ≤ m a :=
  pathEnd_eq_add_nat ss χ

end GlobalTheory.CompanionTheory.RgPath
