module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionSubMemSpanPowSucc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaAction_sub_mem_span_pow_succ : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ g ∈ W.GKs, ∀ (k : ℕ), ∀ a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ k, W.γA (W.resΓ g) a - a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ (k + 1) := by
  intro D HW l _ K s LL h W g hg
  have hχ := (W.GKs_def g).1 hg
  rw [← W.χΓ_res g] at hχ
  have hs : (1 : WithTop ℚ) ≤ (W.s : WithTop ℚ) := by exact_mod_cast W.s_pos
  obtain ⟨c, hc⟩ := GlobalTheory.GamFilt.exists_eq_one_add (D.loc l) LL _ (hs.trans hχ)
  exact GlobalTheory.GamFilt.letγ_sub_mem (W.γ₀ (W.resΓ g)) l c
    (W.γ₀_X _).1 ((W.γ₀_X _).2.trans hc)
