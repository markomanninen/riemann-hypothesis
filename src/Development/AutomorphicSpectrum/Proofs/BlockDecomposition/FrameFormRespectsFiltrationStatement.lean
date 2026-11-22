module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRespectsFiltration
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_form_respects_filtration : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame (Φ := Φ) d) (σ : ∀ T : C, E.D ⟶ T) (j q : ℕ) (I : Fin j → Fin d) (x : Φ.A.obj E.D), x ∈ (Fil q).S E.D →
    ∀ s : ComposableArrows C j, E.form σ I x s ∈ (Fil ((j + q : ℕ) : ℤ)).S (s.obj (Fin.last j)) := by
  intro R _ C _ Φ Fil hF d E σ j q I x hx s
  have prod_fil_mem (T : C) (n : ℕ) (f : Fin n → Φ.A.obj T)
      (hf : ∀ k, f k ∈ (Fil 1).S T) : ∏ k, f k ∈ (Fil (n : ℤ)).S T := by
    induction n with
    | zero =>
      rw [hF.top ((0 : ℕ) : ℤ) (by simp) T]
      exact Submodule.mem_top
    | succ n ih =>
      rw [Fin.prod_univ_succ]
      simpa only [Nat.add_comm 1 n] using
        hF.mul 1 n T (hf 0) (ih (fun k => f k.succ) fun k => hf k.succ)
  refine hF.mul j q _ (prod_fil_mem _ j _ fun k => (Fil 1).map_mem _ ?_) ((Fil q).map_mem (σ _) hx)
  rw [hF.one]
  exact E.mem _ _ _
