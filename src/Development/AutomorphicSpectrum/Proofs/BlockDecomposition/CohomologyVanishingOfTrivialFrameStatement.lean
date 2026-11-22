module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingOfTrivialFrame
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishing_of_trivial_frame : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (E : Frame (Φ := Φ) 0) (F : C ⥤ ModuleCat.{0} R),
    Subsingleton (F.obj E.D) → ∀ n, Subsingleton (CH.H F n) := by
  intro R _ C _ Φ E F hD n
  have hInitial : Limits.IsInitial E.D := by
    refine Limits.IsInitial.ofUniqueHom (fun T => Classical.choice (E.ne T)) ?_
    intro T f
    obtain ⟨g, -, hg⟩ := E.bij f (fun _ => 0) (fun i => i.elim0)
    exact (hg _ (fun i => i.elim0)).trans (hg _ (fun i => i.elim0)).symm
  obtain ⟨-, -, hex0, hex⟩ := CrystallineSemistableComparison.P.initial F E.D hInitial
  have key : ∀ x : CH.H F n, x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x
    refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).2.1 a ha).2 ?_
    cases n with
    | zero =>
      obtain ⟨m, hm⟩ := hex0 a ha
      rw [one_smul] at hm
      have hm0 : m = 0 := Subsingleton.elim _ _
      rw [hm0, map_zero] at hm
      exact hm.symm
    | succ n =>
      obtain ⟨y, hy⟩ := hex n a ha
      rw [one_smul] at hy
      exact ⟨y, hy⟩
  exact ⟨fun x y => by rw [key x, key y]⟩
