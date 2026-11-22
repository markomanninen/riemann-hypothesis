module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattices_agree_almost_everywhere : ∀ (D : D7) (S : HSp D) (L M : Lat S), Submodule.IsFullLattice D.host.E L → Submodule.IsFullLattice D.host.E M → ∃ T : Finset (Pl D), ∀ v, v ∉ T → latV S L (· = v) = latV S M (· = v) := by
  intro D S L M hL hM
  first
  | exact GlobalTheory.FinPl.latV_eq_off_finite D S L M hL hM
  | exact GlobalTheory.FinPl.latV_eq_off_finite D S L M hL hM.toIsLattice
