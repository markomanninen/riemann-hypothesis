module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtNormal_of :
    NormAff → NwtGlue → WtNormal := by
  intro hAff hGlue Z S p _ hS
  have h : ∃ w, IsNwt p w := by
    refine hGlue p (fun s => ?_)
    obtain ⟨U, hU, hs, hd, hi⟩ := hS s
    obtain ⟨A, w, ho, hr, hw⟩ := hAff p U hU hd hi
    exact ⟨A, w, ho, by rw [hr]; exact hs, hw⟩
  unfold nwt
  rw [dite_eq_left h]
  exact h.choose_spec
