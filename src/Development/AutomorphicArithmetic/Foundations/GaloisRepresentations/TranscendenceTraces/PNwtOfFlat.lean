module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtOfFlat_of :
    WtFlat → WtUnique → GenBasic → NwtOfFlat := by
  intro hW hU hG Z S p _ _ _
  have hm : IsNwt p (mult p) := ⟨hW p, fun _ _ _ _ _ => rfl⟩
  have hex : ∃ w, IsNwt p w := ⟨mult p, hm⟩
  have hspec : IsNwt p hex.choose := hex.choose_spec
  have hval : nwt p = hex.choose := by
    unfold nwt
    rw [dite_eq_left hex]
  rw [hval]
  refine hU p _ _ hspec.1 hm.1 {s | GenPt s} (hG.1 S) ?_
  intro Ω _ _ z hz
  exact hspec.2 Ω z hz
