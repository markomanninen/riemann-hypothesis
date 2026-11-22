module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtPt_of :
    WtExt → PtCommon → WtPt := by
  intro hE hC Z S p _ w hw Ω Ω' _ _ _ _ z z' h
  obtain ⟨L, _, _, a, a', ha⟩ := hC Z Ω Ω' z z' h
  rw [← hE p w hw Ω L z a, ← hE p w hw Ω' L z' a', ha]
