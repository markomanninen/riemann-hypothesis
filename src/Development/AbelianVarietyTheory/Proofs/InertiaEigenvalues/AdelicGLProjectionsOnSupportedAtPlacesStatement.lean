module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGLProjections_on_supportedAtPlaces : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, prS S a g = g ∧ prO S a g = 1) ∧ ∀ g, prS S a g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  first | (exact @GlobalTheory.SchurExt.prS_prO_supS) | (exact GlobalTheory.SchurExt.prS_prO_supS) | (intros; apply GlobalTheory.SchurExt.prS_prO_supS <;> assumption)
