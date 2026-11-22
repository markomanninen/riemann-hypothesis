module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGLProjections_mul_infiniteAdelicGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)), prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := by
  first | (exact @GlobalTheory.SchurExt.prS_prO_mul_infGL) | (exact GlobalTheory.SchurExt.prS_prO_mul_infGL) | (intros; apply GlobalTheory.SchurExt.prS_prO_mul_infGL <;> assumption)
