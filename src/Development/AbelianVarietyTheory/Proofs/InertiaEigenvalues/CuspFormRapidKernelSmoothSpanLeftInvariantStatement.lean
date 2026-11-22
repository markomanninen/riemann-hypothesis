module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanLeftInvariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormRapidKernelSmoothSpan_left_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ F ∈ GlobalTheory.JSW.mspanR π,
    ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g := by
  first | exact @GlobalTheory.JSW.mspanR_left_invariant | exact GlobalTheory.JSW.mspanR_left_invariant | (intros; apply GlobalTheory.JSW.mspanR_left_invariant <;> assumption)
