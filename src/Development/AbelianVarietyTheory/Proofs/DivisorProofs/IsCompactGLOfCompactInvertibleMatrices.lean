module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

theorem isCompact_GL_of_invSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (T : Set (Lie E n)),
    IsCompact T → T ⊆ invSet E n →
      IsCompact {y : GL (Fin n) (Cinf E) | toL (y : Matrix (Fin n) (Fin n) (Cinf E)) ∈ T} := by
  intro E _ _ n T hT hsub
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT
  have hu : Continuous fun p : T =>
      (IsUnit.unit (hsub p.2 : IsUnit (Matrix.of p.1)) : GL (Fin n) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have hinv : ContDiffOn ℝ ∞ (GlobalTheory.ConstTermSmooth.invM (E := E) (a := n)) (invSet E n) := by
      have h1 : ContDiffOn ℝ ∞ (fun y : Lie E n => Ring.inverse (Matrix.of y).det) (invSet E n) := fun y hy => by
        obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hy
        have := contDiffAt_ringInverse ℝ (n := ∞) u
        rw [hu] at this
        exact (this.comp y contDiff_det.contDiffAt).contDiffWithinAt
      refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
      have h2 : ContDiff ℝ ∞ fun y : Lie E n => (Matrix.of y).adjugate i j := by
        simp only [Matrix.adjugate_apply]
        have h3 : ContDiff ℝ ∞ fun y : Lie E n => (Function.update y j (Pi.single i 1) : Lie E n) := by
          refine contDiff_pi.2 fun k => ?_
          by_cases h : k = j
          · subst h; simpa using contDiff_const
          · simpa [Function.update_of_ne h] using contDiff_apply ℝ _ k
        exact contDiff_det.comp h3
      exact h1.mul h2.contDiffOn
    have := hinv.continuousOn.comp_continuous
      (f := fun p : T => (p : Lie E n)) continuous_subtype_val fun p => hsub p.2
    refine Continuous.congr this fun p => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  convert isCompact_range hu using 1
  ext y
  constructor
  · intro hy
    exact ⟨⟨toL (y : Matrix (Fin n) (Fin n) (Cinf E)), hy⟩, Units.ext rfl⟩
  · rintro ⟨p, rfl⟩
    exact p.2

end GlobalTheory.WhitBump
