module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicProduct_hasFiniteLength_GL : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), HasFiniteLength π₁ → HasFiniteLength π₂ → IsSmooth π₁ → IsSmooth π₂ → HasFiniteLength (prod₂ π₁ π₂) := by
  first | exact @GlobalTheory.ProdLength.prod₂_hasFiniteLength | exact GlobalTheory.ProdLength.prod₂_hasFiniteLength | (intros; apply GlobalTheory.ProdLength.prod₂_hasFiniteLength <;> assumption)
