module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.RhoLoc

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

theorem UpperTheory.ConvolutionTheory.C.occursIff
    (K : Type) [Field K] [NumberField K] (n : ℕ)
    (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) (w : Pl K) (σ : SmIrr (Gw n w)) :
    Occurs μ V w σ ↔ ∃ f : σ.V →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (σ.ρ g x) = Dp.locOn hV w g (f x) := by
  constructor
  · rintro ⟨f, hf0, hfV, hf⟩
    refine ⟨f.codRestrict V hfV, ?_, ?_⟩
    · intro h
      apply hf0
      exact LinearMap.ext fun x => congrArg Subtype.val (LinearMap.congr_fun h x)
    · intro g x
      apply Subtype.ext
      change f (σ.ρ g x) = Dp.localRepresentationL2 μ w g (f x)
      rw [← Dp.rhoLoc K n μ w g (f x)]
      exact hf g x
  · rintro ⟨f, hf0, hf⟩
    refine ⟨V.subtype ∘ₗ f, ?_, fun x => (f x).2, ?_⟩
    · intro h
      apply hf0
      exact LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun h x)
    · intro g x
      change (f (σ.ρ g x) : LL μ) = rhoL μ w g (f x)
      rw [Dp.rhoLoc K n μ w g]
      exact congrArg Subtype.val (hf g x)
