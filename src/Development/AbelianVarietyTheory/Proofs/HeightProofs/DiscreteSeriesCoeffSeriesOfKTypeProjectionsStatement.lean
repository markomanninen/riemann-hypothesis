module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoeffSeriesOfKTypeProjections
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesCoeffSeries_of_kTypeProjections : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ f : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun ε e →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (x : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, IsKFin ε σ (x j)) ∧
        ∀ y ∈ UJset ε, (∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) = ∑ j, ℓ j (σ y (x j))) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.SmoothGlob.lieSet ε) (UJset ε) σ f := by
  first | exact @GlobalTheory.TypeSum.KSeries.hasTypeAll_of_kTypes | exact GlobalTheory.TypeSum.KSeries.hasTypeAll_of_kTypes | (intros; apply GlobalTheory.TypeSum.KSeries.hasTypeAll_of_kTypes <;> assumption)
