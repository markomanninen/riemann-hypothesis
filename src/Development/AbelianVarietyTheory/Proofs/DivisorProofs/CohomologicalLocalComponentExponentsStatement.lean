module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotientsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockIsTheRun
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomological_local_component_exponents : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd →
  ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ τ, P.HasInfChar τ (m τ)) → (∀ τ, (m τ).Nodup) →
  ∀ f : ℂ, (∀ τ, ∀ z ∈ m τ, ∃ k : ℤ, z = f + k) →
  ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w σ →
    ∀ S : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ s ∈ S, ‖(s : ℂ)‖ = 1 := by
  first | exact @GlobalTheory.TempSat.norm_satake_eq_one | exact GlobalTheory.TempSat.norm_satake_eq_one | (intros; apply GlobalTheory.TempSat.norm_satake_eq_one <;> assumption)
