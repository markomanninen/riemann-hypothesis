module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorsProductCompatible
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenInjectiveExtends
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSurjectiveExtends
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_operators_product_compatible : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.SurjOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    (∀ v, ev v (stdInd F κ v) ≠ 0) →
    ∀ v, ∀ χ ∈ SB (κ → Fv F v), ∃ ψ ∈ SB (κ → Fv F v), ev v ψ = χ := by
  first | exact @GlobalTheory.EvOnto.ev_surjOn_SB | exact GlobalTheory.EvOnto.ev_surjOn_SB | (intros; apply GlobalTheory.EvOnto.ev_surjOn_SB <;> assumption)
