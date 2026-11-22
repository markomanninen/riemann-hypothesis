module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGaussianVacuaSpanOfVacuumEquations
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGaussEqZero

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_gaussianVacuaSpan_of_vacuumEquations : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), GlobalTheory.VacDatum.IsGaussEq M ψ τ Φ →
      Φ ∈ Submodule.span ℂ {Φ' | ∃ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ),
        f ∈ M.Pol ψ τ ∧ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ Φ' = GlobalTheory.WeilM.pureA F f g} := by
  exact @GlobalTheory.VacFactor.mem_span_of_isGaussEq
