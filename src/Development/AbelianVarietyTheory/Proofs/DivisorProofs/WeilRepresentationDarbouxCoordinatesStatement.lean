module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_darboux_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (m n : ℕ) (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ)
    (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) →* Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ p w, ∀ φ ∈ schA F κ, om p (co.rho ψ w φ) = co.rho ψ (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p w) (om p φ)) →
    ∃ M : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ p h, ∀ φ ∈ schA F κ,
        om p (schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) ∧
      ∀ h, Continuous fun p => M p h := by
  first | exact @GlobalTheory.ArchTransportDir.archDir_transport | exact GlobalTheory.ArchTransportDir.archDir_transport | (intros; apply GlobalTheory.ArchTransportDir.archDir_transport <;> assumption)
