module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRestrictedPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_form_restricted_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (JW₁ : Matrix (Fin d₁) (Fin d₁) E)
    (ι : Matrix (Fin d) (Fin d₁) E), ιᵀ * JW * ι.map σ = JW₁ → ∀ z z' : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (1 : Matrix (Fin n) (Fin n) E) * z * ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) ι)ᵀ)
        ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (1 : Matrix (Fin n) (Fin n) E) * z' * ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) ι)ᵀ) = symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW₁) z z' := by
  first | exact @GlobalTheory.MixedLagrGram.symp_restrict_gram | exact GlobalTheory.MixedLagrGram.symp_restrict_gram | (intros; apply GlobalTheory.MixedLagrGram.symp_restrict_gram <;> assumption)
