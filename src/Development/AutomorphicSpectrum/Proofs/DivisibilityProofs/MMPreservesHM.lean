module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PureEqPureA

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct SchwartzMap LineDeriv ContDiff Matrix Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.Lie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] in
private theorem conj_extensionEmbedding_of_isReal {w : InfinitePlace F} (hw : w.IsReal) (y : w.Completion) :
    starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w y) =
      InfinitePlace.Completion.extensionEmbedding w y := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw y]
  exact Complex.conj_ofReal _

theorem piInf_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piInf τ (cA σ x) = (starRingEnd ℂ) (piInf τ x) := by
  obtain ⟨hF, -, -, hστ⟩ := h
  induction x using TensorProduct.inductionOn with
  | tmul a e =>
    rw [show cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e by simp [cA]]
    change InfinitePlace.Completion.extensionEmbedding w (evInf F w a) * τ.1 (σ e) =
      starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w (evInf F w a) * τ.1 e)
    rw [map_mul, conj_extensionEmbedding_of_isReal (hF.isReal w), starRingEnd_apply, hστ]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [NumberField E] in
theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  simp [piInf, compInf, infEmb, inclR]

end GlobalTheory.CompanionTheory.Ar.RT.Lie

end
