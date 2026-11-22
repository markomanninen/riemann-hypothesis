module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacLag

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lagAt {n d m : ℕ} (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
  {u | At (evFin F v) u ∧ ∃ z : Matrix (Fin n) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), u = z * Cᵀ}

def IsLagrAt (σ : E →ₐ[F] E) {d m : ℕ} (W : Spc F E d) (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Prop :=
  IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) W.J) (C.map (compFin F E v))

def HeisInv {σ : E →ₐ[F] E} {n d m : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u ∈ lagAt v C, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
    Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → l φ₁ = l φ

end GlobalTheory.InertVacLag
end
