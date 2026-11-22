module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousDblIncl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAct2DiagonalOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodConstantPolynomialsNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentralCircleOneParameterUnitaryRealPlaceStatement

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.RealLift.Compare

theorem constant_eq_dbl :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (c cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → IsFockMap ψ τ d A C Φ →
    (∀ (g : UG (cA σ) JB) (gd : UG (cA σ) (dbl JB)),
      ((gd : GL (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (β ⊕ β) (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((g : GL β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) 0 0 1 →
      ∀ φ₁ ∈ (adeleClass F).sp κ, ∀ φ₂ ∈ (adeleClass F).sp κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂) →
    ActsBy τ C om Φ (fockAct2 P Q R S) c →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr))) →
    0 < R + S → ∀ w, c w = cd w :=
  compare_of GlobalTheory.T.exists_central_circle_oneParameter_unitary_realPlace GlobalTheory.VacuumWeight.fockAct2_diagonal_one GlobalTheory.tprod_one_pol_ne_zero

end GlobalTheory.RealLift.Compare
