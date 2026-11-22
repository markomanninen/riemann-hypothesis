module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentralCircleOneParameterUnitaryRealPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_circle_oneParameter_unitary_realPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type)
    [Fintype β] [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (w₀ : InfinitePlace F), IsCMExt F E σ →
    ∃ z : ℝ → (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ, ∃ γ ∈ RLines (σ := σ) J,
      IsGen τ C γ (fun w => if w = w₀ then Complex.I • (1 : Mat R S) else 0) ∧
      (∀ t : ℝ, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (z t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • (1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) ∧
      (∀ t : ℝ, At (evI F) ((z t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1)) ∧
      ∀ (t : ℝ) (w : InfinitePlace F), piInf (τ w) (z t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = if w = w₀ then Complex.exp (t * Complex.I) else 1 := by
  first | exact @GlobalTheory.CentralLine.exists_central_line | exact GlobalTheory.CentralLine.exists_central_line | (intros; apply GlobalTheory.CentralLine.exists_central_line <;> assumption)
