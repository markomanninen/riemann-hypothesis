module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInversePreservingAdelicLatticeAtPlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d),
    W.L.IsFullLattice E → ∀ (v : Pl (F := F)) (p : ℕ), (p : 𝓞 F) ∈ v.asIdeal → ∀ c : AF F, IsUnit c →
    ∀ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (M - c • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, ∃ y ∈ GlobalTheory.InertSph.latAt W v, ∃ y' ∈ GlobalTheory.InertSph.latAt W v, z = M *ᵥ y + p • y') →
    ∃ M' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * M' = 1 ∧ M' * M = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M' *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  exact GlobalTheory.InertSph.exists_inv_keeps_latAt
