module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzTensorNeZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)), ∀ φ ∈ SB (κ → Fv F v), φ ≠ 0 →
    ∃ r : (κ → AF F) → ℂ, Rest (evFin F v) φ r ∧ tens (evFin F v) φ r ≠ 0 := by
  first | exact @GlobalTheory.InertSph.exists_rest_tens_ne_zero | exact GlobalTheory.InertSph.exists_rest_tens_ne_zero | (intros; apply GlobalTheory.InertSph.exists_rest_tens_ne_zero <;> assumption)
