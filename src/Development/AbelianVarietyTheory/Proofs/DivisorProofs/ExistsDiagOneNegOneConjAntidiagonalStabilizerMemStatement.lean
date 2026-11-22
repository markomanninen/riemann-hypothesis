module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d)
    (v : Pl (F := F)), ∃ w₀ ∈ GlobalTheory.DblVac.KD σ W v, ∀ q ∈ GlobalTheory.DblVac.KD σ W v, q ∈ GlobalTheory.DblVac.PAnti σ W →
      w₀ * q * w₀⁻¹ ∈ GlobalTheory.DblVac.KD σ W v ∧ w₀ * q * w₀⁻¹ ∈ GlobalTheory.DblVac.PDiag σ W := by
  first | exact @GlobalTheory.DblVacFlip.flipPt_conj_anti_diag | exact GlobalTheory.DblVacFlip.flipPt_conj_anti_diag | (intros; apply GlobalTheory.DblVacFlip.flipPt_conj_anti_diag <;> assumption)
