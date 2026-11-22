module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumStabilizerGaussDecompositionBigCell
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumStabilizer_gaussDecomposition_bigCell : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v, GlobalTheory.DblVac.BigCell W v g →
      ∃ q ∈ GlobalTheory.DblVac.KD σ W v, q ∈ GlobalTheory.DblVac.PAnti σ W ∧ ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ g = q * p := by
  first | exact @GlobalTheory.DblVacGauss.gauss_decomp | exact GlobalTheory.DblVacGauss.gauss_decomp | (intros; apply GlobalTheory.DblVacGauss.gauss_decomp <;> assumption)
