module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualPairIsUnitDetBlocksStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalDictionarySplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceBigCellExistsAdmissibleInverseStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitChoose

theorem isUnit_two_of_not_mem : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    IsUnit (2 : v.adicCompletionIntegers F) := by
  intro F _ _ v h
  have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (2 : 𝓞 F)).2 h
  rwa [map_ofNat] at this

theorem exists_admissible_unipotent_splitPlace_alt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ B d W r s hB hW v hv hψ h2 g hg
  obtain ⟨π₁, π₂, b₁, b₂, hP, hS⟩ := GlobalTheory.T.exists_local_dictionary_splitPlace σ B W r s hB hW v hv hψ
  exact GlobalTheory.T.splitPlace_bigCell_exists_admissible_inverse_alt GlobalTheory.T.exists_dual_pair_isUnit_det_blocks' σ W v hW.skew (isUnit_two_of_not_mem v h2) π₁ π₂ b₁ b₂ hP hS g hg

end GlobalTheory.SplitChoose
