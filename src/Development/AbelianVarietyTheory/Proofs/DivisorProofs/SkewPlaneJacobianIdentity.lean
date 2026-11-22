module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementTorusPart

@[expose] public section

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

noncomputable section

namespace GlobalTheory.ThK.CuspTransfer.Smooth


end GlobalTheory.ThK.CuspTransfer.Smooth

open GlobalTheory.SiegelSet (IsRealLine)
open GlobalTheory.Orb (archMat IsSmoothRealFam)

namespace GlobalTheory.ThK.CuspTransfer.Smooth

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem line_fam (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : IsSmoothRealFam γ ∧ Continuous γ := by
  obtain ⟨w, τ, Z, -, hγ⟩ := hγ
  choose y e1 e2 using hγ
  obtain rfl : γ = fun t => embArch σ J w (y t) := funext e1
  exact GlobalTheory.Orb.isSmoothRealFam_embArch h τ fun i j => by
    simp only [e2]; exact GlobalTheory.Orb.contDiff_exp_smul_entry Z i j





end GlobalTheory.ThK.CuspTransfer.Smooth


end
