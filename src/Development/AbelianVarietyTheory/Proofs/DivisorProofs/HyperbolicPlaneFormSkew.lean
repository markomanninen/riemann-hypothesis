module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutingAlgebrasFiniteSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GelfandTransposeEqOfInvariantWords
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMemStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverseStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBoundTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedUnip
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFiniteMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteModuleGradedQuantumDet

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC

open GlobalTheory.SmoothForms (gelfA)
open Formalism.REAL (GlRel qdet)

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem qdet_mem {B : Type} [Ring B] [Algebra ℂ B] {m : ℕ} (X : Fin m → Fin m → B) (S : Subalgebra ℂ B)
    (hS : ∀ a b, X a b ∈ S) (u : ℂ) : qdet X u ∈ S := by
  unfold qdet Formalism.REAL.qminor
  refine S.sum_mem fun π _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  unfold Formalism.REAL.Tm
  refine S.add_mem ?_ (hS _ _)
  split_ifs
  exacts [S.algebraMap_mem _, S.zero_mem]

end General

end GlobalTheory.LeviHC

end
