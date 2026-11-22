module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierMemSchwartzTotallyReal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPoissonSummationAnyHaar
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversion
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualHaarMeasureInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicFourier_mem_schwartz_totallyReal : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), μ.IsAddHaarMeasure → ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ := by
  first | exact @GlobalTheory.AdelicFourierSch.fourier_mem_schA | exact GlobalTheory.AdelicFourierSch.fourier_mem_schA | (intros; apply GlobalTheory.AdelicFourierSch.fourier_mem_schA <;> assumption)
