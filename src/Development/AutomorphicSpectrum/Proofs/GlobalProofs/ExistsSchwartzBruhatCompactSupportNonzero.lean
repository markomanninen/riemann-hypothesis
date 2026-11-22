module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceGramDetNeZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsEqAdelicCharMul
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphRankOneTuples
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteComponentCoordinatesAction
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TupOfCv
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest

open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing

theorem exists_compactSupport_ne_zero :
    ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι],
      ∃ f ∈ schwartzBruhatPi (K := F) (ι := ι), HasCompactSupport f ∧ f 0 ≠ 0 := by
  intro F _ _ ι _ _
  obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (0 : ι → 𝔸[F])
  obtain ⟨r, -, -, hr0, hrU, hrS⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.SdExist.exists_bump (K := F) 0 U hU
  refine ⟨_, hrS, HasCompactSupport.intro hUc fun x hx => ?_, ?_⟩
  · have : r x = 0 := by
      by_contra h
      exact hx (hrU x h)
    simp [this]
  · exact_mod_cast hr0.ne'

end GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest
