module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSchwartzBruhatCompactSupportNonzero
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceGramDetNeZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsEqAdelicCharMul
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphRankOneTuples
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteComponentCoordinatesAction
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TupOfCv

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartzBruhat_compact_support_nonzero : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι], ∃ f ∈ schwartzBruhatPi (K := F) (ι := ι), HasCompactSupport f ∧ f 0 ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest.exists_compactSupport_ne_zero | exact GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest.exists_compactSupport_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest.exists_compactSupport_ne_zero <;> assumption)
