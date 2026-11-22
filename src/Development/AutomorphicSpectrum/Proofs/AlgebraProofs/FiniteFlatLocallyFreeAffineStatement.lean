module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatLocallyFreeAffine
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_locally_free_affine : ∀ {Y S : Scheme.{0}} (g : Y ⟶ S) [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] (s : S), ∃ W : S.Opens, s ∈ W ∧ IsAffineOpen W ∧ GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom (g ∣_ W).appTop.hom := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.exists_affine_finiteFreeHom | exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.exists_affine_finiteFreeHom | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.exists_affine_finiteFreeHom <;> assumption)
