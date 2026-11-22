module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardRealEmbeddingsEqFinrank
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup

@[expose] public section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_real_embeddings_eq_finrank : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Finite (F →+* ℝ) ∧ Nat.card (F →+* ℝ) = Module.finrank ℚ F := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings <;> assumption)
