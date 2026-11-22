module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_law_good_of_field_embedding : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h, S.LawGood emb lam h := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF hS h
  exact GlobalTheory.Mem.LatGood.lawGood S emb σ lam hF hS hS.lsh_full_lat h
