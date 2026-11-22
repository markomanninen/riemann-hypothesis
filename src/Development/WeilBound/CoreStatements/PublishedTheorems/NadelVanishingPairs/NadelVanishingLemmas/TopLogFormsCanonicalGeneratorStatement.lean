module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.TopLogFormsCanonicalGenerator

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.top_log_forms_canonical_generator : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp (ZMod p)) (d : ℕ) [SmoothOfRelativeDimension d f] {C : Type} [Fintype C] (E : C → CartierDiv X) {ι : Type} (𝒜 : SncAtlas E d ι), ∃ ω₀ : abelian₂ X.functionField, ω₀ ≠ 0 ∧ ∀ (G : CartierDiv X) (y : X) (η : abelian₂ X.functionField), η ∈ logAt (suppAll E) G d y ↔ ∃ c : X.functionField, (canonical f d + ∑ c, E c + G).RegularAt y c ∧ η = c • ω₀ := by
  first | exact @_root_.GlobalTheory.LogDR.logAt_top_eq_canonical | exact _root_.GlobalTheory.LogDR.logAt_top_eq_canonical | (intros; apply _root_.GlobalTheory.LogDR.logAt_top_eq_canonical <;> assumption)
