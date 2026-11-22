module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveChainsQuasiIsoOfLocallySurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechConerve_chains_quasiIso_of_locallySurjective : ∀ (R : Type) [CommRing R] (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (Ψ.map g).unop → QuasiIso ((chains R).map (lev Ψ (coAug g))) := by
  first | (exact @GlobalTheory.EtC.chains_cech_conerve_quasiIso) | (exact GlobalTheory.EtC.chains_cech_conerve_quasiIso) | (intros; apply GlobalTheory.EtC.chains_cech_conerve_quasiIso <;> assumption)
