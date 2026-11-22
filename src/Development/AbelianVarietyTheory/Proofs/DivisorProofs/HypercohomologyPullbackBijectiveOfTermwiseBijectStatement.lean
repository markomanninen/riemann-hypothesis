module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfTermwiseBiject
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomologyPullback_bijective_of_termwise_bijective : ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ n, Injective (I.X n)) → ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L), (∀ p n, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I n)) → ∀ n, Function.Bijective (cpull g I n) := by
  first | (exact @GlobalTheory.LevelCx.main) | (exact GlobalTheory.LevelCx.main) | (intros; apply GlobalTheory.LevelCx.main  <;> assumption)
