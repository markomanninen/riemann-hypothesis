module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterTrivialOnCongruence
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNontrivialHeckeChar

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_character_trivial_on_congruence : ∀ (F : Type) [Field F] [NumberField F] (φ : (AdeleRing (𝓞 F) F)ˣ →* Circle),
    Continuous φ → (∀ b, φ b = 1 ∨ φ b = -1) → (∀ b : (AdeleRing (𝓞 F) F)ˣ, (b : AdeleRing (𝓞 F) F).2 = 1 → φ b = 1) →
    ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ∀ b : (AdeleRing (𝓞 F) F)ˣ,
      (∃ t ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, (b : AdeleRing (𝓞 F) F).2 = 1 + (n : FiniteAdeleRing (𝓞 F) F) * t) →
      (∃ t ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, ((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 + (n : FiniteAdeleRing (𝓞 F) F) * t) →
      φ b = 1 := by
  first | exact @GlobalTheory.HeckeSignLevel.sign_char_trivial_on_congruence | exact GlobalTheory.HeckeSignLevel.sign_char_trivial_on_congruence | (intros; apply GlobalTheory.HeckeSignLevel.sign_char_trivial_on_congruence <;> assumption)
