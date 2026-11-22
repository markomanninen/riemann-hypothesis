module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactElementEigenvaluesUnits
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_element_eigenvalues_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)) (g : H) (p : GLw n w) (s : Fin n → (w.adicCompletion E)ˣ), g.1 = p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹ → IsCompact (closure (Subgroup.zpowers g : Set H)) → ∀ i, Valued.v (s i : w.adicCompletion E) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers | exact GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers | (intros; apply GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers <;> assumption)
