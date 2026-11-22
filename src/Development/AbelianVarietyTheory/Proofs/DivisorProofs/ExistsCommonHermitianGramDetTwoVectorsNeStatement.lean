module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonHermitianGramDetTwoVectorsNe
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNormOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_hermitianGramDetTwoVectors_ne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → E, gram2E σ J x w ≠ 0 ∧ gram2E σ J w y ≠ 0 := by
  first | exact @GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' | exact GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' | (intros; apply GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' <;> assumption)
