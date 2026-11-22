module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormPrincipleOfIsCyclic
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasseNormPrinciple_of_isCyclic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsGalois F E → IsCyclic (E ≃ₐ[F] E) → NP F E := by
  first | exact @GlobalTheory.CNorm.np_cyclic | exact GlobalTheory.CNorm.np_cyclic | (intros; apply GlobalTheory.CNorm.np_cyclic <;> assumption)
