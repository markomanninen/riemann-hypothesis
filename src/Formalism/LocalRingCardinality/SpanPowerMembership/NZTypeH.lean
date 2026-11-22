module

public import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
public import Mathlib
public import Formalism.CyclotomicNorms.StatementT
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {R : Ranks} (H : Host R)

structure Lbl where
  fA : ∀ k, (ZMod (H.g k))[X]
  fB : ∀ k, (ZMod (H.g k))[X]
  ne : ∀ k, fA k ≠ fB k
  okA : ∀ k, (fA k).Monic ∧ (fA k).natDegree = R.r ∧ (fA k).coeff 0 ≠ 0
  okB : ∀ k, (fB k).Monic ∧ (fB k).natDegree = R.r ∧ (fB k).coeff 0 ≠ 0
  good : ∀ k (PP J : Type) (t : PP → Bool), (∃ v, t v = true) → (∃ v, t v = false) →
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (fun v => if t v then fA k else fB k) (fun (_ : PP) (_ : J) => (1 : (ZMod (H.g k))ˣ))

variable {H} (Lb : Lbl H)



variable (H) (what₂ : Rows.Data R) (h : NHyp H what₂)

section Field

variable (K : Type) [Field K] [CharZero K]

end Field


end Formalism.BasicNotions.Examples₂.NZ
