module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSubfieldValuationClosure
public import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
public import ReciprocityTheory.SemistableReduction.AlgAll
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subfield_valuation_closure' : ∀ (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (S : Subfield U), ∃ S' : Subfield U, ∀ u, u ∈ S' ↔ ∀ γ : WithZero (Multiplicative ℤ), γ ≠ 0 → ∃ s ∈ S, v (u - s) < γ := by
  first | exact @GlobalTheory.exists_subfield_valuation_closure | exact GlobalTheory.exists_subfield_valuation_closure | (intros; apply GlobalTheory.exists_subfield_valuation_closure <;> assumption)
