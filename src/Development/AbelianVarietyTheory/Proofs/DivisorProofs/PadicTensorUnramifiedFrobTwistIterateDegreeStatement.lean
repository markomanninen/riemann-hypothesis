module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicTensorUnramifiedFrobTwistIterateDegree
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicTensorUnramifiedFrobTwist_iterate_degree : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r → ∀ x : KQ p K r, (⇑(sigKQ p K r))^[r] x = x := by
  first | exact @GlobalTheory.LKRes.sigKQ_iterate_self | exact GlobalTheory.LKRes.sigKQ_iterate_self | (intros; apply GlobalTheory.LKRes.sigKQ_iterate_self; all_goals assumption)
