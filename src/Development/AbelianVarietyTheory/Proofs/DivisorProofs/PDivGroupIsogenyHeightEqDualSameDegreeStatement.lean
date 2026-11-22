module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegree
public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → G.height = H.height ∧ IsIsog (dualHom G H q) ∧ ∀ e, HasLogDeg q e → HasLogDeg (dualHom G H q) e := by
  first | exact @GlobalTheory.Dieu.height_eq_and_dual_isog | exact GlobalTheory.Dieu.height_eq_and_dual_isog | (intros; apply GlobalTheory.Dieu.height_eq_and_dual_isog <;> assumption)
