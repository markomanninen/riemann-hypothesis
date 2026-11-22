module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod

@[expose] public section

open Matrix Finset
open PositivityTheory.RgBcC.RealD (epow gelA)

namespace GlobalTheory.CompanionTheory.ModelS

theorem epow_eq_pow_of {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    epow E m a b = ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero =>
      change (if a = b then 1 else 0) = _
      simp only [pow_zero, Matrix.one_apply]
  | succ m ih =>
      change (∑ c, E a c * epow E m c b) = _
      simp only [pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem gelA_central : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E →
    ∀ (m : ℕ) (a b : Fin n), gelA E m * E a b = E a b * gelA E m := by
  intro n V _ _ E hE m a b
  rw [eq_comm, ← sub_eq_zero]
  delta gelA
  simp only [epow_eq_pow_of]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [GlobalTheory.SmoothForms.comm_pow_of_apply E hE, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self]

end GlobalTheory.CompanionTheory.ModelS
