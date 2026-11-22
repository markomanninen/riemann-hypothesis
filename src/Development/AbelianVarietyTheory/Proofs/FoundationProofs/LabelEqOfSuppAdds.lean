module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEqStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionActionOnFixK1
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUpperMulInc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterIrreducibleLabel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntertwinerUnipotentInvariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLawsStatement
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPrincipalCongruenceFixedVectorsIff

@[expose] public section

noncomputable section

namespace GlobalTheory.GLp.Supp

open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders TensorProduct GlobalTheory.GLq.Opp MonoidAlgebra
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem alg_apply {G U : Type} [Group G] [Fintype G] [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ G U)
    (a : MonoidAlgebra ℂ G) (w : U) : ρ.asAlgebraHom a w = ∑ x, a.coeff x • ρ x w := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single x c =>
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Finsupp.single_eq_of_ne hy]
    · simp

theorem entN_par {a b : ℕ} (x : Gn g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (y : Gn g b) (i j : ℕ) :
    (i < a → j < a → entN (par finSumFinEquiv x B y).val i j = entN x.val i j) ∧
    (a ≤ i → j < a → entN (par finSumFinEquiv x B y).val i j = 0) ∧
    (entN (par finSumFinEquiv x B y).val (a + i) (a + j) = entN y.val i j) ∧
    (B = 0 → i < a → a ≤ j → entN (par finSumFinEquiv x B y).val i j = 0) := by
  refine ⟨fun hi hj => ?_, fun hi hj => ?_, ?_, fun hB hi hj => ?_⟩
  · have := par_apply finSumFinEquiv x B y (.inl ⟨i, hi⟩) (.inl ⟨j, hj⟩)
    rw [entN, entN, dite_eq_left ⟨by omega, by omega⟩, dite_eq_left ⟨hi, hj⟩]
    exact this
  · unfold entN
    split_ifs with h
    · have := par_apply finSumFinEquiv x B y (.inr ⟨i - a, by omega⟩) (.inl ⟨j, hj⟩)
      rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] at this
      rw [← this]
      exact congrArg₂ _ (Fin.ext (by simp; omega)) (Fin.ext (by simp))
    · rfl
  · unfold entN
    by_cases h : i < b ∧ j < b
    · rw [dite_eq_left ⟨by omega, by omega⟩, dite_eq_left h]
      exact par_apply finSumFinEquiv x B y (.inr ⟨i, h.1⟩) (.inr ⟨j, h.2⟩)
    · rw [dite_eq_right (by omega), dite_eq_right h]
  · unfold entN
    split_ifs with h
    · have := par_apply finSumFinEquiv x B y (.inl ⟨i, hi⟩) (.inr ⟨j - a, by omega⟩)
      subst hB
      rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] at this
      rw [← this]
      exact congrArg₂ _ (Fin.ext (by simp)) (Fin.ext (by simp; omega))
    · rfl

theorem ext_entN {n : ℕ} {x y : Gn g n} (h : ∀ i j : ℕ, i < n → j < n → entN x.val i j = entN y.val i j) :
    x = y := by
  ext i j
  rw [← ParInd.entN_self x.val, ← ParInd.entN_self y.val, h _ _ i.2 j.2]

section Local

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def repK (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : Representation ℂ (Gn g n) (fixK1 π) where
  toFun x := (π (lift g n x)).restrict fun _ hv => padicIntGL_smul_mem_principalCongruenceFixed π hv _
  map_one' := LinearMap.ext fun v => Subtype.ext (lift_one_apply π v.2)
  map_mul' x y := LinearMap.ext fun v => Subtype.ext (lift_mul_apply π v.2 x y)

theorem repK_red (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (k : GL (Fin n) ℤ_[g]) (v : fixK1 π) :
    (repK π (red g n k) v : V) = π (inc g n k) v :=
  inc_eq_of_red_eq π v.2 (red_invFun _)

theorem repK_alg (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a : MonoidAlgebra ℂ (Gn g n)) (v : fixK1 π) :
    ((repK π).asAlgebraHom a v : V) = actK π a v := by
  rw [alg_apply, actK, LinearMap.sum_apply, Submodule.coe_sum]
  rfl

end Local

section Ind

variable {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def parZ (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g]) : GL (Fin (a + b)) ℤ_[g] where
  val := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val B 0 y.val)
  inv := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (x⁻¹).val
    (-((x⁻¹).val * B * (y⁻¹).val)) 0 (y⁻¹).val)
  val_inv := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [← Matrix.mul_assoc]
  inv_val := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc]

theorem parZ_apply (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g])
    (i j : Fin a ⊕ Fin b) : (parZ x B y).val (finSumFinEquiv i) (finSumFinEquiv j) =
      Matrix.fromBlocks x.val B 0 y.val i j := by
  simp [parZ]

theorem red_parZ (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g]) :
    red g _ (parZ x B y) =
      par finSumFinEquiv (red g a x) (B.map (PadicInt.toZMod (p := g))) (red g b y) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [par_apply, ParInd.red_val, Matrix.map_apply, parZ_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp [ParInd.red_val]

theorem exists_dual_right (z : W ⊗[ℂ] W') (hz : z ≠ 0) : ∃ P : W ⊗[ℂ] W' →ₗ[ℂ] W, P z ≠ 0 ∧
    ∀ (A : W →ₗ[ℂ] W) (y : W ⊗[ℂ] W'), P (TensorProduct.map A LinearMap.id y) = A (P y) := by
  let β := Module.Basis.ofVectorSpace ℂ W'
  have h1 : TensorProduct.equivFinsuppOfBasisRight β z ≠ 0 := by simpa using hz
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h1
  refine ⟨Finsupp.lapply i ∘ₗ (TensorProduct.equivFinsuppOfBasisRight β).toLinearMap, hi, fun A y => ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem exists_dual_left (z : W ⊗[ℂ] W') (hz : z ≠ 0) : ∃ P : W ⊗[ℂ] W' →ₗ[ℂ] W', P z ≠ 0 ∧
    ∀ (A : W' →ₗ[ℂ] W') (y : W ⊗[ℂ] W'), P (TensorProduct.map LinearMap.id A y) = A (P y) := by
  obtain ⟨P, h1, h2⟩ := exists_dual_right (TensorProduct.comm ℂ W W' z) (by simpa using hz)
  refine ⟨P ∘ₗ (TensorProduct.comm ℂ W W').toLinearMap, h1, fun A y => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← h2]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

end Ind

end GlobalTheory.GLp.Supp
