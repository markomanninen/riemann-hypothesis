module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgHomog

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_sep :
    ∀ {C K : Type} [CommRing C] [IsLocalRing C] [CommRing K] [Algebra C K] {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P), IsNoetherianRing (lauSub P) → ⨅ N : ℕ, vertex h ^ N = ⊥ := by
  intro C K _ _ _ _ P _ h hN
  classical
  rw [eq_bot_iff]
  intro p hp
  rw [Submodule.mem_iInf] at hp
  let comp : lauSub P → ℤ → lauSub P := fun x j =>
    ⟨AddMonoidAlgebra.single j (x.1.coeff j), single_mem_lauSub P (x.2 j)⟩
  have coeff_comp (x : lauSub P) (j : ℤ) :
      (comp x j).1 = AddMonoidAlgebra.single j (x.1.coeff j) := rfl
  have comp_mem_vertex : ∀ x : lauSub P, x ∈ vertex h → ∀ j, comp x j ∈ vertex h := by
    intro x hx j
    change ∃ c ∈ maximalIdeal C, algebraMap C K c = (comp x j).1.coeff 0
    rw [coeff_comp, AddMonoidAlgebra.coeff_single]
    by_cases hj : j = 0
    · subst j
      rw [Finsupp.single_eq_same]
      exact hx
    · exact ⟨0, Ideal.zero_mem _, by rw [Finsupp.single_eq_of_ne' hj, map_zero]⟩
  have comp_mem_pow : ∀ (N : ℕ) (x : lauSub P), x ∈ vertex h ^ N →
      ∀ j, comp x j ∈ vertex h ^ N := by
    intro N
    induction N with
    | zero =>
      intro x hx j
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on (C := fun z => ∀ j, comp z j ∈ vertex h ^ (n + 1)) hx ?_ ?_
      · intro y hy z hz j
        have e : comp (y * z) j =
            ∑ i ∈ y.1.coeff.support, comp y i * comp z (-i + j) := by
          apply Subtype.ext
          simp only [AddSubmonoidClass.coe_finsetSum, coeff_comp, Subalgebra.coe_mul,
            AddMonoidAlgebra.single_mul_single, add_neg_cancel_left]
          rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
          exact map_sum (AddMonoidAlgebra.singleAddHom j) _ _
        rw [e, pow_succ]
        exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (ih y hy i) (comp_mem_vertex z hz _)
      · intro y z hy hz j
        have e : comp (y + z) j = comp y j + comp z j := by
          apply Subtype.ext
          simp only [coeff_comp, Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
            AddMonoidAlgebra.single_add]
        rw [e]
        exact add_mem (hy j) (hz j)
  have hcomp : ∀ j : ℤ, (p : AddMonoidAlgebra K ℤ).coeff j = 0 := by
    intro j
    let a := (p : AddMonoidAlgebra K ℤ).coeff j
    let q := comp p j
    have hq : ∀ N : ℕ, q ∈ vertex h ^ N := fun N => comp_mem_pow N p (hp N) j
    have hq' : q ∈ ⨅ i : ℕ, (vertex h) ^ i • (⊤ : Submodule (lauSub P) (lauSub P)) := by
      rw [Submodule.mem_iInf]
      intro i
      simp only [Ideal.smul_eq_mul, Ideal.mul_top]
      exact hq i
    obtain ⟨⟨r, hr⟩, hrq⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (vertex h) q).1 hq'
    have hrq' : r * q = q := hrq
    obtain ⟨c, hc, hcr⟩ := hr
    have h1 : ((r * q : lauSub P) : AddMonoidAlgebra K ℤ).coeff j =
        (r : AddMonoidAlgebra K ℤ).coeff 0 * a := by
      have h0 := AddMonoidAlgebra.coeff_mul_single_add (r : AddMonoidAlgebra K ℤ) a j 0
      rw [zero_add] at h0
      exact h0
    have h2 : ((r * q : lauSub P) : AddMonoidAlgebra K ℤ).coeff j = a := by
      rw [hrq']
      show (AddMonoidAlgebra.single j a).coeff j = a
      rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    rw [h2, ← hcr] at h1
    have hu : IsUnit (algebraMap C K (1 - c)) :=
      (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits c hc).map _
    have h3 : algebraMap C K (1 - c) * a = 0 := by
      rw [map_sub, map_one, sub_mul, one_mul, ← h1, sub_self]
    exact hu.mul_right_eq_zero.1 h3
  apply Subtype.ext
  ext j
  simpa using hcomp j
