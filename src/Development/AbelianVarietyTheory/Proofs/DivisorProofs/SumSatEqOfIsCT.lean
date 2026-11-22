module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOperatorAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermFiniteDimensionalSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermFiniteDimensionalSpanParabolic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlInductiveRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanGenEigenOfFiniteDimensionalOrbit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpand
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermCenterActionSmoothForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSingleCharSpanMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorConstantTermSum

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.SatWordAt

open GlobalTheory.LFun Formalism.UG

theorem esymm_add (A B : Multiset ℂ) (j : ℕ) :
    (A + B).esymm j = ∑ i ∈ Finset.HasAntidiagonal.antidiagonal j, A.esymm i.1 * B.esymm i.2 := by
  induction A using Multiset.induction_on generalizing j with
  | empty =>
    rw [zero_add, Finset.sum_eq_single (0, j)]
    · simp [Multiset.esymm]
    · rintro ⟨a, b⟩ hab hne
      have hab' : a + b = j := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
      obtain _ | a := a
      · exact absurd (by simp [← hab']) hne
      · rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simp)]
        simp
    · simp
  | cons a A ih =>
    have hrec : ∀ (s : Multiset ℂ) (k : ℕ), (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := fun s k => by
      simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]
    have h0 : ∀ s : Multiset ℂ, s.esymm 0 = 1 := fun s => by simp [Multiset.esymm]
    obtain _ | j := j
    · simp [h0]
    · rw [Multiset.cons_add, hrec, ih, ih, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
      simp only [hrec, h0, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, add_assoc]

theorem satEig_add {q r s N : ℕ} (hq : q ≠ 0) (h : r + s = N) {C B : Multiset ℂˣ} (hC : C.card = r) (hB : B.card = s) (j : ℕ) :
    satEig q N (C + B) j = ∑ i ∈ (Finset.range (r + 1) ×ˢ Finset.range (s + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j),
      (q : ℂ) ^ (((j : ℂ) * (N - j) - i.1 * (r - i.1) - i.2 * (s - i.2)) / 2) * (satEig q r C i.1 * satEig q s B i.2) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hz : ∀ (A : Multiset ℂˣ) (k : ℕ), A.card < k → (A.map fun b : ℂˣ => (b : ℂ)).esymm k = 0 := fun A k hk => by
    rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simpa using hk)]
    simp
  rw [satEig, Multiset.map_add (f := _), esymm_add, Finset.mul_sum]
  symm
  refine Finset.sum_subset_zero_on_sdiff (fun i hi => ?_) (fun i hi => ?_) fun i hi => ?_
  · exact Finset.HasAntidiagonal.mem_antidiagonal.2 (Finset.mem_filter.1 hi).2
  · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
    have h3 := Finset.HasAntidiagonal.mem_antidiagonal.1 h1
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, h3, and_true, not_and_or, not_lt] at h2
    rcases h2 with h2 | h2
    · rw [hz C _ (by omega)]; simp
    · rw [hz B _ (by omega)]; simp
  · simp only [satEig]
    have e : ((j : ℂ) * (N - j)) / 2 = ((j : ℂ) * (N - j) - i.1 * (r - i.1) - i.2 * (s - i.2)) / 2 +
      (i.1 * (r - i.1)) / 2 + (i.2 * (s - i.2)) / 2 := by ring
    rw [e, Complex.cpow_add _ _ hq', Complex.cpow_add _ _ hq']
    ring

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {v : HeightOneSpectrum (𝓞 E)} {N r s : ℕ}

section Lin

variable {m : ℕ} {u : List (Letter E)} {f : Vec u} {h : wsize u + m = N}

end Lin

variable {ϖ : v.adicCompletion E}


end GlobalTheory.ResW.SatWordAt

namespace GlobalTheory.ResW

end GlobalTheory.ResW

end
