module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeLeLogOfIntegralHermitianFormStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PairingNormalisingConstantLogLeBoundStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreservedStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtNormMulWeylPairingIntegralSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefiniteStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDualStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.ProdFormula
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

private theorem selfDualK_full {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : IsSelfDualK G M) : Submodule.IsFullLattice K M := by
  classical
  haveI : Submodule.IsLattice K M := hM.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hM.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin n → K) → K := fun x => star x ⬝ᵥ G *ᵥ y
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) s f
  have ha0 : (algebraMap (𝓞 K) K a) ≠ 0 :=
    (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 K) (Fin n → K) := {
    carrier := {x | ∃ b : 𝓞 K, (b : K) = (algebraMap (𝓞 K) K a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : K) + c = _
      rw [hb, hc]
      simp [f, dotProduct, Matrix.mulVec, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd K) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def,
        RingOfIntegers.mapRingHom_apply, Pi.star_apply, star_mul, dotProduct, Matrix.mulVec,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : K) * _ = _
      ring }
  have hsP : (s : Set (Fin n → K)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 K) K a) • y ∈ M := by
    rw [← hM.2]
    change ∀ x ∈ M, star x ⬝ᵥ G *ᵥ ((algebraMap (𝓞 K) K a) • y) ∈ (1 : Submodule (𝓞 K) K)
    intro x hx
    obtain ⟨b, hb⟩ := (hs ▸ Submodule.span_le.mpr hsP) hx
    have hpair : (b : K) = star x ⬝ᵥ G *ᵥ ((algebraMap (𝓞 K) K a) • y) := by
      rw [hb]
      simp only [f, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    refine ⟨b, ?_⟩
    simpa [LinearMap.toSpanSingleton_apply, Algebra.smul_def] using hpair
  have hy' : (algebraMap (𝓞 K) K a) • y ∈ Submodule.span K (M : Set (Fin n → K)) :=
    Submodule.subset_span hy
  have := (Submodule.span K (M : Set (Fin n → K))).smul_mem (algebraMap (𝓞 K) K a)⁻¹ hy'
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

theorem testLatticeCondition_sumLat_nabK_and_delK : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric (sumGram lam e G) X → TestLatticeCondition N X (sumLat lam e fun c => nabK lam (M c)) (bound (Fintype.card ι) n R) ∧ TestLatticeCondition N X (sumLat lam e fun c => delK lam (M c)) (bound (Fintype.card ι) n R) := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hsp G hG C _ M hM N e X hX
  classical
  obtain ⟨s, hs0, hs, hlog⟩ := GlobalTheory.T.pairing_normalising_constant_log_le_bound K ι n lam R hR hsp
  have hlat := fun c => GlobalTheory.T.nablaDeltaOperator_lattice_preserved K ι n lam (M c) (fun τ => selfDualK_full (G τ) (M c τ) (hM c τ))
  have main : ∀ T : C → Submodule (𝓞 K) (VV K lam), (∀ c, Submodule.IsFullLattice K (T c)) →
      (∀ c, T c ≤ nabK lam (M c)) → TestLatticeCondition N X (sumLat lam e T) (bound (Fintype.card ι) n R) := by
    intro T hT hle
    obtain ⟨hL, hN, -⟩ := GlobalTheory.T.orthogonalSumCoefficientLattice_isLattice_and_dual K ι n lam C N e T (fun c => (hT c).toIsLattice)
    haveI : Finite C :=
      Finite.of_injective (fun c => e.symm (c, (e ⟨0, hN⟩).2)) (fun a b h => by
        simpa using h)
    letI : Fintype C := Fintype.ofFinite C
    obtain ⟨hval, hdef, -, hdet⟩ := GlobalTheory.T.sumPairingGramMatrix_values_and_definite K ι n lam G hG C N e
    have hne : sumLat lam e T ≠ ⊥ := by
      intro h
      obtain ⟨c⟩ := (inferInstance : Nonempty C)
      obtain ⟨i⟩ := GlobalTheory.TestLat.SumLat.idx_nonempty lam
      have ht : ∃ t ∈ T c, t ≠ 0 := by
        by_contra hn
        push_neg at hn
        have hb : T c = ⊥ := by
          apply le_antisymm _ bot_le
          intro t ht
          simpa using hn t ht
        have hs := (hT c).span_eq_top
        rw [hb] at hs
        have hv := congrArg (fun S : Submodule K (VV K lam) => (bVV K lam i) ∈ S) hs
        have hv0 : bVV K lam i = 0 := by simpa using hv
        exact (bVV K lam).ne_zero i hv0
      obtain ⟨t, ht, ht0⟩ := ht
      let f := GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e
      let z := f.symm (Pi.single c t)
      have hz : z ∈ sumLat lam e T := by
        rw [GlobalTheory.TestLat.Model.mem_sumLat]
        intro c'
        have heq : valAt lam e c' z = (Pi.single c t : C → VV K lam) c' :=
          congrFun (f.apply_symm_apply (Pi.single c t)) c'
        rw [heq]
        by_cases hc : c' = c
        · subst hc; simpa using ht
        · simp [Pi.single_eq_of_ne hc]
      rw [h] at hz
      have hz0 : z = 0 := by simpa using hz
      have heq := congrFun (f.apply_symm_apply (Pi.single c t)) c
      change valAt lam e c z = (Pi.single c t : C → VV K lam) c at heq
      rw [hz0, map_zero, Pi.single_eq_same] at heq
      exact ht0 heq.symm
    refine ⟨hL.fg, hne, fun v => (hX v).1, le_trans ?_ hlog⟩
    refine GlobalTheory.T.maxSlope_le_log_of_integral_hermitian_form K v₀ hv N (sumGram lam e G) X ⟨hdef.2.1, hX⟩ s hs0 _ hL.fg hne ?_
    intro x hx y hy
    rw [hval, Finset.mul_sum, ← hs]
    refine Subring.sum_mem _ fun c _ => ?_
    have hmem : ∀ z ∈ sumLat lam e T, valAt lam e c z ∈ nabK lam (M c) := fun z hz =>
      hle c ((Submodule.mem_iInf _).1 hz c)
    exact GlobalTheory.T.extNorm_mul_weylPairing_integral_selfDual K ι n lam G (M c) (fun τ => (hG τ).1) hdet (hM c) _ (hmem x hx) _ (hmem y hy)
  exact ⟨main _ (fun c => (hlat c).1) (fun c => le_rfl),
    main _ (fun c => (hlat c).2) (fun c => delLeNab K ι n lam (M c))⟩

end GlobalTheory.TestLat
