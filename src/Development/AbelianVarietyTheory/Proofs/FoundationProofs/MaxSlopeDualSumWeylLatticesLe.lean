module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.ProdFormula
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeLeLogOfIntegralHermitianFormStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDualStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PairingNormalisingConstantLogLeBoundStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualFormIntegralOnDualFr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedWeylLatticeHermitianDualityStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreservedStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtNormMulWeylPairingIntegralSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefiniteStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDualStatement

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

private theorem selfDual_full {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : IsSelfDualK G M) : Submodule.IsFullLattice K M := by
  classical
  letI := hM.1
  refine ⟨?_⟩
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨s, hs⟩ := hM.1.fg
  obtain ⟨d, hd, hden⟩ := GlobalTheory.DualLat.exists_den_finset
    (s.image (fun y => star y ⬝ᵥ (G *ᵥ x)))
  have hdx : d • x ∈ M := by
    rw [← hM.2]
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rw [Matrix.mulVec_smul, dotProduct_smul]
      exact hden _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz =>
      simpa [star_add, add_dotProduct] using add_mem hy hz
    | smul a y _ hy =>
      obtain ⟨b, hb⟩ := Submodule.mem_one.mp (GlobalTheory.DualLat.star_mem_one
        (Submodule.mem_one.mpr ⟨a, rfl⟩ : (algebraMap (𝓞 K) K a) ∈ (1 : Submodule (𝓞 K) K)))
      have heq : star (a • y) = (algebraMap (𝓞 K) K b) • star y := by
        ext i
        change star (algebraMap (𝓞 K) K a * y i) = algebraMap (𝓞 K) K b * star (y i)
        rw [star_mul, hb, mul_comm]
      rw [heq, smul_dotProduct]
      exact Submodule.smul_mem (1 : Submodule (𝓞 K) K) b hy
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := fun h =>
    hd ((IsFractionRing.injective (𝓞 K) K) (by simpa using h))
  have hx := (Submodule.span K (M : Set (Fin n → K))).smul_mem
    (algebraMap (𝓞 K) K d)⁻¹ (Submodule.subset_span hdx)
  rwa [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hdK, one_smul] at hx

private theorem sumLat_full {K : Type} [Field K] [NumberField K]
    {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} [Fintype C]
    (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam)
    (T : C → Submodule (𝓞 K) (VV K lam))
    (hT : ∀ c, Submodule.IsFullLattice K (T c))
    (hL : Submodule.IsLattice K (sumLat lam e T)) :
    Submodule.IsFullLattice K (sumLat lam e T) := by
  classical
  letI := hL
  refine ⟨?_⟩
  let f := SumLat.valEquiv (K := K) lam e
  let g : C → VV K lam →ₗ[K] (Fin N → K) := fun c =>
    f.symm.toLinearMap ∘ₗ LinearMap.single K (fun _ : C => VV K lam) c
  have hval : ∀ c c' t, valAt lam e c' (g c t) = (Pi.single c t : C → VV K lam) c' := by
    intro c c' t
    exact congrFun (f.apply_symm_apply (Pi.single c t : C → VV K lam)) c'
  have hmem : ∀ c t, t ∈ T c → g c t ∈ sumLat lam e T := by
    intro c t ht
    rw [Model.mem_sumLat]
    intro c'
    rw [hval]
    by_cases hc : c' = c
    · subst hc; simpa using ht
    · simp [hc]
  have key : ∀ c t, t ∈ Submodule.span K (T c : Set (VV K lam)) →
      g c t ∈ Submodule.span K (sumLat lam e T : Set (Fin N → K)) := by
    intro c t ht
    induction ht using Submodule.span_induction with
    | mem t ht => exact Submodule.subset_span (hmem c t ht)
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx => simpa using Submodule.smul_mem _ a hx
  apply eq_top_iff.mpr
  intro u _
  have hsum : ∑ c, g c (valAt lam e c u) = u := by
    apply f.injective
    rw [map_sum]
    have h : ∀ c, f (g c (valAt lam e c u)) =
        Pi.single c (valAt lam e c u) := fun c => f.apply_symm_apply _
    simp only [h]
    exact Finset.univ_sum_single (fun c => valAt lam e c u)
  rw [← hsum]
  apply Submodule.sum_mem
  intro c _
  apply key
  rw [(hT c).span_eq_top]
  trivial

theorem testLatticeCondition_dualFr_sumLat_delK : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric ((sumGram lam e G)⁻¹)ᵀ X → TestLatticeCondition N X (dualFr (sumLat lam e fun c => delK lam (M c))) (bound (Fintype.card ι) n R) := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hsp G hG C _ M hM N e X hX
  have hGh : ∀ τ, (G τ)ᴴ = G τ := fun τ => (hG τ).1
  have hMfull : ∀ c τ, Submodule.IsFullLattice K (M c τ) := fun c τ => selfDual_full _ _ (hM c τ)
  have hdel : ∀ c, Submodule.IsFullLattice K (delK lam (M c)) := fun c =>
    (GlobalTheory.T.nablaDeltaOperator_lattice_preserved K ι n lam (M c) (hMfull c)).2
  obtain ⟨hlat, hN, hdual⟩ := GlobalTheory.T.orthogonalSumCoefficientLattice_isLattice_and_dual K ι n lam C N e (fun c => delK lam (M c)) (fun c => (hdel c).toIsLattice)
  haveI : Finite C := by
    let i₀ : VVIdx lam := (e ⟨0, hN⟩).2
    refine Finite.of_injective (fun c : C => e.symm (c, i₀)) ?_
    intro a b hab
    exact (Prod.ext_iff.1 (e.symm.injective hab)).1
  letI : Fintype C := Fintype.ofFinite C
  obtain ⟨hval, hH, hHi, hGu⟩ := GlobalTheory.T.sumPairingGramMatrix_values_and_definite K ι n lam G hG C N e
  have hHu : IsUnit (sumGram lam e G).det := by
    have h1 := (hH.2.2 v₀.embedding).isUnit
    rw [Matrix.isUnit_iff_isUnit_det] at h1
    have h2 : ((sumGram lam e G).map v₀.embedding).det = v₀.embedding (sumGram lam e G).det :=
      (RingHom.map_det v₀.embedding (sumGram lam e G)).symm
    rw [h2] at h1
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at h1
    exact not_isUnit_zero h1
  have hnab : hdualFr (sumGram lam e G) (sumLat lam e fun c => delK lam (M c))
      = sumLat lam e fun c => nabK lam (M c) := by
    rw [hdual G hGh]
    congr 1
    funext c
    rw [(GlobalTheory.T.transported_weylLattice_hermitianDuality K ι n lam G (M c) hGh hGu (hMfull c)).2]
    congr 1
    funext τ
    exact (hM c τ).2
  obtain ⟨s, hs, hse, hsb⟩ := GlobalTheory.T.pairing_normalising_constant_log_le_bound K ι n lam R hR hsp
  have hint : ∀ x ∈ hdualFr (sumGram lam e G) (sumLat lam e fun c => delK lam (M c)),
      ∀ y ∈ hdualFr (sumGram lam e G) (sumLat lam e fun c => delK lam (M c)),
        (s : K) * (star x ⬝ᵥ sumGram lam e G *ᵥ y) ∈ (algebraMap (𝓞 K) K).range := by
    intro x hx y hy
    rw [hnab] at hx hy
    rw [hval, Finset.mul_sum]
    refine Subring.sum_mem _ fun c _ => ?_
    rw [← hse]
    exact GlobalTheory.T.extNorm_mul_weylPairing_integral_selfDual K ι n lam G (M c) hGh hGu (hM c) _
      ((Submodule.mem_iInf _).1 hx c) _ ((Submodule.mem_iInf _).1 hy c)
  have hint' := dualForm_integral_on_dualFr K N (sumGram lam e G) hH.1 hHu _ s hint
  have hD := (GlobalTheory.T.dualLattice_isLattice_and_hermitianDual.1 K N (sumGram lam e G) _ hHu (sumLat_full lam e _ hdel hlat)).1
  have hne : dualFr (sumLat lam e fun c => delK lam (M c)) ≠ ⊥ := by
    classical
    let i : Fin N := ⟨0, hN⟩
    obtain ⟨S, hS⟩ := hlat.fg
    obtain ⟨⟨d, hd⟩, hden⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors (𝓞 K)) (S.image (fun x => x i))
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hm : (Pi.single i (algebraMap (𝓞 K) K d) : Fin N → K) ∈
        dualFr (sumLat lam e fun c => delK lam (M c)) := by
      intro x hx
      rw [← hS] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        rw [single_dotProduct]
        exact Submodule.mem_one.2 (hden _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
      | zero => simp
      | add x y _ _ hx hy => simpa [dotProduct_add] using add_mem hx hy
      | smul c x _ hx => simpa [dotProduct_smul] using Submodule.smul_mem (1 : Submodule (𝓞 K) K) c hx
    intro h0
    rw [h0, Submodule.mem_bot] at hm
    have := congrFun hm i
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact hd0 (RingOfIntegers.coe_injective (by simpa using this))
  refine ⟨hD.fg, hne, fun v => (hX v).1, le_trans ?_ hsb⟩
  exact GlobalTheory.T.maxSlope_le_log_of_integral_hermitian_form K v₀ hv N _ X ⟨hHi.2.1, hX⟩ s hs _ hD.fg hne hint'

end GlobalTheory.TestLat
