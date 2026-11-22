module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralBasisUnramifiedInvolutionExtStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformizerCompatibleUnramifiedExtStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitTraceFormDiscrUnramifiedExtStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetConjugationMatrixIntegralBasisStatement

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit :
    ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d →
      (letI : Algebra K.E K'.E := φ.toAlgebra
       ∃ w : Module.Basis (Fin d) K.E K'.E,
         (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det ≠ 0 ∧
           val K.O (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = 0) := by
  intro K K' d φ h hd
  let : Algebra K.E K'.E := φ.toAlgebra
  have hbasis : ∃ w : Module.Basis (Fin d) K.E K'.E, ∀ z : K'.E,
      (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔
        ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k := by
    obtain ⟨w, key⟩ := IntBasis.exists_key h
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have hmax (a : Fin d → K.E) : ∃ m, ∀ k, IntBasis.adicVal K (a k) ≤ IntBasis.adicVal K (a m) :=
      Finite.exists_max (fun k => IntBasis.adicVal K (a k))
    have hli : LinearIndependent K.E w := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      obtain ⟨m, hm⟩ := hmax g
      have hk := key g m hm
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hg
      rw [hg, map_zero] at hk
      have hgm : g m = 0 := (Valuation.zero_iff _).1 hk.symm
      intro k
      have hkm := hm k
      rw [hgm, map_zero] at hkm
      exact (Valuation.zero_iff _).1 (le_antisymm hkm zero_le)
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by
      rw [Fintype.card_fin]
      exact h.2.2.2.2.symm)
    refine ⟨B, fun z => ?_⟩
    have hz : ∑ k, φ (B.repr z k) * w k = z := by
      conv_rhs => rw [← B.sum_repr z]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coe_basisOfLinearIndependentOfCardEqFinrank, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    obtain ⟨m, hm⟩ := hmax (B.repr z)
    have hv := key _ m hm
    rw [hz] at hv
    rw [← IntBasis.adicVal_le_one_iff K' z]
    constructor
    · intro hzO k
      rw [← IntBasis.adicVal_le_one_iff]
      exact (hm k).trans (hv ▸ hzO)
    · intro hall
      rw [hv]
      exact (IntBasis.adicVal_le_one_iff K _).2 (hall m)
  obtain ⟨w, hw⟩ := hbasis
  refine ⟨w, ?_⟩
  obtain ⟨π, π', hππ, hm, hm'⟩ := GlobalTheory.T.exists_uniformizer_compatible_unramifiedExt K K' d φ h
  have hw1 : ∀ k, ∃ y : K'.O, algebraMap K'.O K'.E y = w k := by
    intro k
    apply (hw _).2
    intro m
    by_cases hkm : k = m
    · subst m
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hkm]⟩
  have hdiscr : ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u =
      (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)).det := by
    have hj : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective K'.O K'.E
    have hi : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E

    have hlift : ∀ a : K.O, φ (algebraMap K.O K.E a) ∈ (algebraMap K'.O K'.E).range := by
      intro a
      apply (hw _).2
      intro k
      obtain ⟨c, hc⟩ := (hw 1).1 ⟨1, map_one _⟩ k
      refine ⟨a * c, ?_⟩
      have h1 : φ (algebraMap K.O K.E a) = (algebraMap K.O K.E a) • (1 : K'.E) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hc]
    let e : K'.O ≃+* (algebraMap K'.O K'.E).range :=
      RingEquiv.ofBijective (algebraMap K'.O K'.E).rangeRestrict
        ⟨fun x y h => hj (congrArg Subtype.val h), (algebraMap K'.O K'.E).rangeRestrict_surjective⟩
    let ι : K.O →+* K'.O :=
      e.symm.toRingHom.comp ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift)
    have hι : ∀ a, algebraMap K'.O K'.E (ι a) = φ (algebraMap K.O K.E a) := by
      intro a
      exact congrArg Subtype.val (e.apply_symm_apply ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift a))
    let : Algebra K.O K'.O := ι.toAlgebra
    have hsm : ∀ (a : K.O) (y : K'.O),
        algebraMap K'.O K'.E (a • y) = algebraMap K.O K.E a • algebraMap K'.O K'.E y := by
      intro a y
      rw [Algebra.smul_def, map_mul, Algebra.smul_def]
      exact congrArg (· * _) (hι a)
    have hsum : ∀ (g : Fin d → K.O) (v : Fin d → K'.O),
        algebraMap K'.O K'.E (∑ k, g k • v k) = ∑ k, algebraMap K.O K.E (g k) • algebraMap K'.O K'.E (v k) := by
      intro g v
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => hsm _ _

    choose bv hbv using hw1
    have hcoord : ∀ (y : K'.O) (k : Fin d), ∃ a : K.O, algebraMap K.O K.E a = w.repr (algebraMap K'.O K'.E y) k :=
      fun y => (hw _).1 ⟨y, rfl⟩
    choose c hc using hcoord
    have hli : LinearIndependent K.O bv := by
      rw [Fintype.linearIndependent_iff]
      intro g hg k
      have h1 := congrArg (algebraMap K'.O K'.E) hg
      rw [hsum, map_zero] at h1
      simp only [hbv] at h1
      have h2 := (Fintype.linearIndependent_iff.1 w.linearIndependent) _ h1 k
      exact hi (by rw [h2, map_zero])
    have hsp : ⊤ ≤ Submodule.span K.O (Set.range bv) := by
      intro y _
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨c y, hj ?_⟩
      rw [hsum]
      simp only [hbv, hc]
      exact w.sum_repr _
    let b : Module.Basis (Fin d) K.O K'.O := Module.Basis.mk hli hsp
    have hb : ∀ k, algebraMap K'.O K'.E (b k) = w k := fun k => by
      rw [Module.Basis.mk_apply]; exact hbv k
    have hrep : ∀ y k, algebraMap K.O K.E (b.repr y k) = w.repr (algebraMap K'.O K'.E y) k := by
      intro y k
      conv_rhs => rw [← b.sum_repr y, hsum]
      simp only [hb]
      rw [w.repr_sum_self]

    have hTr : ∀ y, algebraMap K.O K.E (Algebra.trace K.O K'.O y) =
        Algebra.trace K.E K'.E (algebraMap K'.O K'.E y) := by
      intro y
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace w, Matrix.trace, Matrix.trace,
        map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.diag_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
        Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', hrep, map_mul, hb]

    have hιπ : ι π = π' := hj (by rw [hι, hππ])
    have hmax : (Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)).IsMaximal := by
      rw [hm, Ideal.map_span, Set.image_singleton]
      have h1 : algebraMap K.O K'.O π = π' := hιπ
      rw [h1, ← hm']
      exact IsLocalRing.maximalIdeal.isMaximal _
    refine ⟨Algebra.discr K.O b, ResDisc.isUnit_discr_of_isMaximal_map b hmax, ?_⟩
    rw [Algebra.discr_def, RingHom.map_det]
    congr 1
    ext k m
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, Matrix.of_apply, hTr, map_mul, hb]
  obtain ⟨u, hu, hue⟩ := hdiscr
  have hφ := h.2.1
  have hunit : ∃ u : K.O, IsUnit u ∧
      algebraMap K.O K.E u = (Matrix.of fun m l => w.repr (K'.c (w l)) m).det := by
    set C : Matrix (Fin d) (Fin d) K.E := Matrix.of fun m l => w.repr (K'.c (w l)) m with hC
    have hsm : ∀ (e : K.E) (x : K'.E), e • x = φ e * x := fun e x => rfl
    have hint : ∀ m l, ∃ a : K.O, algebraMap K.O K.E a = C m l := by
      intro m l
      obtain ⟨y, hy⟩ := hw1 l
      obtain ⟨y', hy'⟩ := K'.c_int y
      have h2 : ∃ y : K'.O, algebraMap K'.O K'.E y = K'.c (w l) := ⟨y', by rw [← hy', hy]⟩
      exact (hw _).1 h2 m
    choose A hA using hint
    have hrep : ∀ (x : K'.E) (n : Fin d), w.repr (K'.c x) n = ∑ m, K.c (w.repr x m) * C n m := by
      intro x n
      have hx : K'.c x = ∑ m, K.c (w.repr x m) • K'.c (w m) := by
        conv_lhs => rw [← w.sum_repr x]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hsm, hsm, map_mul, ← hφ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hx, map_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl
    have hCC : C * (K.c : K.E →+* K.E).mapMatrix C = 1 := by
      ext n l
      have h := hrep (K'.c (w l)) n
      rw [K'.c_c, w.repr_self, Finsupp.single_apply] at h
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_coe]
      rw [eq_comm]
      convert h using 1
      · exact if_congr eq_comm rfl rfl
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_comm]
      rfl
    have hdet : C.det * K.c C.det = 1 := by
      have h := congrArg Matrix.det hCC
      rw [Matrix.det_mul, Matrix.det_one, ← RingHom.map_det] at h
      exact h
    have hdetA : algebraMap K.O K.E (Matrix.of A).det = C.det := by
      rw [RingHom.map_det]
      congr 1
      ext m l
      simp [hA]
    refine ⟨(Matrix.of A).det, ?_, hdetA⟩
    obtain ⟨β, hβ⟩ := K.c_int (Matrix.of A).det
    apply IsUnit.of_mul_eq_one β
    apply IsFractionRing.injective K.O K.E
    rw [map_mul, ← hβ, hdetA, hdet, map_one]
  obtain ⟨v, hv, hve⟩ := hunit
  have key : (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))) =
      (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)) * (Matrix.of fun m l => w.repr (K'.c (w l)) m) := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.of_apply]
    conv_lhs => rw [← w.sum_repr (K'.c (w l))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hdet : (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = algebraMap K.O K.E (u * v) := by
    rw [key, Matrix.det_mul, ← hue, ← hve, map_mul]
  rw [hdet]
  refine ⟨?_, GlobalTheory.UnitLemma.Orbit.val_unit _ (hu.mul hv)⟩
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]
  exact (hu.mul hv).ne_zero
