module

public import Mathlib
public import Formalism.LocalRingCardinality.DataSpaces

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd :
    {E : Type} →
      [inst : Field E] → [inst_1 : NumberField E] → [inst_2 : StarRing E] → (W : Formalism.BasicNotions.HSpace E) → Set (Fin W.rank → E) :=
    fun {E : Type} [Field E] [NumberField E] [StarRing E] (W : Formalism.BasicNotions.HSpace E) ↦
      {x : Fin W.rank → E | ∑ i : Fin W.rank, x i • (W.frame : Fin W.rank → W.V) i ∈ W.L0}

private theorem UpperTheory.Reformulated.B.EmbeddingTypeJumps.integral_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E]
    (W : Formalism.BasicNotions.HSpace E) {a : E} (ha : IsIntegral ℤ a) {v : W.V} (hv : v ∈ W.L0) :
    a • v ∈ W.L0 := by
  let b : NumberField.RingOfIntegers E := ⟨a, ha⟩
  have h : (algebraMap (NumberField.RingOfIntegers E) E b) • v ∈ W.L0 := by
    rw [algebraMap_smul]
    exact W.L0.smul_mem b hv
  exact h

private theorem UpperTheory.Reformulated.B.EmbeddingTypeJumps.exists_int_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E]
    (W : Formalism.BasicNotions.HSpace E) (v : W.V) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ W.L0 := by
  classical
  have := W.standardTuple_isLattice
  obtain ⟨s, hs⟩ := Submodule.IsLattice.fg E W.L0
  obtain ⟨n, hn, hgen⟩ := exists_integral_multiples ℤ ℚ (s.image (W.hT v))
  refine ⟨n, hn, ?_⟩
  rw [Int.cast_smul_eq_zsmul E]
  let f := (W.hT (n • v)).restrictScalars (NumberField.RingOfIntegers E)
  have hpair : W.L0 ≤ (1 : Submodule (NumberField.RingOfIntegers E) E).comap f := by
    rw [← hs, Submodule.span_le]
    intro y hy
    have hint := hgen (W.hT v y) (Finset.mem_image_of_mem (W.hT v) hy)
    apply Submodule.mem_one.mpr
    refine ⟨⟨n • W.hT v y, hint⟩, ?_⟩
    change n • W.hT v y = W.hT (n • v) y
    rw [map_zsmul]
    exact (map_zsmul (LinearMap.evalAddMonoidHom y) n (W.hT v)).symm
  have hself : Formalism.HermitianLatticesTheory.dual W.hT W.L0 = W.L0 :=
    W.baseLattice_isUnimodular
  rw [← hself]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf,
    Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  intro y hy
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hpair hy)
  have hint : IsIntegral ℤ (W.hT (n • v) y) := ha ▸ a.property
  have hstar := hint.map_of_comp_eq (RingHom.id ℤ) (starRingEnd E) (by ext <;> simp)
  rw [W.herm.eq (n • v) y] at hstar
  exact ⟨⟨_, hstar⟩, rfl⟩

theorem UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd_low :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E]
      [inst_5 : StarRing E] (W : Formalism.BasicNotions.HSpace E),
      ∃ (c : NumberField.RingOfIntegers F),
        c ≠ (0 : NumberField.RingOfIntegers F) ∧
          ∀ (i : Fin W.rank) (e : E), IsIntegral ℤ e → Pi.single i ((↑c : F) • e) ∈ UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd W := by
  intro F E _ _ _ _ _ _ W
  choose n hn hmem using fun i : Fin W.rank => UpperTheory.Reformulated.B.EmbeddingTypeJumps.exists_int_smul_mem W (W.frame i)
  refine ⟨((∏ i, n i : ℤ) : NumberField.RingOfIntegers F), ?_, ?_⟩
  · exact Int.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hn i)
  · intro i e he
    obtain ⟨k, hk⟩ : n i ∣ ∏ j, n j := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    have hk' : IsIntegral ℤ (k • e) := he.smul k
    have hm := UpperTheory.Reformulated.B.EmbeddingTypeJumps.integral_smul_mem W hk' (hmem i)
    have hc : ((((∏ j, n j : ℤ) : NumberField.RingOfIntegers F) : F)) • e = (k • e) * (n i : E) := by
      rw [hk, Algebra.smul_def, NumberField.RingOfIntegers.coe_eq_algebraMap, map_intCast,
        map_intCast, zsmul_eq_mul, Int.cast_mul]
      ring
    show ∑ j : Fin W.rank, (Pi.single i _ : Fin W.rank → E) j • W.frame j ∈ W.L0
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, hc, mul_smul]
    exact hm
