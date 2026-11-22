module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetRepsMaximalIdealMatrixModMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open GlobalTheory.LowerHecke.MaxReps in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_reps_maximalIdealMatrix_mod_mul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ),
      valuation k (ϖ : k) = uniformizer k →
      ∀ (s : Finset D) (g : GL D k),
        (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D,
          g = κ * GlobalTheory.GLDoubling.torusElt (k := k) (n := D) ϖ (indic s) * κ') →
        ∃ N : Finset (Matrix D A k), (∀ ν ∈ N, ∀ i a, valuation k (ν i a) < 1) ∧
          ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) →
            ∃! ν', ν' ∈ N ∧ ∃ μ : Matrix D A k,
              (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s g hg
  classical
  have existsRightInverse :
      ∃ Q : Matrix D D k, GlobalTheory.StepData.IntM Q ∧
        g.1 * Q = (ϖ : k) • (1 : Matrix D D k) := by
    obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hg
    have hϖ1 : (ϖ : k) ∈ 𝒪[k] := (hϖ ▸ uniformizer_lt_one).le
    have inverseIntegral (u : GL D k) (hu : u ∈ KO k D) :
        GlobalTheory.StepData.IntM u⁻¹.1 := by
      obtain ⟨v, rfl⟩ := hu
      rw [← map_inv]
      exact fun i j => (v⁻¹.1 i j).2
    have mulIntegral (X Y : Matrix D D k) (hX : GlobalTheory.StepData.IntM X)
        (hY : GlobalTheory.StepData.IntM Y) : GlobalTheory.StepData.IntM (X * Y) :=
      fun i j => sum_mem fun l _ => mul_mem (hX i l) (hY l j)
    let t := GlobalTheory.GLDoubling.torusElt (k := k) (n := D) ϖ (indic s)
    have ht : t.1 = diagonal fun i => (ϖ : k) ^ indic s i := by
      exact GlobalTheory.GLDoubling.val_torusElt ϖ (indic s)
    let D0 : Matrix D D k := diagonal fun i => (ϖ : k) ^ (1 - indic s i)
    have hD0 : t.1 * D0 = (ϖ : k) • (1 : Matrix D D k) := by
      rw [ht, diagonal_mul_diagonal, smul_one_eq_diagonal]
      congr 1
      funext i
      rw [← zpow_add₀ ϖ.ne_zero]
      simp
    refine ⟨(κ'⁻¹ : GL D k).1 * D0 * (κ⁻¹ : GL D k).1, ?_, ?_⟩
    · refine mulIntegral _ _ (mulIntegral _ _ (inverseIntegral κ' hκ') ?_) (inverseIntegral κ hκ)
      intro i j
      simp only [D0, diagonal_apply]
      split_ifs
      · by_cases hi : i ∈ s <;> simp [indic, hi, hϖ1]
      · exact zero_mem _
    · have e1 : κ'.1 * (κ'⁻¹ : GL D k).1 = 1 := Units.mul_inv κ'
      have e2 : κ.1 * (κ⁻¹ : GL D k).1 = 1 := Units.mul_inv κ
      simp only [Units.val_mul]
      calc κ.1 * t.1 * κ'.1 * ((κ'⁻¹ : GL D k).1 * D0 * (κ⁻¹ : GL D k).1)
          = κ.1 * (t.1 * (κ'.1 * (κ'⁻¹ : GL D k).1) * D0) * (κ⁻¹ : GL D k).1 := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [e1, Matrix.mul_one, hD0, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, e2]
  obtain ⟨Q, hQ, hgQ⟩ := existsRightInverse
  let M : AddSubgroup (Matrix D A k) := maxLat k A D
  let H := (mulLat (A := A) g.1).addSubgroupOf M
  have scaleMem {x : k} (hx : valuation k x < 1) : (ϖ : k)⁻¹ * x ∈ 𝒪[k] := by
    change valuation k _ ≤ 1
    have h0 : valuation k (ϖ : k) ≠ 0 := by simp
    rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one, hϖ, le_uniformizer_iff]
    exact hx
  let redMap : M →+ (D → A → 𝓀[k]) :=
    { toFun := fun ν i a =>
        IsLocalRing.residue 𝒪[k] ⟨(ϖ : k)⁻¹ * (ν : Matrix D A k) i a, scaleMem (ν.2 i a)⟩
      map_zero' := by
        funext i a
        simp only [AddSubgroup.coe_zero, Matrix.zero_apply, mul_zero, Pi.zero_apply]
        exact map_zero _
      map_add' := by
        intro ν ν'
        funext i a
        simp only [Pi.add_apply]
        rw [← map_add (f := _)]
        congr 1
        ext
        simp [mul_add] }
  have hK : redMap.ker ≤ H := by
    intro ν hν
    rw [AddMonoidHom.mem_ker] at hν
    rw [AddSubgroup.mem_addSubgroupOf]
    have hμ : ∀ i a, valuation k ((ϖ : k)⁻¹ * (ν : Matrix D A k) i a) < 1 := fun i a => by
      have := congrFun (congrFun hν i) a
      simp only [redMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at this
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Valuation.Integer.not_isUnit_iff_valuation_lt_one] at this
      exact this
    refine ⟨Q * ((ϖ : k)⁻¹ • (ν : Matrix D A k)), ?_, ?_⟩
    · intro i a
      rw [Matrix.mul_apply]
      refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
      rw [map_mul]
      calc
        _ ≤ 1 * valuation k (((ϖ : k)⁻¹ • (ν : Matrix D A k)) l a) :=
          mul_le_mul_of_nonneg_right (hQ i l) zero_le
        _ < 1 := by simpa using hμ l a
    · rw [← Matrix.mul_assoc, hgQ, Matrix.smul_mul, Matrix.one_mul, smul_smul,
        mul_inv_cancel₀ ϖ.ne_zero, one_smul]
  have : Finite (M ⧸ redMap.ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).symm.toEquiv
  have : redMap.ker.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have : H.FiniteIndex := AddSubgroup.finiteIndex_of_le hK
  have : Finite (M ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
  let _ := Fintype.ofFinite (M ⧸ H)
  refine ⟨Finset.univ.image fun q : M ⧸ H => ((Quotient.out q : M) : Matrix D A k), ?_, ?_⟩
  · intro ν hν
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hν
    exact (Quotient.out q).2
  · intro ν hν
    have key : ∀ q : M ⧸ H, q = (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) ↔
        ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ((Quotient.out q : M) : Matrix D A k) = g.1 * μ := by
      intro q
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine exists_congr fun μ => and_congr_right fun _ => ?_
      show -((Quotient.out q : M) : Matrix D A k) + ν = g.1 * μ ↔ _
      rw [neg_add_eq_sub]
    refine ⟨((Quotient.out (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) : M) : Matrix D A k),
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).1 rfl⟩, ?_⟩
    rintro y ⟨hy, hyμ⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [(key q).2 hyμ]
