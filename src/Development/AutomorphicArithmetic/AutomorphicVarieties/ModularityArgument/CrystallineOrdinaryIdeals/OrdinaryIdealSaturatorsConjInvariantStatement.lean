module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsConjInvariant
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinaryIdeal_saturators_conj_invariant :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
      (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C]
      (r : GQ l →* GG (m := 3) (R := C)) (h : GL (Fin 3) C), HasMult D.η r →
      D.ordIdeal (conjBy h r) = D.ordIdeal r ∧
        (∀ a, D.dd (conjBy h r) a = D.dd r a) ∧ D.del (conjBy h r) = D.del r := by
  intro l _ O _ _ _ D C _ _ r h hr
  have hone : ∀ s ∈ D.HL, (r s).right = 1 := by
    intro s hs
    rw [hr s]
    exact MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).1
  have hmat (s : GQ l) (hs : s ∈ D.HL) :
      (conjBy h r s).mat =
        (h : Matrix (Fin 3) (Fin 3) C) * (r s).mat *
          ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    have hleft : (conjBy h r s).left = h * (r s).left * h⁻¹ := by
      show (GG.ofGL h * r s * (GG.ofGL h)⁻¹).left = _
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.inv_left]
      simp only [SemidirectProduct.right_inl, SemidirectProduct.left_inl, SemidirectProduct.mul_right,
        hone s hs, mul_one, inv_one, map_one, MulAut.one_apply]
    unfold GG.mat
    rw [hleft, Units.val_mul, Units.val_mul]
  have hsh : ∀ s ∈ D.HL, ∀ a, D.sh (conjBy h r) a s =
      (h : Matrix (Fin 3) (Fin 3) C) * D.sh r a s * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro s hs a
    simp only [UpperTheory.V.Loc.Dat3.sh]
    rw [hmat s hs, GlobalTheory.OrdLoc.conj_sub_scalar]
  have hHLopen : IsOpen (D.HL : Set (GQ l)) := GlobalTheory.OrdLoc.hl_isOpen' D
  have hs0 : D.s0 ∈ D.HL := by
    obtain ⟨s, ⟨hs, hi⟩, hcyc⟩ := ((cycInertia l).2 D.HL hHLopen).2
    have hex : ∃ s, D.IsInertiaInfiniteCyclotomic s := ⟨s, hs, hi, hcyc⟩
    exact (Classical.epsilon_spec hex).1
  have hex : ∃ σ, D.IsFr σ := by
    have : D.HL.Normal := GlobalTheory.OrdLoc.hl_normal' D
    obtain ⟨hIn, -, -, ⟨σ₀, hσ₀⟩, -⟩ := iqBasic l
    have : (Iq l).Normal := hIn
    have : D.HL.FiniteIndex := GlobalTheory.OrdLoc.finiteIndex_of_open' ⟨D.HL, hHLopen⟩
    let N : Subgroup (GQ l) := D.HL ⊔ Iq l
    have : N.FiniteIndex := Subgroup.finiteIndex_of_le (show D.HL ≤ N from le_sup_left)
    have : N.Normal := Subgroup.sup_normal _ _
    let q : GQ l ⧸ N := (σ₀ : GQ l ⧸ N)
    let m := orderOf q
    have hmN : σ₀ ^ m ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact pow_orderOf_eq_one q
    obtain ⟨σ, hσ, i₀, hi₀, hpow⟩ := Subgroup.mem_sup_of_normal_right.1 hmN
    let φ := QuotientGroup.mk' (Iq l)
    have hφ : ∀ {x}, φ x = 1 ↔ x ∈ Iq l := fun {x} => QuotientGroup.eq_one_iff x
    have hφm : φ σ₀ ^ m = φ σ := by
      rw [← map_pow, ← hpow, map_mul, hφ.2 hi₀, mul_one]
    refine ⟨σ, ⟨hσ, ?_⟩, σ₀, m, hσ₀, orderOf_pos q, ?_⟩
    · rw [eq_top_iff]
      intro g _
      rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe, mem_closure_iff]
      intro U hU hgU
      have hV : IsOpen (D.HL.subtype '' U) :=
        hHLopen.isOpenEmbedding_subtypeVal.isOpenMap U hU
      have hcl : (g : GQ l) ∈ closure ((Iq l ⊔ Subgroup.zpowers σ₀ : Subgroup (GQ l)) :
          Set (GQ l)) := by
        rw [← Subgroup.topologicalClosure_coe, frobDense σ₀ hσ₀]
        trivial
      obtain ⟨x, ⟨u, huU, rfl⟩, hx⟩ := mem_closure_iff.1 hcl _ hV ⟨g, hgU, rfl⟩
      obtain ⟨i, hi, z, hz, hiz⟩ := Subgroup.mem_sup_of_normal_left.1 hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      change i * σ₀ ^ k = (u : GQ l) at hiz
      have hkN : σ₀ ^ k ∈ N := by
        have e : σ₀ ^ k = i⁻¹ * (u : GQ l) := by rw [← hiz]; group
        rw [e]
        exact N.mul_mem (Subgroup.mem_sup_right (Subgroup.inv_mem _ hi)) (Subgroup.mem_sup_left u.2)
      have hdvd : (m : ℤ) ∣ k := by
        change (orderOf q : ℤ) ∣ k
        rw [orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]
        exact hkN
      obtain ⟨j, rfl⟩ := hdvd
      have hφu : φ (u : GQ l) = φ σ ^ j := by
        rw [← hiz, map_mul, hφ.2 hi, one_mul, map_zpow, zpow_mul, zpow_natCast, hφm]
      have hy : (u : GQ l) * σ ^ (-j) ∈ Iq l := by
        rw [← hφ, map_mul, map_zpow, hφu, zpow_neg, mul_inv_cancel]
      refine ⟨u, huU, ?_⟩
      let y : D.HL := ⟨(u : GQ l) * σ ^ (-j), D.HL.mul_mem u.2 (D.HL.zpow_mem hσ _)⟩
      have e : u = y * (⟨σ, hσ⟩ : D.HL) ^ j := by
        ext
        simp [y]
      rw [SetLike.mem_coe, e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy)
        (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))
    · rw [← hpow]
      simpa using Subgroup.inv_mem _ hi₀
  have hfrSpec : D.IsFr D.fr := Classical.epsilon_spec hex
  obtain ⟨hfr, -⟩ := hfrSpec.1
  have htr : ∀ a, D.tr (conjBy h r) a = D.tr r a := by
    intro a
    simp only [UpperTheory.V.Loc.Dat3.tr]
    rw [hsh _ hs0, hsh _ hs0, hmat _ hfr, GlobalTheory.OrdLoc.conj_mul_three_alt, GlobalTheory.OrdLoc.trace_conj]
  have hdd : ∀ a, D.dd (conjBy h r) a = D.dd r a := by
    intro a
    simp only [UpperTheory.V.Loc.Dat3.dd, htr]
  have hprod : ∀ t : Fin 3 → GQ l, (∀ a, t a ∈ D.HL ⊓ Iq l) →
      D.sh (conjBy h r) 0 (t 0) * D.sh (conjBy h r) 1 (t 1) * D.sh (conjBy h r) 2 (t 2) =
        (h : Matrix (Fin 3) (Fin 3) C) * (D.sh r 0 (t 0) * D.sh r 1 (t 1) * D.sh r 2 (t 2)) *
          ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro t ht
    rw [hsh _ (Subgroup.mem_inf.1 (ht 0)).1, hsh _ (Subgroup.mem_inf.1 (ht 1)).1,
      hsh _ (Subgroup.mem_inf.1 (ht 2)).1, GlobalTheory.OrdLoc.conj_mul_three_alt]
  refine ⟨?_, hdd, by simp only [UpperTheory.V.Loc.Dat3.del, hdd]⟩
  unfold UpperTheory.V.Loc.Dat3.ordIdeal
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x (⟨s, hs, i, rfl⟩ | ⟨t, ht, i, j, rfl⟩)
    · exact Ideal.subset_span
        (Or.inl ⟨s, hs, i, by rw [hmat s (Subgroup.mem_inf.1 hs).1, GlobalTheory.OrdLoc.charpoly_conj]⟩)
    · rw [hprod t ht]
      apply GlobalTheory.OrdLoc.ent_mem_mul
      intro a b
      exact Ideal.subset_span (Or.inr ⟨t, ht, a, b, rfl⟩)
  · rw [Ideal.span_le]
    rintro x (⟨s, hs, i, rfl⟩ | ⟨t, ht, i, j, rfl⟩)
    · exact Ideal.subset_span
        (Or.inl ⟨s, hs, i, by rw [hmat s (Subgroup.mem_inf.1 hs).1, GlobalTheory.OrdLoc.charpoly_conj]⟩)
    · rw [GlobalTheory.OrdLoc.unconj h (D.sh r 0 (t 0) * D.sh r 1 (t 1) * D.sh r 2 (t 2)), ← hprod t ht]
      apply GlobalTheory.OrdLoc.ent_mem_mul
      intro a b
      exact Ideal.subset_span (Or.inr ⟨t, ht, a, b, rfl⟩)
