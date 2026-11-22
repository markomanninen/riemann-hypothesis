module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesSubstCoeffSubMemIdealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFormalGroupLawEvalPointsOfDegreeLeOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowFirstAddSecondThreeGroupsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowSecondAddThirdThreeGroupsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSecondThirdEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEvalTwoGroupsThreeGroupsEqZeroOfNeZeroStatement

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.CobRel
theorem coeff_subst_sub_mem :
    ∀ {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype σ]
      (N : Ideal B) (u ℓ : σ → MvPowerSeries τ B), (∀ s, constantCoeff (u s) = 0) →
      (∀ s (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (u s) = coeff β (ℓ s)) →
      ∀ (m : ℕ) (c : MvPowerSeries σ Q),
        (∀ α : σ →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) →
        ∀ (w : τ →₀ ℕ), w.degree = m → ∃ r ∈ N,
          coeff w (MvPowerSeries.subst (QLog.up (Q := Q) u) c) -
            coeff w (MvPowerSeries.subst (QLog.up (Q := Q) ℓ) c) = algebraMap B Q r := by
  intro B Q σ τ _ _ _ _ N u ℓ hu hlin m c hc w hw
  have hℓ : ∀ s, constantCoeff (ℓ s) = 0 := fun s => by
    simpa only [coeff_zero_eq_constantCoeff_apply, hu s] using (hlin s 0 (by simp)).symm
  have horder : ∀ s, (2 : ℕ∞) ≤ (u s - ℓ s).order := fun s =>
    nat_le_order (n := 2) fun β hβ => by
      rw [map_sub, hlin s β (by omega), sub_self]
  have huSubst : HasSubst (QLog.up (Q := Q) u) :=
    hasSubst_of_constantCoeff_zero fun s => by simp [QLog.up, hu s]
  have hℓSubst : HasSubst (QLog.up (Q := Q) ℓ) :=
    hasSubst_of_constantCoeff_zero fun s => by simp [QLog.up, hℓ s]
  rw [coeff_subst huSubst, coeff_subst hℓSubst,
    ← finsum_sub_distrib (coeff_subst_finite huSubst c w) (coeff_subst_finite hℓSubst c w)]
  refine finsum_induction (fun x : Q => ∃ r ∈ N, x = algebraMap B Q r)
    ⟨0, N.zero_mem, by simp⟩
    (fun x y ⟨r, hr, hx⟩ ⟨t, ht, hy⟩ => ⟨r + t, N.add_mem hr ht, by rw [hx, hy, map_add]⟩)
    fun α => ?_
  have hprod (v : σ → MvPowerSeries τ B) :
      (α.prod fun s e => QLog.up (Q := Q) v s ^ e) =
        MvPowerSeries.map (algebraMap B Q) (α.prod fun s e => v s ^ e) := by
    simp only [QLog.up, Finsupp.prod, map_prod, map_pow]
  rw [hprod u, hprod ℓ, coeff_map, coeff_map, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub,
    ← map_sub]
  by_cases h : α.degree < m
  · obtain ⟨b, hb, hcb⟩ := hc α h
    exact ⟨b * _, N.mul_mem_right _ hb, by rw [hcb, map_mul]⟩
  · have hmono := GlobalTheory.SubstMod.order_monoProd_sub u ℓ hu hℓ horder α
    have hdegree : w.degree < α.degree + 1 := by omega
    have hzero : coeff w ((α.prod fun s e => u s ^ e) - α.prod fun s e => ℓ s ^ e) = 0 :=
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hdegree) hmono)
    exact ⟨0, N.zero_mem, by rw [hzero, map_zero, mul_zero]⟩

theorem coeff_op_of_degree_le_one : ∀ {B O : Type} [CommRing B] [CommRing O] (θ : B →+* O) {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}, IsLift θ μ → ∀ {τ : Type} (u v : Fin d → MvPowerSeries τ B), (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ (i : Fin d) (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (op μ u v i) = coeff β (u i + v i) := GlobalTheory.T.coeff_formalGroupLawEvalPoints_of_degree_le_one

theorem coeff_prod_addLeft : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) = if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := GlobalTheory.T.coeff_prod_pow_first_add_second_threeGroups

theorem coeff_prod_addRight : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) = if α = Finsupp.sumElim a (b + e) then (∏ i, ((b + e) i).choose (b i) : R) else 0 := GlobalTheory.T.coeff_prod_pow_x1_x2_add_x3

theorem coeff_evalTwoGroups_second_third_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), a ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_second_third_eq_zero

theorem coeff_evalTwoGroups_first_second_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), e ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := GlobalTheory.T.coeff_evalTwoGroups_threeGroups_eq_zero_of_ne_zero

end GlobalTheory.CobRel

namespace GlobalTheory.CobRel

theorem degree_sumElim3 {d : ℕ} (a b e : Fin d →₀ ℕ) :
    (Finsupp.sumElim a (Finsupp.sumElim b e)).degree = a.degree + b.degree + e.degree := by
  simp [Finsupp.degree_eq_sum, Fintype.sum_sum_type, add_assoc]

theorem x_hasSubst {R : Type} [CommRing R] {d : ℕ} (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)
    (hu : ∀ j, constantCoeff (u j) = 0) (hv : ∀ j, constantCoeff (v j) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

end GlobalTheory.CobRel

namespace GlobalTheory.CobRel

theorem cocycle_rel_mod : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (m : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) → In N (cob2 (QLog.up (Q := Q) μ) c) → ∀ n : Fin d →₀ ℕ, n.degree = m → ∀ a b : Fin d →₀ ℕ, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → ∃ r ∈ N, (∏ i, Nat.choose ((a + b) i) (a i) : Q) * coeff (Finsupp.sumElim (a + b) (n - (a + b))) c - (∏ i, Nat.choose ((n - a) i) (b i) : Q) * coeff (Finsupp.sumElim a (n - a)) c = algebraMap B Q r := by
  intro B O Q _ _ _ _ θ d μ hμ N m c hc hcob n hn a b ha _ hab hab'
  set e := n - (a + b) with he_def
  have he : e ≠ 0 := fun h => hab' (le_antisymm hab (tsub_eq_zero_iff_le.1 h))
  have hbe : b + e = n - a := by
    ext i
    have := hab i
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply, he_def] at this ⊢
    omega
  have hn' : a + b + e = n := by
    ext i
    have := hab i
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply, he_def] at this ⊢
    omega
  set w : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ := Finsupp.sumElim a (Finsupp.sumElim b e) with hw_def
  have hw : w.degree = m := by
    rw [← hn, ← hn', hw_def, degree_sumElim3, map_add (f := _), map_add (f := _)]
  have hX : ∀ (R : Type) [CommRing R] (j : Fin d),
      constantCoeff (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 ∧
      constantCoeff (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 ∧
      constantCoeff (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 := fun R _ j => by
    simp [x1, x2, x3]
  have hop : ∀ (R : Type) [CommRing R] (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
      (∀ i, constantCoeff (ν i) = 0) → ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ i,
      constantCoeff (op ν u v i) = 0 := fun R _ ν hν u v hu hv i =>
    constantCoeff_subst_eq_zero (x_hasSubst u v hu hv) (fun s => by cases s <;> simp [hu, hv]) (hν i)
  have hmapop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B),
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ i,
      map (algebraMap B Q) (op μ u v i) = op (QLog.up (Q := Q) μ) (fun j => map (algebraMap B Q) (u j))
        (fun j => map (algebraMap B Q) (v j)) i := fun u v hu hv i => by
    simp only [op, at2, QLog.up]
    rw [map_subst (x_hasSubst u v hu hv)]
    congr 1
    funext s
    cases s <;> rfl
  have hmX : ∀ j, (map (algebraMap B Q) (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x1 j) ∧
      (map (algebraMap B Q) (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x2 j) ∧
      (map (algebraMap B Q) (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x3 j) := fun j => by
    simp [x1, x2, x3, map_X]

  have hc2 : ∀ s, constantCoeff (Sum.elim (op μ x1 x2) x3 s) = 0 := by
    intro s
    cases s with
    | inl i => exact hop B μ hμ.const _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1) i
    | inr i => exact (hX B i).2.2
  have hd2 : ∀ s (β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ), β.degree ≤ 1 →
      coeff β (Sum.elim (op μ x1 x2) x3 s) = coeff β (Sum.elim (fun i => x1 i + x2 i) x3 s) := by
    intro s β hβ
    cases s with
    | inl i => exact coeff_op_of_degree_le_one θ hμ _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1) i β hβ
    | inr i => rfl
  obtain ⟨r2, hr2, h2⟩ := coeff_subst_sub_mem N _ _ hc2 hd2 m c hc w hw
  have hu2 : QLog.up (Q := Q) (Sum.elim (op μ x1 x2) x3) = Sum.elim (op (QLog.up (Q := Q) μ) x1 x2) x3 := by
    funext s
    cases s with
    | inl i =>
      simp only [QLog.up, Sum.elim_inl]
      rw [hmapop _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1)]
      simp only [(hmX _).1, (hmX _).2.1]
    | inr i => simp only [QLog.up, Sum.elim_inr]; exact (hmX i).2.2
  have hl2 : QLog.up (Q := Q) (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) x3) =
      Sum.elim (fun i => x1 i + x2 i) x3 := by
    funext s
    cases s with
    | inl i => simp only [QLog.up, Sum.elim_inl, map_add (f := _), (hmX i).1, (hmX i).2.1]
    | inr i => simp only [QLog.up, Sum.elim_inr]; exact (hmX i).2.2
  rw [hu2, hl2] at h2
  have hv2 : coeff w (MvPowerSeries.subst (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) Q)) x3) c) =
      (∏ i, ((a + b) i).choose (a i) : Q) * coeff (Finsupp.sumElim (a + b) e) c := by
    rw [coeff_subst (x_hasSubst _ _ (fun j => by simp [(hX Q j).1, (hX Q j).2.1]) (fun j => (hX Q j).2.2)),
      finsum_eq_single _ (Finsupp.sumElim (a + b) e)]
    · rw [hw_def, coeff_prod_addLeft, ite_eq_left rfl, smul_eq_mul, mul_comm]
    · intro α hα
      rw [hw_def, coeff_prod_addLeft, ite_eq_right hα, smul_zero]

  have hc3 : ∀ s, constantCoeff (Sum.elim x1 (op μ x2 x3) s) = 0 := by
    intro s
    cases s with
    | inl i => exact (hX B i).1
    | inr i => exact hop B μ hμ.const _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2) i
  have hd3 : ∀ s (β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ), β.degree ≤ 1 →
      coeff β (Sum.elim x1 (op μ x2 x3) s) = coeff β (Sum.elim x1 (fun i => x2 i + x3 i) s) := by
    intro s β hβ
    cases s with
    | inl i => rfl
    | inr i => exact coeff_op_of_degree_le_one θ hμ _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2) i β hβ
  obtain ⟨r3, hr3, h3⟩ := coeff_subst_sub_mem N _ _ hc3 hd3 m c hc w hw
  have hu3 : QLog.up (Q := Q) (Sum.elim x1 (op μ x2 x3)) = Sum.elim x1 (op (QLog.up (Q := Q) μ) x2 x3) := by
    funext s
    cases s with
    | inl i => simp only [QLog.up, Sum.elim_inl]; exact (hmX i).1
    | inr i =>
      simp only [QLog.up, Sum.elim_inr]
      rw [hmapop _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2)]
      simp only [(hmX _).2.1, (hmX _).2.2]
  have hl3 : QLog.up (Q := Q) (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B))) =
      Sum.elim x1 (fun i => x2 i + x3 i) := by
    funext s
    cases s with
    | inl i => simp only [QLog.up, Sum.elim_inl]; exact (hmX i).1
    | inr i => simp only [QLog.up, Sum.elim_inr, map_add (f := _), (hmX i).2.1, (hmX i).2.2]
  rw [hu3, hl3] at h3
  have hv3 : coeff w (MvPowerSeries.subst (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) Q))) c) =
      (∏ i, ((b + e) i).choose (b i) : Q) * coeff (Finsupp.sumElim a (b + e)) c := by
    rw [coeff_subst (x_hasSubst _ _ (fun j => (hX Q j).1) (fun j => by simp [(hX Q j).2.1, (hX Q j).2.2])),
      finsum_eq_single _ (Finsupp.sumElim a (b + e))]
    · rw [hw_def, coeff_prod_addRight, ite_eq_left rfl, smul_eq_mul, mul_comm]
    · intro α hα
      rw [hw_def, coeff_prod_addRight, ite_eq_right hα, smul_zero]

  obtain ⟨k, hk, hk'⟩ := hcob w
  have hsplit : coeff w (cob2 (QLog.up (Q := Q) μ) c) = coeff w (at2 c x2 x3) -
      coeff w (MvPowerSeries.subst (Sum.elim (op (QLog.up (Q := Q) μ) x1 x2) x3) c) +
      coeff w (MvPowerSeries.subst (Sum.elim x1 (op (QLog.up (Q := Q) μ) x2 x3)) c) - coeff w (at2 c x1 x2) := by
    simp only [cob2, map_sub, map_add (f := _)]; rfl
  rw [hsplit, hw_def, coeff_evalTwoGroups_second_third_eq_zero c a b e ha, coeff_evalTwoGroups_first_second_eq_zero c a b e he, ← hw_def] at hk'
  rw [hbe] at hv3
  refine ⟨-k - r2 + r3, N.add_mem (N.sub_mem (N.neg_mem hk) hr2) hr3, ?_⟩
  rw [map_add (f := _), map_sub, map_neg, ← hk', ← h2, ← h3, hv2, hv3]
  ring

end GlobalTheory.CobRel
