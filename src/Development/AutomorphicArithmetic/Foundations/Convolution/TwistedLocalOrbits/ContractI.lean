module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ContractRow
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem mem_iw {g : GL (Fin n) E} : g ∈ iwahori E (Fin n) ↔
    ((∀ i j, valuation E (g.val i j) ≤ 1) ∧ ∀ i j, valuation E (g⁻¹.val i j) ≤ 1) ∧
      ∀ i j, j < i → valuation E (g.val i j) < 1 := by
  rw [mem_iwahori, GlobalTheory.SplitFlip.mem_KO_iff]
  rfl

private theorem diag_one {g : GL (Fin n) E} (hg : g ∈ iwahori E (Fin n)) (i : Fin n) :
    valuation E (g.val i i) = 1 := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_iw.1 hg
  have h4 := (mem_iw.1 (inv_mem hg)).2
  refine le_antisymm (h1 i i) (not_lt.1 fun h => ?_)
  have : valuation E (∑ l, g.val i l * g⁻¹.val l i) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
    rw [map_mul]
    rcases lt_trichotomy l i with hl | hl | hl
    · exact (mul_le_of_le_one_right' (h2 l i)).trans_lt (h3 i l hl)
    · subst hl
      exact (mul_le_of_le_one_right' (h2 l l)).trans_lt h
    · exact (mul_le_of_le_one_left' (h1 i l)).trans_lt (h4 l i hl)
  change valuation E ((g.val * g⁻¹.val) i i) < 1 at this
  rw [g.mul_inv] at this
  simp at this

private theorem sg_mem {σ : E ≃+* E} (hσ : Isom σ) {g : GL (Fin n) E} (hg : g ∈ iwahori E (Fin n)) :
    sg σ g ∈ iwahori E (Fin n) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_iw.1 hg
  rw [mem_iw, ← map_inv]
  exact ⟨⟨fun i j => (hσ _).le.trans (h1 i j), fun i j => (hσ _).le.trans (h2 i j)⟩,
    fun i j h => (hσ _).le.trans_lt (h3 i j h)⟩

end

theorem UpperTheory.ConvolutionTheory.Loc.contractI :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E), Isom σ → ∀ t : Fin n → Eˣ, Strict t → ∀ g ∈ iwahoriCoset t,
      ∃ k ∈ iwahori E (Fin n), ∃ s ∈ torusO E (Fin n), g = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k := by
  rintro E _ _ _ _ n σ hσ t ht g ⟨a, ha, b, hb, rfl⟩
  have hb' : b * sg σ a ∈ iwahori E (Fin n) := mul_mem hb (sg_mem hσ ha)
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_iw.1 hb'
  have hu : uniformizer E < 1 := uniformizer_lt_one
  have ht' : ∀ j l, j < l → valuation E ((t j : E) / t l) ≤ uniformizer E := fun j l h => by
    rw [le_uniformizer_iff, map_div₀, div_lt_one₀ (zero_le.trans_lt (ht j l h))]
    exact ht j l h
  let B := b * sg σ a
  have hdiag := diag_one (inv_mem hb')
  have hone (i j : Fin n) : valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hconj : ∃ k ∈ ball n (uniformizer E), (∀ i j, valuation E (k⁻¹.val i j) ≤ 1) ∧
      ∃ s : Fin n → Eˣ,
        (∀ i, valuation E ((((s i)⁻¹ : Eˣ) : E) - B⁻¹.val i i) ≤ uniformizer E) ∧
        diagT E (Fin n) t * B = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k := by
    choose x μ hμ hx hxe using exists_row hσ t le_rfl hu ht' B.val B⁻¹.val B.inv_mul
      h1 h2 (diag_one hb') hdiag (fun j l h => le_uniformizer_iff.2 (h3 j l h))
      (fun j l h => by
        rw [map_mul]
        exact (mul_le_of_le_one_right' (h2 j l)).trans (ht' j l h))
    have hμ0 : ∀ i, μ i ≠ 0 := fun i h => by
      have hi := hμ i
      rw [h, zero_sub, Valuation.map_neg, hdiag i] at hi
      exact (not_le.2 hu) hi
    let M : Matrix (Fin n) (Fin n) E := Matrix.of x
    have hoff (i j) (h : i ≠ j) : valuation E (M i j) < 1 := by
      simpa [M, one_apply_ne h] using (hx i j).trans_lt hu
    have hd (i) : valuation E (M i i) = 1 := by
      have hi := (hx i i).trans_lt hu
      rw [one_apply_eq] at hi
      change valuation E (x i i) = 1
      rw [← sub_add_cancel (x i i) 1, Valuation.map_add_eq_of_lt_right, map_one]
      simpa only [map_one] using hi
    have hbound := vecMul_bound M (fun i j => by
      by_cases h : i = j
      · exact h ▸ (hd i).le
      · exact (hoff i j h).le) hd (fun i j h => hoff i j h.ne') n
    have hunit : IsUnit M := by
      refine vecMul_injective_iff_isUnit.1 fun u v huv => funext fun l => ?_
      have hzero : (u - v) ᵥ* M = 0 := by
        rw [sub_vecMul, sub_eq_zero]
        exact huv
      have hl := hbound (u - v) 0 (fun j hj => absurd j.2 (not_lt.2 hj))
        (fun j _ => le_of_eq ((map_eq_zero _).2 (congrFun hzero j))) l
      simpa [sub_eq_zero] using hl
    obtain ⟨k, hk⟩ := hunit
    refine ⟨k, fun i j => by rw [hk]; exact hx i j, ?_, fun i => (Units.mk0 _ (hμ0 i))⁻¹,
      fun i => by simpa using hμ i, ?_⟩
    · intro i j
      refine hbound (fun l => k⁻¹.val i l) 1 (fun l hl => absurd l.2 (not_lt.2 hl))
        (fun j _ => ?_) j
      rw [← hk]
      change valuation E ((k⁻¹.val * k.val) i j) ≤ 1
      rw [k.inv_mul]
      exact hone i j
    · rw [mul_assoc, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← eq_mul_inv_iff_mul_eq, mul_assoc]
      ext i j
      rw [Units.val_mul, Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal,
        diagonal_mul, Matrix.mul_apply]
      have hsg (l) : (sg σ k).val i l = σ (x i l) := by
        show σ (k.val i l) = _
        rw [hk]
        rfl
      simp only [hsg, Pi.mul_apply, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [mul_right_comm, ← hxe, hk, mul_inv_cancel_right₀ (hμ0 i)]
      rfl
  obtain ⟨k, hk, hk', s, hs, e⟩ := hconj
  have hkI : k ∈ iwahori E (Fin n) := by
    refine mem_iw.2 ⟨⟨fun i j => ?_, hk'⟩, fun i j h => by simpa [one_apply_ne h.ne'] using (hk i j).trans_lt hu⟩
    rw [← sub_add_cancel (k.val i j) ((1 : Matrix (Fin n) (Fin n) E) i j)]
    exact Valuation.map_add_le _ ((hk i j).trans hu.le) (hone i j)
  refine ⟨k * a⁻¹, mul_mem hkI (inv_mem ha), s, inv_mem_iff.1 fun i => ?_, ?_⟩
  · have hd := diag_one (inv_mem hb') i
    show valuation E (((s i)⁻¹ : Eˣ) : E) = 1
    rw [← sub_add_cancel (((s i)⁻¹ : Eˣ) : E) ((b * sg σ a)⁻¹.val i i), Valuation.map_add_eq_of_lt_right, hd]
    exact hd ▸ (hs i).trans_lt hu
  · calc a * diagT E (Fin n) t * b = a * (diagT E (Fin n) t * (b * sg σ a)) * (sg σ a)⁻¹ := by group
      _ = _ := by rw [e, map_mul (sg σ), map_inv]; group
