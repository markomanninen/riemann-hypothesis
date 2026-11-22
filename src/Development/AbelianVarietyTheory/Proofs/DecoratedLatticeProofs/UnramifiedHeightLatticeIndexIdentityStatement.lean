module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeightLatticeIndexIdentity
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Formalism.LocalToGlobal.Columns.HeckeSp

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open GlobalTheory.HeckeLatIndex in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedHeight_lattice_index_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ (m g : GL D k) (s : Finset D), (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') → ∀ (L Lm large₂ : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ Lm ↔ m.1.mulVec v ∈ L) → (∀ v, v ∈ large₂ ↔ (g⁻¹).1.mulVec v ∈ L) → (((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) ^ 2 * H (m * g) = (resCard k : ℝ) ^ s.card * H m := by
  intro k _ _ _ _ D _ _ ϖ hϖ H hH m g s hg L Lm large₂ hL hLm hLg
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast (show 0 < resCard k by unfold resCard; exact Nat.card_pos)
  have hgt_mul_index (h : GL D k) (L P : AddSubgroup (D → k))
      (hL : ∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1)
      (hP : ∀ v, v ∈ P ↔ h.1.mulVec v ∈ L) :
      H h * (((P ⊓ L).relIndex P : ℕ) : ℝ) * (((P ⊓ L).relIndex L : ℕ) : ℝ) = 1 := by
    have decompose (g : GL D k) :
        ∃ x ∈ KO k D, ∃ y ∈ KO k D, ∃ e : D → ℤ, g = x * torusElt k D ϖ e * y := by
      obtain ⟨x, hx, y, hy, a, rfl⟩ := GlobalTheory.LocalCartan.exists_diagT g
      let ordHom : kˣ →* Multiplicative ℤ :=
        MonoidHom.mk' (fun z => Multiplicative.ofAdd (ord k z))
          (fun z w => by rw [ord_mul, ofAdd_add])
      let e : D → ℤ := fun i => ord k (a i)
      let u : D → kˣ := fun i => a i / ϖ ^ e i
      have hu (i : D) : valuation k (u i : k) = 1 := by
        apply ord_eq_zero_iff.mp
        have he := congrArg Multiplicative.toAdd (map_zpow ordHom ϖ (e i))
        have hp : ord k (ϖ ^ e i) = e i := by
          simpa [ordHom, toAdd_zpow, ord_eq_one hϖ] using he
        have hz := ord_mul k (u i) (ϖ ^ e i)
        rw [show u i * ϖ ^ e i = a i by simp [u], hp] at hz
        change e i = _ at hz
        omega
      refine ⟨x * diagT k D u, mul_mem hx (GlobalTheory.LocalCartan.diagT_mem_KO hu),
        y, hy, e, ?_⟩
      have ha : a = u * fun i => ϖ ^ e i := funext fun i => by simp [u]
      unfold torusElt
      rw [ha, map_mul]
      simp only [mul_assoc]
    obtain ⟨x, hx, y, hy, e, rfl⟩ := decompose h
    let t : GL D k := torusElt k D ϖ e
    let Pt : AddSubgroup (D → k) := L.comap (Matrix.mulVecLin t.1).toAddMonoidHom
    have hPt : ∀ v, v ∈ Pt ↔ t.1.mulVec v ∈ L := fun v => Iff.rfl
    obtain ⟨e1, e2⟩ := ko_index k D t x y hx hy L Pt P hL hPt hP
    have hd := diag_index k D ϖ hϖ e L Pt hL (fun v => by
      rw [hPt, hL]
      simp [t, torusElt, val_diagT, Matrix.mulVec_diagonal])
    have hH1 : H (x * t * y) = H t := by rw [(hH.1 y hy _).2, (hH.1 x hx _).1]
    rw [e1, e2, mul_assoc, hd]
    change H (x * t * y) * _ = 1
    rw [hH1, hH.2 e, ← zpow_add₀ hq.ne']
    simp
  obtain ⟨κ, hκ, κ', hκ', hgeq⟩ := hg

  have hgL : ∀ v, v ∈ L → g.1.mulVec v ∈ L := by
    intro v hv
    rw [hgeq, hL]
    have h1 := ko_pres k D κ' hκ' v ((hL v).1 hv)
    have h2 : ∀ i, valuation k ((torusElt k D ϖ (indic s)).1.mulVec (κ'.1.mulVec v) i) < 1 := by
      intro i
      simp only [torusElt, val_diagT, Matrix.mulVec_diagonal, map_mul]
      have hle : valuation k ((ϖ ^ indic s i : kˣ) : k) ≤ 1 := by
        unfold indic
        split_ifs
        · simp only [zpow_one]
          rw [hϖ]
          exact uniformizer_lt_one.le
        · simp
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hle) (h1 i)
    have h3 := ko_pres k D κ hκ _ h2
    simpa [Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc] using h3
  have hLgL : large₂ ≤ L := by
    intro v hv
    have : g.1.mulVec ((g⁻¹).1.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← this]
    exact hgL _ ((hLg v).1 hv)
  set φ := (Matrix.mulVecLin g.1).toAddMonoidHom with hφ
  have hinj : Function.Injective φ := mulVec_injective g

  let P₁ : AddSubgroup (D → k) := L.comap (Matrix.mulVecLin (m * g).1).toAddMonoidHom
  let P₂ : AddSubgroup (D → k) := L.comap (Matrix.mulVecLin g.1).toAddMonoidHom
  have hP₁ : ∀ v, v ∈ P₁ ↔ (m * g).1.mulVec v ∈ L := fun v => Iff.rfl
  have hP₂ : ∀ v, v ∈ P₂ ↔ g.1.mulVec v ∈ L := fun v => Iff.rfl
  have mP₁ : P₁.map φ = Lm := map_eq_of_preimage g P₁ Lm fun w => by
    rw [hP₁, hLm, Units.val_mul, Matrix.mulVec_mulVec]
  have mL : L.map φ = large₂ := by
    refine map_eq_of_preimage g L large₂ fun w => ?_
    rw [hLg, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have mP₂ : P₂.map φ = L := map_eq_of_preimage g P₂ L hP₂
  have k₁ := hgt_mul_index m L Lm hL hLm
  have k₂ := hgt_mul_index (m * g) L P₁ hL hP₁
  have k₃ := hgt_mul_index g L P₂ hL hP₂
  rw [← AddSubgroup.relIndex_map_map_of_injective (f := φ) _ _ hinj,
    ← AddSubgroup.relIndex_map_map_of_injective (f := φ) (P₁ ⊓ L) L hinj,
    AddSubgroup.map_inf_eq _ _ _ hinj, mP₁, mL] at k₂
  have hLP₂ : L ≤ P₂ := fun v hv => hgL v hv
  rw [inf_eq_right.2 hLP₂, AddSubgroup.relIndex_self, ← AddSubgroup.relIndex_map_map_of_injective (f := φ) _ _ hinj,
    mL, mP₂] at k₃
  have hHg : H g = (resCard k : ℝ) ^ (-(s.card : ℤ)) := by
    rw [hgeq, (hH.1 κ' hκ' _).2, (hH.1 κ hκ _).1, hH.2]
    congr 2
    unfold sumAbs indic
    rw [Finset.sum_congr rfl (fun i _ => show |(if i ∈ s then (1:ℤ) else 0)| = if i ∈ s then 1 else 0 by split_ifs <;> simp)]
    simp
  rw [hHg] at k₃

  have t₁ := AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) (Lm ⊓ L) Lm (inf_le_inf_left _ hLgL) inf_le_left
  have t₂ := AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) large₂ L inf_le_right hLgL
  have t₃ := AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) (Lm ⊓ L) L (inf_le_inf_left _ hLgL) inf_le_right
  have hQ : (large₂.relIndex L : ℝ) = (resCard k : ℝ) ^ s.card := by
    have hne' : (resCard k : ℝ) ^ s.card ≠ 0 := by positivity
    rw [_root_.zpow_neg, zpow_natCast, Nat.cast_one, mul_one, inv_mul_eq_one₀ hne'] at k₃
    exact k₃.symm
  have e1 : (((Lm ⊓ large₂).relIndex Lm : ℕ) : ℝ) = ((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) * ((Lm ⊓ L).relIndex Lm : ℕ) := by
    rw [← t₁]; push_cast; ring
  have e2 : (resCard k : ℝ) ^ s.card * (((Lm ⊓ large₂).relIndex large₂ : ℕ) : ℝ) = ((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) * ((Lm ⊓ L).relIndex L : ℕ) := by
    rw [← hQ]
    have := congrArg (fun n : ℕ => (n : ℝ)) (t₂.trans t₃.symm)
    push_cast at this
    linarith
  linear_combination (-(((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) ^ 2 * H (m * g)) * k₁ + ((resCard k : ℝ) ^ s.card * H m) * k₂
    + (-(H m * H (m * g) * (resCard k : ℝ) ^ s.card * (((Lm ⊓ large₂).relIndex large₂ : ℕ) : ℝ))) * e1
    + (-(H m * H (m * g) * (((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) * (((Lm ⊓ L).relIndex Lm : ℕ) : ℝ))) * e2
