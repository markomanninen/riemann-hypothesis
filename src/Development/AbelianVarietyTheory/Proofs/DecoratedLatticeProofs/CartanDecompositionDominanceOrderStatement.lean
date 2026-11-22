module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceOrder
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open GlobalTheory.ZonalInduct (pot pot_lt pot_nonneg pos_iff_lt psum nonneg_of_dom) in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_decomposition_dominance_order :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (ϖ : kˣ) (c : ℕ → ℂ), c N ≠ 0 →
    (∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧
      ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        x = κ * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * κ') →
    (∀ (μ ν : Fin N → ℤ), Antitone μ → Antitone ν → ∀ n : ℕ, n ≤ N → ∀ g : GL (Fin N) k,
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        g = κ * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ
          (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) * κ') →
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ μ * g =
          κ * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * κ') →
      ∑ i, ν i = ∑ i, μ i + n ∧ ∀ j : ℕ,
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
            (μ i + indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i)) →
    (∀ g : GL (Fin N) k, ∃ R, IsRepsK g R) →
    ∀ h : GL (Fin N) k → ℂ,
      (∀ κ ∈ KO k (Fin N), ∀ m, h (κ * m) = h m ∧ h (m * κ) = h m) →
      (∀ (s : Finset (Fin N)) R,
        IsRepsK (GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (indic s)) R →
          ∀ m, ∑ g ∈ R, h (m * g) = c s.card * h m) →
      h 1 = 0 → ∀ m, h m = 0 := by
  intro k _ _ _ _ N ϖ c hc hcart hdom hex h hK hT h1 m
  let torus := GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ
  have torus_add (a b : Fin N → ℤ) : torus (a + b) = torus a * torus b := by
    apply Units.ext
    simp only [torus, Units.val_mul, GlobalTheory.GLDoubling.val_torusElt, diagonal_mul_diagonal]
    congr 1; funext i; simp [zpow_add₀ (Units.ne_zero ϖ)]
  have torus_zero : torus (fun _ => 0) = 1 := by
    apply Units.ext
    rw [GlobalTheory.GLDoubling.val_torusElt]; simp
  have torus_one_comm (g : GL (Fin N) k) :
      g * torus (fun _ => 1) = torus (fun _ => 1) * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, GlobalTheory.GLDoubling.val_torusElt]
    ext i j; simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have vanish_of_shift (j : ℕ) (m : GL (Fin N) k)
      (hm : h (m * torus (fun _ => (j : ℤ))) = 0) : h m = 0 := by
    induction j generalizing m with
    | zero => simpa [torus_zero] using hm
    | succ j ih =>
      apply ih
      have hz : indic (Finset.univ : Finset (Fin N)) = fun _ => 1 := funext fun i => by simp [indic]
      obtain ⟨R, hR⟩ := hex (torus (indic Finset.univ))
      set z := torus (fun _ => 1) with hzdef
      set m' := m * torus (fun _ => (j : ℤ))
      have hsplit : torus (fun _ => ((j + 1 : ℕ) : ℤ)) = torus (fun _ => (j : ℤ)) * z := by
        rw [hzdef, ← torus_add]; congr 1
      have hm' : h (m' * z) = 0 := by rw [← hm, hsplit, mul_assoc]
      have key := hT Finset.univ R hR m'
      have hterm : ∀ g ∈ R, h (m' * g) = 0 := by
        intro g hg
        obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hR.1 g hg
        rw [hz] at *
        have e : m' * (κ * z * κ') = (m' * z) * (κ * κ') := by
          rw [torus_one_comm]
          simp only [mul_assoc]
        rw [e, (hK _ (mul_mem hκ hκ') _).2, hm']
      rw [Finset.sum_eq_zero hterm, Finset.card_univ, Fintype.card_fin] at key
      exact (mul_eq_zero.1 key.symm).resolve_left hc
  have vanish_dominant :
      ∀ n : ℕ, ∀ e : Fin N → ℤ, Antitone e → (∀ i, 0 ≤ e i) → pot e ≤ n → h (torus e) = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih e ha he hpot
    have IH : ∀ ν : Fin N → ℤ, Antitone ν → (∀ i, 0 ≤ ν i) → pot ν < pot e →
        h (torus ν) = 0 := by
      intro ν hν hν0 hlt
      have h0 := pot_nonneg hν0
      exact ih (pot ν).toNat (by omega) ν hν hν0 (by omega)
    by_cases hzero : ∀ i, e i = 0
    · have : e = fun _ => 0 := funext hzero
      rw [this, torus_zero, h1]
    push Not at hzero
    obtain ⟨i₀, hi₀⟩ := hzero
    have hi₀pos : 0 < e i₀ := lt_of_le_of_ne (he i₀) (Ne.symm hi₀)
    obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = (Finset.univ.filter fun j => 0 < e j).card := ⟨_, rfl⟩
    have key : ∀ i, 0 < e i ↔ (i : ℕ) < n₀ := fun i => hn₀ ▸ pos_iff_lt ha i
    have hn₀N : n₀ ≤ N := by rw [hn₀]; exact (Finset.card_le_univ _).trans (by simp)
    obtain ⟨s, hs⟩ : ∃ s : Finset (Fin N), s = Finset.univ.filter fun i : Fin N => (i : ℕ) < n₀ := ⟨_, rfl⟩
    have hind : ∀ i, indic s i = if 0 < e i then 1 else 0 := by
      intro i; simp only [indic, hs, Finset.mem_filter, Finset.mem_univ, true_and, ← key]
    have hscard : s.card = n₀ := by
      rw [hn₀]; congr 1; rw [hs]; ext i; simp [key]
    set μ : Fin N → ℤ := fun i => e i - indic s i with hμdef
    have hμe : ∀ i, μ i + indic s i = e i := fun i => by simp [hμdef]
    have hμa : Antitone μ := by
      intro i j hij
      have := ha hij; have hi := he i; have hj := he j
      simp only [hμdef, hind]
      split_ifs <;> omega
    have hμ0 : ∀ i, 0 ≤ μ i := by
      intro i; have := he i; simp only [hμdef, hind]; split_ifs <;> omega
    have hμlt : pot μ < pot e := by
      apply pot_lt
      · intro j; unfold psum
        exact Finset.sum_le_sum fun i _ => by simp only [hμdef, hind]; split_ifs <;> omega
      · intro hh; have := congrFun hh i₀; simp only [hμdef, hind, ite_eq_left hi₀pos] at this; omega
    have hμv := IH μ hμa hμ0 hμlt
    have hTe : torus e = torus μ * torus (indic s) := by
      rw [← torus_add]; congr 1; funext i; exact (hμe i).symm
    have hsumind : ∑ i, indic s i = (n₀ : ℤ) := by
      rw [← hscard]; simp [indic]
    obtain ⟨R, hR⟩ := hex (torus (indic s))
    have hsum := hT s R hR (torus μ)
    rw [hμv, mul_zero] at hsum
    have hterm : ∀ g ∈ R, h (torus μ * g) = 0 ∨
        h (torus μ * g) = h (torus e) := by
      intro g hg
      obtain ⟨ν, hν, κ1, hκ1, κ2, hκ2, hx⟩ := hcart (torus μ * g)
      have hval : h (torus μ * g) = h (torus ν) := by
        rw [hx, mul_assoc, (hK κ1 hκ1 _).1, (hK κ2 hκ2 _).2]
      obtain ⟨κ, hκ, κ', hκ', hgeq⟩ := hR.1 g hg
      have hd := hdom μ ν hμa hν n₀ hn₀N g ⟨κ, hκ, κ', hκ', by rw [← hs]; exact hgeq⟩ ⟨κ1, hκ1, κ2, hκ2, hx⟩
      simp only [← hs] at hd
      obtain ⟨hd1, hd2⟩ := hd
      have hle : ∀ j, psum ν j ≤ psum e j := by
        intro j; have := hd2 j; simp only [hμe] at this; exact this
      have hsumeq : ∑ i, ν i = ∑ i, e i := by
        rw [hd1, ← hsumind, ← Finset.sum_add_distrib]; simp only [hμe]
      have hν0 := nonneg_of_dom hν he hle hsumeq
      by_cases hνe : ν = e
      · right; rw [hval, hνe]
      · left; rw [hval]; exact IH ν hν hν0 (pot_lt hle hνe)
    obtain ⟨g₁, ⟨hg₁R, hg₁K⟩, -⟩ := hR.2 1 (one_mem _)
    have hg₁ : h (torus μ * g₁) = h (torus e) := by
      have e1 : torus μ * g₁ =
          torus e * (g₁⁻¹ * (1 * torus (indic s)))⁻¹ := by
        rw [hTe]; group
      rw [e1, (hK _ (inv_mem hg₁K) _).2]
    by_contra hx
    have hite : ∀ g ∈ R, h (torus μ * g) =
        if h (torus μ * g) = h (torus e) then h (torus e) else 0 := by
      intro g hg
      rcases hterm g hg with h0 | h0
      · rw [h0, ite_eq_right (Ne.symm hx)]
      · rw [ite_eq_left h0]; exact h0
    rw [Finset.sum_congr rfl hite, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul] at hsum
    have hcard : (R.filter fun g => h (torus μ * g) = h (torus e)).card ≠ 0 :=
      Finset.card_ne_zero.2 ⟨g₁, Finset.mem_filter.2 ⟨hg₁R, hg₁⟩⟩
    rcases mul_eq_zero.1 hsum with hc0 | hc0
    · exact hcard (by exact_mod_cast hc0)
    · exact hx hc0
  obtain ⟨ν, hν, κ, hκ, κ', hκ', rfl⟩ := hcart m
  rw [mul_assoc, (hK κ hκ _).1, (hK κ' hκ' _).2]
  change h (torus ν) = 0
  let j := (∑ i, |ν i|).toNat
  apply vanish_of_shift j
  rw [← torus_add]
  refine vanish_dominant (pot (ν + fun _ => (j : ℤ))).toNat (ν + fun _ => (j : ℤ))
    ?_ ?_ (Int.self_le_toNat _)
  · intro a b hab; simp only [Pi.add_apply]; linarith [hν hab]
  · intro i; simp only [Pi.add_apply]
    have h1' : |ν i| ≤ ∑ i, |ν i| :=
      Finset.single_le_sum (f := fun i => |ν i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le (ν i)
    have h3 := Int.self_le_toNat (∑ i, |ν i|)
    omega
