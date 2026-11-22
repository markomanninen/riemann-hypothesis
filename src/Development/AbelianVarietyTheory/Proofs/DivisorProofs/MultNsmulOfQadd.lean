module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem mult_nsmul_of_qadd {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X)
    (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    rw [zero_nsmul, (CartierDiv.isEqn_zero z).mult_eq, Units.val_one, (unitAt_one z).ord_eq_zero]
    simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem eff_nsmul_of_qadd {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

theorem qNum_add : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ),
    IsProjOver p → ∀ (N : LB X) (a b : ℚ) (D B : X → ℚ), QNum p N a D → QNum p N b B →
      QNum p N (a + b) (D + B) := by
  intro X _ _ p hp N a b D B hD hB
  letI := algebraΓOfHom p
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨m, D₀, hm, hD₀, rfl, hDn⟩ := hD
  obtain ⟨m', B₀, hm', hB₀, rfl, hBn⟩ := hB
  refine ⟨m * m', m' • D₀ + m • B₀, Nat.mul_pos hm hm', (eff_nsmul_of_qadd hD₀ m').add
    (eff_nsmul_of_qadd hB₀ m), ?_, ?_⟩
  · funext z
    simp only [Pi.add_apply, qWeil, CartierDiv.mult_add, mult_nsmul_of_qadd]
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    push_cast
    field_simp
  · intro C hC
    let hLB (D : CartierDiv X) : (toLB D).IsLB := (presents_toLB D).isLB
    let f : CartierDiv X →+ Pic X := AddMonoidHom.mk' (fun D => cls _ (hLB D)) fun D E =>
      (cls_eq_iff _ (isLB_tens (hLB D) (hLB E))).2
        ((presents_toLB _).lbIso ((presents_toLB D).tens (presents_toLB E)))
    have e := hC.interNumRed_of_cls_eq_add (N := toLB (m' • D₀ + m • B₀))
      (A := lbPow (toLB D₀) m') (B := lbPow (toLB B₀) m) hH (hLB (m' • D₀ + m • B₀))
      (isLB_lbPow (hLB D₀) m') (isLB_lbPow (hLB B₀) m)
      (by
        rw [cls_lbPow (hLB D₀), cls_lbPow (hLB B₀)]
        change f (m' • D₀ + m • B₀) = m' • f D₀ + m • f B₀
        rw [map_add, map_nsmul, map_nsmul])
    rw [hC.interNumRed_lbPow hH (hLB D₀), hC.interNumRed_lbPow hH (hLB B₀)] at e
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    have hD' := hDn C hC
    have hB' := hBn C hC
    rw [e]
    push_cast
    rw [div_eq_iff h1] at hD'
    rw [div_eq_iff h2] at hB'
    rw [div_eq_iff (mul_ne_zero h1 h2), hD', hB']
    ring

end GlobalTheory.PairStep
