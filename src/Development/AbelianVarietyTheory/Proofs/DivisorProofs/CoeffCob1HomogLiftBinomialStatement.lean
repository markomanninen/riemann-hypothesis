module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCob1HomogLiftBinomial
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_cob1_homog_lift_binomial :
    ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q]
    (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ →
    ∀ (m : ℕ) (h : MvPowerSeries (Fin d) Q), m ≠ 0 →
    (∀ α : Fin d →₀ ℕ, α.degree ≠ m → coeff α h = 0) →
    ∀ a e : Fin d →₀ ℕ, (a + e).degree ≤ m →
    coeff (Finsupp.sumElim a e) (cob1 (GlobalTheory.QLog.up Q μ) h) =
      if a ≠ 0 ∧ e ≠ 0 then (∏ i, Nat.choose ((a + e) i) (a i) : Q) * coeff (a + e) h else 0 := by
  intro B O Q _ _ _ _ θ d μ hμ m h hm hh a e hdeg
  classical
  have hlin : ∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 →
      coeff α (GlobalTheory.QLog.up Q μ i) = coeff α (addLaw Q d i) := by
    intro i α hα
    rw [GlobalTheory.QLog.up, coeff_map, GlobalTheory.CobHom.coeff_lift_low hμ i α hα,
      GlobalTheory.Katz.LowLaw.coeff_addLaw]
    split_ifs <;> simp
  have hlow : ∀ α : Fin d →₀ ℕ, α.degree < m → coeff α h = 0 := fun α hα => hh α hα.ne
  have hγ : (Finsupp.sumElim a e).degree = (a + e).degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    simp
  have h0 : coeff 0 h = 0 := hh 0 (by simpa using Ne.symm hm)
  have hlead := (GlobalTheory.CobLead.cob_eq_additive_lead Q d (GlobalTheory.QLog.up Q μ)
    m hlin).1 h hlow (Finsupp.sumElim a e)
  rw [hlead.2 (hγ ▸ hdeg), GlobalTheory.CobHom.coeff_cob1_additive_law_binomial]
  by_cases ha : a = 0
  · subst a
    by_cases he : e = 0
    · subst e
      simp [h0]
    · simp [he]
  · by_cases he : e = 0
    · subst e
      simp [ha]
    · simp [ha, he]
