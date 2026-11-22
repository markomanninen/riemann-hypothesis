module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LkHost
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.LocalConditionRankThreeEvenLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PlDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd3AltAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd3Alt

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V UpperTheory.V.Z.Win
open Formalism.GaloisCohomology UpperTheory.V.Base in
theorem UpperTheory.V.Z.Win.Dn.hostEnd_of_loc3_frame_linkedEnd_downCsdK (h3 : Dn.Loc3) (hK3 : Dn.LocalConditionRankThreeEvenLevel) :
    HostFrameEx → _root_.UpperTheory.V.Z.Sym.Pl.LinkedEndEAlt → _root_.UpperTheory.V.Z.Win.Dn.DownCsdKAlt → _root_.UpperTheory.V.Pr.HostEndAlt := by
  intro hF hL hD K _ _ _ hK Ω _ _ _ l hl ι c N _ e ψ o₁ hd σ hσ B hB
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  obtain ⟨L, _, _, _, _, g₁, Φ, C₀, ⟨k⟩, ok, big, sc⟩ := hF Ω l c N e ψ o₁ hd σ hσ B hB
  have hσ' : IsConjOm σ.toRingEquiv := hσ
  have hsq : σ * σ = 1 := by
    obtain ⟨j, hj⟩ := hσ'
    exact AlgEquiv.ext fun x => j.injective (by
      have h1 : j (σ (σ x)) = starRingEnd ℂ (j (σ x)) := hj (σ x)
      have h2 : j (σ x) = starRingEnd ℂ (j x) := hj x
      rw [AlgEquiv.mul_apply, h1, h2, Complex.conj_conj, AlgEquiv.one_apply])
  have hΨ : Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 := by
    have h1 : cycZ ℚ Ω l σ = -1 := hσ'.cyc (E := ℚ)
    have h2 : chiO ℚ Ω l c.O σ = -1 := by
      show Units.map (algebraMap ℤ_[l] c.O).toMonoidHom (cycZ ℚ Ω l σ) = -1
      rw [h1]
      apply Units.ext
      simp
    have h3 : (Chr.dirG ℚ Ω ψ σ : c.O) = (-1) ^ e := by
      rw [Chr.dirG, MonoidHom.comp_apply, (Chr.clsFacts ℚ Ω N).2.2.2.1 σ hσ', MulChar.coe_toUnitHom]
      exact hd.par
    apply Units.ext
    show ((chiO ℚ Ω l c.O σ ^ (e : ℤ) * Chr.dirG ℚ Ω ψ σ : c.Oˣ) : c.O) = 1
    rw [h2, zpow_natCast, Units.val_mul, h3, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_pow]
    simp
  have hram : ∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ (UnitaryThreeInertia.eta4 Ω).ker →
      B'.valuation ((l * N : ℕ) : Ω) < 1 := by
    intro B' h
    have h4 : B'.valuation ((4 : ℕ) : Ω) < 1 := by
      by_contra h4
      refine h fun s hs => ?_
      have h5 : Chr.cls ℚ Ω 4 s = 1 := (Chr.clsFacts ℚ Ω 4).2.2.2.2 B' h4 hs
      rw [MonoidHom.mem_ker, UnitaryThreeInertia.eta4, Chr.dirG, MonoidHom.comp_apply, h5, map_one]
    have h2 : B'.valuation ((2 : ℕ) : Ω) < 1 := by
      by_contra h2
      rw [not_lt] at h2
      rw [show (4 : ℕ) = 2 * 2 from rfl, Nat.cast_mul, map_mul] at h4
      exact (not_lt.2 (one_le_mul h2 h2)) h4
    obtain ⟨m, hm⟩ := (hd.N_even.mul_left l).two_dvd
    have hm' : B'.valuation (m : Ω) ≤ 1 := (B'.valuation_le_one_iff _).2 (natCast_mem B' m)
    rw [hm, Nat.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hm') h2
  obtain ⟨hfin, haut, -⟩ := hL Ω l ι c N e ψ hd.e_pos hd.N_even (UnitaryThreeInertia.eta4 Ω) σ g₁ B (l * N) dvd_rfl hram L Φ C₀ k hB ok big sc
  haveI : IsAlgClosure L Ω := Th.Db.algClo L Ω
  have hLk : LinkHyp c N e (UnitaryThreeInertia.eta4 Ω) σ B (l * N) := ⟨hd.e_pos, dvd_rfl, mul_ne_zero hl.out.ne_zero (NeZero.ne N), hram, hB, hσ⟩
  have hker : ∀ [Algebra K Ω], Base.galOf ℚ K Ω = (UnitaryThreeInertia.eta4 Ω).ker := by
    intro _
    rw [← Base.range_galEmb]
    exact (UnitaryThreeInertia.gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1
  exact ⟨g₁, marks_of_link k ok (dvd_mul_right l N) hsq hΨ, finEnd_of_finPt k ok (dvd_mul_right l N) hsq hfin,
    _root_.UpperTheory.V.Z.Win.Dn.autEnd3_alt hD k ok (dvd_mul_right l N) hσ ι K hker (fun A _ _ r hr hi _ _ _ ρ hρ => by
    haveI : IsAlgClosure K Ω := Th.Db.algClo K Ω
    have t := h3 Ω l c N e ψ _ _ g₁ B _ hLk L Φ C₀ k ok A r hr K hker.symm ρ hρ
    exact ⟨t.1, t.2, hK3 Ω l c N e ψ hd.N_even _ _ g₁ B _ hLk L Φ C₀ k ok big sc A r hr hi K hker.symm ρ hρ⟩) haut⟩
end
