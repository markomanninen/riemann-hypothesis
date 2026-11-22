module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickeningStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.QLog

theorem dIn_top_formalLog_map : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q]
    (σ : Type) (g : MvPowerSeries σ B), constantCoeff g = 1 →
      DIn (⊤ : Ideal B) (formalLog (map (algebraMap B Q) g)) := by
  intro B Q _ _ _ _ σ g hg α i
  classical
  obtain ⟨u, hu⟩ : IsUnit g := isUnit_iff_constantCoeff.mpr (by rw [hg]; exact isUnit_one)
  set φ := algebraMap B Q
  have hG : constantCoeff (map φ g) = 1 := by simp [hg]
  have hd : pderiv (R := Q) i (formalLog (map φ g)) = map φ ((↑u⁻¹ : MvPowerSeries σ B) * pderiv (R := B) i g) := by
    have h1 := mul_pderiv_formalLog hG i
    rw [pderiv_map] at h1
    have h2 : map φ (↑u⁻¹ : MvPowerSeries σ B) * map φ g = 1 := by
      rw [← map_mul, ← hu, Units.inv_mul, map_one]
    calc pderiv (R := Q) i (formalLog (map φ g))
        = (map φ (↑u⁻¹ : MvPowerSeries σ B) * map φ g) * pderiv (R := Q) i (formalLog (map φ g)) := by
          rw [h2, one_mul]
      _ = map φ ((↑u⁻¹ : MvPowerSeries σ B) * pderiv (R := B) i g) := by
          rw [mul_assoc, h1, map_mul]
  by_cases hα : α i = 0
  · exact ⟨0, Submodule.mem_top, by simp [hα]⟩
  · refine ⟨coeff (α - Finsupp.single i 1) ((↑u⁻¹ : MvPowerSeries σ B) * pderiv (R := B) i g),
      Submodule.mem_top, ?_⟩
    rw [natCast_mul_coeff_of_pderiv_eq hd hα, coeff_map]

end GlobalTheory.QLog
