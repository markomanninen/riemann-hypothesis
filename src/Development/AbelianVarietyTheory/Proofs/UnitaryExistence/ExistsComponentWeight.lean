module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralRatZetaOfCoeff
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PointsDetectFrobeniusSections
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralDetSubOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEqNsmulOfDvdPairing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelAutomorphismPeriodFamily
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexFrobeniusPoints
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetCharacterReductionInvariant

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.CharacterFunction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem natCast_mem_half {l l₂ : Level H} {pd : ℕ} {I : Ideal (𝓞 E)} (hM : l₂.M = l.M * pd)
    (hMb : l₂.Mb = l.Mb * I) : (pd : 𝓞 E) ∈ I := by
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(pd : 𝓞 E)} := by
    have h2 := l₂.prod
    rw [hMb, hM, Ideal.map_mul, mul_mul_mul_comm, l.prod, Nat.cast_mul,
      ← Ideal.span_singleton_mul_span_singleton] at h2
    refine mul_left_cancel₀ ?_ h2
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM0
  have : Ideal.span {(pd : 𝓞 E)} ≤ I := hp ▸ Ideal.mul_le_left
  exact this (Ideal.subset_span rfl)

theorem nsmul_mem_smul_top {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] {I : Ideal R} {N : ℕ}
    (h : (N : R) ∈ I) (x : L) : N • x ∈ (I • ⊤ : Submodule R L) := by
  rw [← Nat.cast_smul_eq_nsmul R]
  exact Submodule.smul_mem_smul h trivial

end GlobalTheory.CharacterFunction
