module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.IwasawaVolumeBoundOf
public import Formalism.PeriodIntegrals.LatCountG
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
public import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
public import Formalism.LogSumExpBounds.StatementD
public import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
public import Mathlib
public import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
public import Formalism.GelfandTransference.EnergyIdentity
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.LatticeRigidity.StatementC
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.DetNorm
public import Formalism.HermitianLattices.StatementMass
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdelesExt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.NatSmulMulEq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.AlgebraMapIntMemIntAd

@[expose] public section

noncomputable section

namespace PI.IwaMeasEx.Gauge.ZetaZeros

open Filter Topology Formalism.MainNotions.S

section Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

theorem norm_exp_sub_partial_le (x : 𝔸) (m : ℕ) :
    ‖NormedSpace.exp x - ∑ i ∈ Finset.range m, ((i.factorial : ℝ)⁻¹) • x ^ i‖ ≤
      Real.exp ‖x‖ - ∑ i ∈ Finset.range m, ((i.factorial : ℝ)⁻¹) * ‖x‖ ^ i := by
  have h1 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • x ^ i) (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  have h2 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • ‖x‖ ^ i) (Real.exp ‖x‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  have h1' := (hasSum_nat_add_iff' m).mpr h1
  have h2' := (hasSum_nat_add_iff' m).mpr h2
  simp only [smul_eq_mul] at h2'
  refine h1'.norm_le_of_bounded h2' (fun i => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x _) (by positivity)

theorem norm_exp_le' (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  simpa using norm_exp_sub_partial_le x 0

end Trotter

section Mat

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

end Mat

end PI.IwaMeasEx.Gauge.ZetaZeros

end
