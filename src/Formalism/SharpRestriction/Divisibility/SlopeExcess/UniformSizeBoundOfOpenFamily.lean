module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.LocalRingCardinality.DataKap
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
public import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues
public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIVDefs
public import Formalism.DegreeFormula.FlagDegFormula
public import Formalism.SharpRestriction.Divisibility.LatticeTransfer
public import Formalism.SharpRestriction.Divisibility.PrinLevClass
public import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
public import Formalism.SharpRestriction.Divisibility.WeightFamilies
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Formalism.DegreeFormula.PointDegree.FlagDeg
public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.GelfandTransference.EnergyIdentity
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Formalism.SharpRestriction.Divisibility.AdmissibleRank.FreeFamilyOfLeavesAndAdmissible
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop
public import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
public import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLbud
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV.Proofs

open Formalism.BasicNotions Formalism.MainNotions

theorem top2c2_dlSize (eps : ℝ) (Fm : FamP eps) : J.DlSize Fm := by
  unfold J.DlSize
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := Fm.sizes x hx1 i
  obtain ⟨-, -, -, -, -, h, -⟩ := hQD
  exact h

end Formalism.MainNotions.DIV.Proofs
