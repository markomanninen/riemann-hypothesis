module

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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative

@[expose] public section

noncomputable section

namespace Formalism.L2.S.S7.IwasawaBase

open MeasureTheory NumberField
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates

variable (I : AutInst)

theorem muA_right (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] : (I.muA μf).IsMulRightInvariant := by
  have : μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds I μf
  exact rr_muA_right I μf

end Formalism.L2.S.S7.IwasawaBase

end
