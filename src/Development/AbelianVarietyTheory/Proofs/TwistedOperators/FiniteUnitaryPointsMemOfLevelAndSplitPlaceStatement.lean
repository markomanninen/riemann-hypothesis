module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryPointsMemOfLevelAndSplitPlace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteUnitaryPoints_mem_of_level_and_split_place : ∀ {D : D7} (V : HSp D) (H : Subgroup (GA D V)) (N : ℕ), 0 < N → (∀ g ∈ GfC V, ∀ m : ℕ, 0 < m → g ^ m ∈ H → g ∈ H) →
    (∀ k ∈ GfC V, GlobalTheory.Member.FinCong V N k → k ∈ H) → (∀ e, IsSplitIdem D e → ∀ g, Formalism.L2.Theta.SuppAt e V g → g ∈ H) → ∀ g ∈ GfC V, g ∈ H := by
  first | exact @GlobalTheory.FinPtsGen.mem_of_level_of_split | exact GlobalTheory.FinPtsGen.mem_of_level_of_split | (intros; apply GlobalTheory.FinPtsGen.mem_of_level_of_split <;> assumption)
