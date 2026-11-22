module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedStaircaseTensorPeriodicUniformizerPow
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedStaircaseTensor_periodic_uniformizerPow : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s)
    (ϖ : kˣ), IsUnif ϖ → ∀ (e : ℕ) (T : G.Args → ℂ), G.IsTensor ϖ e (oppositePath G.m) T → ∀ (J : G.Level) (keep : Bool)
    (x : ColArgs G) (y : RowArgs G) (v l : Vars G), l ∈ varLat G ϖ (G.m * e) →
    moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y (v + l)) =
      moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y v) := by
  first | exact @GlobalTheory.UnfoldLoss.moved_stair_periodic | exact GlobalTheory.UnfoldLoss.moved_stair_periodic | (intros; apply GlobalTheory.UnfoldLoss.moved_stair_periodic <;> assumption)
