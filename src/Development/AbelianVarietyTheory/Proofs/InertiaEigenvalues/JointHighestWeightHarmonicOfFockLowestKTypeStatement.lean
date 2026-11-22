module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHighestWeightHarmonicOfFockLowestKType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZRYRCover
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKHwMap

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointHighestWeightHarmonic_of_fock_lowestKType : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P : PolF D m n), GlobalTheory.LowestKType.IsHarm w P → GlobalTheory.LowestKType.IsNHw w lam P → GlobalTheory.LowestKType.IsKHw w P → ∀ τ : D.what₂.Tau, ∃ (α : Fin (min (w.p τ) m) → ℂ) (β : Fin (m - w.p τ) → ℂ), GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ GlobalTheory.HarmLine.zR m n (w.p τ)) (Prod.mk τ ∘ GlobalTheory.HarmLine.yR m n (w.p τ)) (fun a => lam τ a - (m : ℂ) / 2 + ((m - w.p τ : ℕ) : ℂ)) α β P := by
  first | exact @GlobalTheory.JointDict.jointTop_of_lowestKType | exact GlobalTheory.JointDict.jointTop_of_lowestKType | (intros; apply GlobalTheory.JointDict.jointTop_of_lowestKType <;> assumption)
