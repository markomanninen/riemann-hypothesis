module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHighestWeightHarmonicMultiplicityOneCoverin
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
theorem _root_.GlobalTheory.T.jointHighestWeightHarmonic_multiplicity_one_covering : ∀ {σ : Type} {k l N : ℕ} (z : Fin k × Fin N → σ) (y : Fin l × Fin N → σ), Function.Injective z → Function.Injective y → (∀ u w, z u ≠ y w) → (∀ s, (∃ u, z u = s) ∨ ∃ w, y w = s) → ∀ κ : Fin N → ℂ, ∃ Q₀ : MvPolynomial σ ℂ, ∀ (α : Fin k → ℂ) (β : Fin l → ℂ) (f : MvPolynomial σ ℂ), GlobalTheory.CompactHarm.JointTop z y κ α β f → ∃ r : ℂ, f = r • Q₀ := by
  first | exact @GlobalTheory.CompactHarm.jointTop_line | exact GlobalTheory.CompactHarm.jointTop_line | (intros; apply GlobalTheory.CompactHarm.jointTop_line <;> assumption)
