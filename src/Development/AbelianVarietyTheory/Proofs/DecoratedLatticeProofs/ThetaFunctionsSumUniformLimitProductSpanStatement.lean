module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsSumUniformLimitProductSpan
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunctions_sum_uniform_limit_product_span : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), ∀ f, IsThetaFunO ψ S T f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS T) (IsThetaFunO ψ A T) (IsThetaFunO ψ B T)) f := by
  first | exact @GlobalTheory.DenseSum.unifLimit_prodSpan | exact GlobalTheory.DenseSum.unifLimit_prodSpan | (intros; apply GlobalTheory.DenseSum.unifLimit_prodSpan <;> assumption)
