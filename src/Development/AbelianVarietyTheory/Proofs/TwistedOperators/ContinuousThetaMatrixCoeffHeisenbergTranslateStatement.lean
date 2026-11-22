module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousThetaMatrixCoeffHeisenbergTranslate
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_thetaMatrixCoeff_heisenbergTranslate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → Continuous (fun w : WO S T => thPair μ 𝓕 f (heisO ψ S T w f₀)) := by
  first | exact @GlobalTheory.MatCoefCont.continuous_thPair_heisO | exact GlobalTheory.MatCoefCont.continuous_thPair_heisO | (intros; apply GlobalTheory.MatCoefCont.continuous_thPair_heisO <;> assumption)
