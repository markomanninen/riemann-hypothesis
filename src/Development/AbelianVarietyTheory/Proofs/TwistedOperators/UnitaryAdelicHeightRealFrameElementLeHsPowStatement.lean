module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightRealFrameElementLeHsPow
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicHeight_realFrameElement_le_hsPow : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau), ∃ (C : ℝ) (m : ℕ), ∀ g ∈ Formalism.MainNotions.S.UJset (A.ε τ), GlobalTheory.Grow.height V (A.elt θ τ g) ≤ C * (1 + Formalism.REAL.hs g) ^ m := by
  first | exact @GlobalTheory.FrameHeight.height_elt_le | exact GlobalTheory.FrameHeight.height_elt_le | (intros; apply GlobalTheory.FrameHeight.height_elt_le <;> assumption)
