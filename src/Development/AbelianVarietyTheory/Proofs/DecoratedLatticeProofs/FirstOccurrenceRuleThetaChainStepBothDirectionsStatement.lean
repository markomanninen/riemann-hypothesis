module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstOccurrenceRuleThetaChainStepBothDirections
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstOccurrenceRule_thetaChainStep_both_directions : ∀ (D : D7) (X : ProvA), Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → ∀ k : Fin D.R.m, ChainPar D k → ∀ τ, RulePar X (parB (Ptw D) k τ) (parB (Ptw D) (k + 1) τ) (expS D k τ) (expT D k τ) ∧ RulePar X (parB (Ptw D) (k + 1) τ) (parB (Ptw D) k τ) (expT D k τ) (expS D k τ) := by
  first | exact @GlobalTheory.StepRule.rulePar_step | exact GlobalTheory.StepRule.rulePar_step | (intros; apply GlobalTheory.StepRule.rulePar_step <;> assumption)
