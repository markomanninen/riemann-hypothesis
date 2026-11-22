module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondGelfandInvariantValueEq
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondGelfandInvariant_value_eq : ∀ (n : ℕ) (lam : Fin n → ℂ), GlobalTheory.Dec.gelfVal lam 2 = ∑ a, lam a ^ 2 - ((rhoSq n : ℚ) : ℂ) := by
  first | exact @GlobalTheory.GelfandTwo.gelfVal_two | exact GlobalTheory.GelfandTwo.gelfVal_two | (intros; apply GlobalTheory.GelfandTwo.gelfVal_two <;> assumption)
