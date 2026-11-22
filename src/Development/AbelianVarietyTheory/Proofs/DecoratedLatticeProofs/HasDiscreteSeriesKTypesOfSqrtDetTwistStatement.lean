module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfSqrtDetTwist
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
theorem _root_.GlobalTheory.T.hasDiscreteSeriesKTypes_of_sqrtDetTwist : ∀ (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ), HasTypes (Cover.twist R) lam → HasTypes R fun a => lam a + 1 / 2 := by
  first | exact @GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist | exact GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist | (intros; apply GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist <;> assumption)
