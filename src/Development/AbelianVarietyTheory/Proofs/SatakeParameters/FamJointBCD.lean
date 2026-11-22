module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.ClusteredLetterwiseBoxes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLongOrbitWordConditionsOfLargeScale
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeWordConditionsOfLargeScale
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamJEpsPos

@[expose] public section

open NumberField IsDedekindDomain Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem HTW.RecS.fam_jointBCD : ∀ {eps : ℝ} (Fm : FamP eps) (R : KillingConditions.RowK), (∀ D : D7, LocalSituation.adm7 D) → (∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (j : Fm.Ix x) (HW : HWOf (Fm.D x j).loc) (X : KillingConditions.HubData (Fm.D x j)), GlobalTheory.HTW.LJ.ConclusionJa (Fm.D x j) → (∀ i, TwistedPlaces.TwLoc (Fm.D x j) i → TwistedPlaces.InertK (Fm.D x j) ((Fm.D x j).nd.l i) → ∀ π ∈ (Fm.D x j).nd.Zgood i, GlobalTheory.HTW.RecS.PtIn i (X.r i) (X.ρ i) π) → KillingConditions.JointParametersHubConditions (Fm.L x j) HW X R := by
  intro eps Fm R a b
  obtain ⟨x0, h⟩ := GlobalTheory.HTW.RecS.fam_joints Fm R.C₂ a b
  exact ⟨x0, fun x hx h1 j HW X hJ hP =>
    GlobalTheory.Survey.ClusteredLetterwiseBoxes.frozenBCD_of _ HW X R (h x hx h1 j HW hJ).1 (h x hx h1 j HW hJ).2 hP⟩

end GlobalTheory
