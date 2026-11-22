module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteOfPadicCoeff
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot

@[expose] public section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_of_padicCoeff' : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  first | exact @GlobalTheory.isAdicComplete_of_padicCoeff | exact GlobalTheory.isAdicComplete_of_padicCoeff | (intros; apply GlobalTheory.isAdicComplete_of_padicCoeff <;> assumption)
