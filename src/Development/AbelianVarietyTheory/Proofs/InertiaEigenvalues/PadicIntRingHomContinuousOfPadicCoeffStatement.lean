module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntRingHomContinuousOfPadicCoeff
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot

@[expose] public section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_ringHom_continuous_of_padicCoeff' : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → ∀ φ : ℤ_[p] →+* O, Continuous φ := by
  first | exact @GlobalTheory.padicInt_ringHom_continuous_of_padicCoeff | exact GlobalTheory.padicInt_ringHom_continuous_of_padicCoeff | (intros; apply GlobalTheory.padicInt_ringHom_continuous_of_padicCoeff <;> assumption)
