module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARParts
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∃ X : ProvA, (∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam) ∧ DiscreteSeriesBlattner X ∧ admQ5 X ∧ ArchimedeanRallisFirst X ∧ ArchimedeanRallisSecond X ∧ ArchimedeanRallisUpDownLine X ∧ ArchimedeanRallisFifth X := by
  first | exact @GlobalTheory.RealPlaceTheta.exists_record_theta | exact GlobalTheory.RealPlaceTheta.exists_record_theta | (intros; apply GlobalTheory.RealPlaceTheta.exists_record_theta <;> assumption)
