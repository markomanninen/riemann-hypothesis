module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.H1H2LocalDuality
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
public import ReciprocityTheory.Hypotheses.GalCoh

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hOneTwo_of_localFiniteness_tateDuality_eulerChar : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ D : D7, HOneTwo D := by
  first | exact @GlobalTheory.HOneTwoLevel.hOneTwo_holds | exact GlobalTheory.HOneTwoLevel.hOneTwo_holds | (intros; apply GlobalTheory.HOneTwoLevel.hOneTwo_holds <;> assumption)
