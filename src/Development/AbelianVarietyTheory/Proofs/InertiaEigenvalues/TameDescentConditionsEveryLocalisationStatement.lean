module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_descent_conditions_every_localisation : ∀ (D : D7) (i : D.nd.Loc), TameCharacterConditions D i ∧ TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i := by
  first | exact @GlobalTheory.TameDesign.main | exact GlobalTheory.TameDesign.main | (intros; apply GlobalTheory.TameDesign.main <;> assumption)
