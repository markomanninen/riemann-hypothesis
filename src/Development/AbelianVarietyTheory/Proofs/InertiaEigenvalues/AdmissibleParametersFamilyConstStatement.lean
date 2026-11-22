module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConst
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_parameters_family_const : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, 1 ≤ C ∧ ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ParametersPolynomiallyBounded (Fm.L x i) C (Fm.params x hx i) := by
  first | exact @GlobalTheory.NLink.admissible_parameters_design_family | exact GlobalTheory.NLink.admissible_parameters_design_family | (intros; apply GlobalTheory.NLink.admissible_parameters_design_family <;> assumption)
