module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogCardLevelGroupLeScalePowMulLength
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
theorem _root_.GlobalTheory.T.exists_log_card_restRows_le_pow_mul_length : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ C * x ^ C * (Fm.L x i).sc.L := by
  first | exact @GlobalTheory.NLink.log_card_levelGroup_le_scale_pow_mul_length | exact GlobalTheory.NLink.log_card_levelGroup_le_scale_pow_mul_length | (intros; apply GlobalTheory.NLink.log_card_levelGroup_le_scale_pow_mul_length <;> assumption)
