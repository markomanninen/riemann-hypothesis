module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorPrimesLtSpecialPrimeThresholdEventually
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
public import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductorPrimes_lt_specialPrimeThreshold_eventually : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x),
    ((Fm.D x a).host.q : ℝ) < LevelStarExponents.lStar (Fm.L x a) ∧ ((Fm.D x a).host.d : ℝ) < LevelStarExponents.lStar (Fm.L x a) ∧
      ∀ p ∈ (Fm.D x a).host.small, (p : ℝ) < LevelStarExponents.lStar (Fm.L x a) := by
  first | exact @GlobalTheory.LevelBelowStarBound.QdSmall.qd_lt_lStar | exact GlobalTheory.LevelBelowStarBound.QdSmall.qd_lt_lStar | (intros; apply GlobalTheory.LevelBelowStarBound.QdSmall.qd_lt_lStar <;> assumption)
