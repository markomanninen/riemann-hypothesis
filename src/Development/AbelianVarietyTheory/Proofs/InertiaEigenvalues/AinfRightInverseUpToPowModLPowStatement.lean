module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfRightInverseUpToPowModLPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimitStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatPowDvdPerPowMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTowerStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPolesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverseStatement

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_rightInverse_up_to_pow_mod_lPow : ∀ (l : ℕ) [Fact l.Prime] (d d' n M : ℕ) (τ : Ainf l) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d') (Ainf l)) (Q : Matrix (Fin d') (Fin d) (Ainf l)), IsUnit (inclW l τ) → IsUnit (Y.map (inclW l)) → Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (A * Q).map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → ∀ i j, (l : Ainf l) ^ n ∣ (A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j := by
  first | exact @GlobalTheory.AinfRinv.rinv_mod_pow | exact GlobalTheory.AinfRinv.rinv_mod_pow | (intros; apply GlobalTheory.AinfRinv.rinv_mod_pow <;> assumption)
