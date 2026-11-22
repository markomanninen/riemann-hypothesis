module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SaturatedAinfLatticeFreeOverBreuilKisin
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
theorem _root_.GlobalTheory.T.saturatedAinfLattice_free_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (T0 V V' : Matrix (Fin d) (Fin d) (WCb l)) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T0 → (∀ i j, V i j ∈ bk.OE) → (∀ i j, V' i j ∈ bk.OE) → V * V' = 1 → Y1.map (inclW l) = inclW l τ ^ N • (T0 * V) → ∃ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Wm Wm' : Matrix (Fin d) (Fin d) (WCb l)), IsUnit (Y.map (inclW l)) ∧ (∀ i j, Wm i j ∈ bk.OE) ∧ (∀ i j, Wm' i j ∈ bk.OE) ∧ Wm * Wm' = 1 ∧ Y.map (inclW l) = inclW l τ ^ N • (T0 * Wm) ∧ ∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a) := by
  first | (exact @GlobalTheory.BKLim.SatLat.main) | (exact GlobalTheory.BKLim.SatLat.main) | (intros; apply GlobalTheory.BKLim.SatLat.main  <;> assumption)
