module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantEtaleBasisChangeByOEUnit
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
theorem _root_.GlobalTheory.T.invariantEtaleBasis_change_by_OE_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (T0 Wm Wm' A0 A0' : Matrix (Fin d) (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T0.map (galW l (g : GQ l)) = T0) → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T0.map (frobW l) = T0 * A0 → A0 * A0' = 1 → (∀ i j, Wm i j ∈ bk.OE) → (∀ i j, Wm' i j ∈ bk.OE) → Wm * Wm' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * (T0 * Wm).map (galW l (g : GQ l)) = T0 * Wm) ∧ ∃ A1 A1' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A1 i j ∈ bk.OE) ∧ (∀ i j, A1' i j ∈ bk.OE) ∧ (T0 * Wm).map (frobW l) = (T0 * Wm) * A1 ∧ A1 * A1' = 1 := by
  first | (exact @GlobalTheory.ChangeEtaleBasis.main) | (exact GlobalTheory.ChangeEtaleBasis.main) | (intros; apply GlobalTheory.ChangeEtaleBasis.main  <;> assumption)
