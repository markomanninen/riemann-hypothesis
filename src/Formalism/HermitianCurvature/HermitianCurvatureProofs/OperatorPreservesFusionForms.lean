module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmBorderES
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmBorderFull
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmMove
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmSandwich
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnLevBasics
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnGlevImage
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnLevTransfer
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleLeft
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleTorus
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTInv
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTPres
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmCapComm
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnHermHaar
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylCellRange.ReflectionMultiplicationOnBigCell

@[expose] public section

theorem Formalism.FourierDecayAlt.P.border_first_expansion : Formalism.FourierDecayAlt.Q.BorderE := by
  exact quantum_minor_border_es.1

theorem Formalism.FourierDecayAlt.P.border_last_expansion : Formalism.FourierDecayAlt.Q.BorderS := by
  exact quantum_minor_border_es.2

theorem Formalism.FourierDecayAlt.P.border_full_expansion : Formalism.FourierDecayAlt.Q.BorderFull := by
  exact quantum_minor_border_full

theorem Formalism.FourierDecayAlt.P.rtt_sandwich : Formalism.FourierDecayAlt.Q.RTTSandwich := by
  exact rtt_sandwich'

theorem Formalism.FourierDecayAlt.P.level_group_image : Formalism.FourierDecayAlt.Q.GlevImage := by
  obtain ⟨hH, hU, -⟩ := level_basics
  exact gl_level_image hH hU

theorem Formalism.FourierDecayAlt.P.level_transfer : Formalism.FourierDecayAlt.Q.LevelTransfer := by
  exact level_transfer_of_levHom level_basics.1

theorem Formalism.FourierDecayAlt.P.left_action_rule : Formalism.FourierDecayAlt.Q.RuleLeft := by
  exact qnRuleLeft

theorem Formalism.FourierDecayAlt.P.torus_action_rule : Formalism.FourierDecayAlt.Q.RuleTorus := by
  exact qnRuleTorus

theorem Formalism.FourierDecayAlt.P.operator_invariance : Formalism.FourierDecayAlt.Q.TInvariant := by
  exact qnTInv

theorem Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms : Formalism.FourierDecayAlt.Q.TPreservesFF := by
  exact qnTPres

theorem Formalism.FourierDecayAlt.P.capelli_commutation : Formalism.FourierDecayAlt.Q.CapCommute := by
  exact capelli_det_commute

theorem Formalism.FourierDecayAlt.P.hermitian_haar_invariance : Formalism.FourierDecayAlt.Q.HermHaar := by
  exact qnHermHaar
