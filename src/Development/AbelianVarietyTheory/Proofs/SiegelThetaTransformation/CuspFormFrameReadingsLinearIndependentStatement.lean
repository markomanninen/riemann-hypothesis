module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormFrameReadingsLinearIndependent
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanInst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_frame_readings_linearIndependent : ∀ (D : D7) (T : Top D), LawsM T.toCore → ∀ j, InR D j → ∀ a n, JInjRd T j a n := by
  first | exact @GlobalTheory.Dict.readings_independent | exact GlobalTheory.Dict.readings_independent | (intros; apply GlobalTheory.Dict.readings_independent <;> assumption)
