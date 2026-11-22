module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanInst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.BcExAll
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.Dict

theorem readings_independent :
    ∀ (D : D7) (T : Top D), LawsM T.toCore → ∀ j, InR D j → ∀ a n, JInjRd T j a n := by
  intro D T hM j hj a n

  have hA := GlobalTheory.FramedBaseChange.bcEx_all _ _ _ _ (T.Q.Xo j) T.Q.c T.σ₀
  have hF := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.2.1
  exact jInjRd_of_wt T hM hj a n hA hF

end GlobalTheory.Dict
