module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPolynomialBoundRunConstantsDegreeFour
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
public import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
public import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_bound_runConstants_degree_four : ∃ C₀ : ℝ → ℝ → ℝ → ℝ, (∀ a b c, 0 ≤ C₀ a b c) ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CA CR Ck Tt cc : ℝ), WeightAlgebra.ParA large₂ CA → Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L → InR D j → j < D.R.m → 3 ≤ D.R.r → 0 ≤ CR → ka.size ≤ Ck * (D.R.k : ℝ) * (D.R.f : ℝ) * large₂.sc.b → 0 < Tt → 0 < cc → Tt * cc ≤ 1 → 1 ≤ zBase large₂ ∧ GlobalTheory.ArcCM.RoomAt large₂ j ka CR Tt cc (C₀ CA CR Ck) 4 := by
  first | exact @GlobalTheory.ArcCM.Room.room_four | exact GlobalTheory.ArcCM.Room.room_four | (intros; apply GlobalTheory.ArcCM.Room.room_four <;> assumption)
