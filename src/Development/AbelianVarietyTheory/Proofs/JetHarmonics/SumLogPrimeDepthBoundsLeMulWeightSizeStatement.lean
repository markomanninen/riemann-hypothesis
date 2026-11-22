module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumLogPrimeDepthBoundsLeMulWeightSize
public import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
public import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
public import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_log_prime_depth_bounds_le_mul_weight_size : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j), 1 ≤ w.n → Real.log (WeightAlgebra.DF w) ≤ 2 * large₂.sc.L → (WeightAlgebra.DF w : ℝ) * (Real.log (WeightAlgebra.DF w) + 2.2) + (c2 D w * Real.log D.host.QS + cHalf w * Real.log D.host.q + cHalf w * Real.log D.host.d) + ∑ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤ WeightAlgebra.PN D large₂ * w.size := by
  first | exact @GlobalTheory.PtTie.depth_sum_le_PN | exact GlobalTheory.PtTie.depth_sum_le_PN | (intros; apply GlobalTheory.PtTie.depth_sum_le_PN <;> assumption)
