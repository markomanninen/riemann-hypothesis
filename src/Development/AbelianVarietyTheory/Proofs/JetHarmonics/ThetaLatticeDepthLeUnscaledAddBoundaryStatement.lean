module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLatticeDepthLeUnscaledAddBoundary
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
theorem _root_.GlobalTheory.T.thetaLattice_depth_le_unscaled_add_boundary : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  first | exact @GlobalTheory.RecDepth.depth_le | exact GlobalTheory.RecDepth.depth_le | (intros; apply GlobalTheory.RecDepth.depth_le <;> assumption)
