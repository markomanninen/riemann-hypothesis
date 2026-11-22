module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionRankLowerBoundOfHilbertSamuel
public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Formalism.HarderNarasimhan.StatementPl

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalSectionRankLowerBound_of_hilbertSamuel : Quoted → RankLow := by
  first | exact @GlobalTheory.HSCore.RankBound.rankLow | exact GlobalTheory.HSCore.RankBound.rankLow | (intros; apply GlobalTheory.HSCore.RankBound.rankLow <;> assumption)
