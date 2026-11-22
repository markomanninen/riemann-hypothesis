module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRankLeBergmanBoundGoodCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.DataParamsT
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumSecondStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemSpanCuspOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointsOverComponentOpenSet
public import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ClausesIffExistsUnique

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormRank_le_bergmanBound_goodCover : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (la : AllWt.Weight (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) (β : ℝ), 0 ≤ β → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la β → (Y.rkC la Z : ℝ) ≤ β := by
  first | exact @GlobalTheory.RankBergman.rkC_le_of_bergLe | exact GlobalTheory.RankBergman.rkC_le_of_bergLe | (intros; apply GlobalTheory.RankBergman.rkC_le_of_bergLe <;> assumption)
