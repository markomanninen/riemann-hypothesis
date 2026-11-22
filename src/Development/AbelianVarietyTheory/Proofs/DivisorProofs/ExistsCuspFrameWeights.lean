module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.DataParamsT
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCmPtFrPolyNeZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolyDivDet
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartWD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCoverComponentExtendsToRankOneCuspData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFrameReadingNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldFrameValueNeZeroOfComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCmStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortLatticeSpanningSets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortGeneratorsOfShortSpanningFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormComponentAddLeOfGramFrameStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatFrameOfIsShortGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtBigRun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameBerg

theorem one_le_gap_of_strictAnti {N : ℕ} {v : Fin N → ℤ} (hv : StrictAnti v) {k : ℕ} (hk : k + 1 < N) :
    1 ≤ gap v k := by
  rw [gap, dite_eq_left hk]
  have := hv (show (⟨k, by omega⟩ : Fin N) < ⟨k + 1, hk⟩ from Fin.mk_lt_mk.2 (Nat.lt_succ_self k))
  omega

theorem gap_add {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

theorem antitone_of_gap_nonneg {N : ℕ} {v : Fin N → ℤ} (h : ∀ k, k + 1 < N → 0 ≤ gap v k) : Antitone v := by
  have key : ∀ d (a b : Fin N), (b : ℕ) = a + d → v b ≤ v a := by
    intro d
    induction d with
    | zero =>
      intro a b hab
      have e : b = a := Fin.ext (by simpa using hab)
      rw [e]
    | succ d ih =>
      intro a b hab
      have hc : (a : ℕ) + d < N := by omega
      have h1 := ih a ⟨(a : ℕ) + d, hc⟩ rfl
      have h2 := h ((a : ℕ) + d) (by omega)
      rw [gap, dite_eq_left (by omega)] at h2
      have e : b = ⟨(a : ℕ) + d + 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [e]
      linarith
  intro a b hab
  exact key ((b : ℕ) - a) a b (by have : (a : ℕ) ≤ b := hab; omega)

end GlobalTheory.FrameBerg

namespace GlobalTheory.FrameBerg


end GlobalTheory.FrameBerg
