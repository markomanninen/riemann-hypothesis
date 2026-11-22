module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeOfDetEqZero
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBoundStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortLatticeSpanningSets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortGeneratorsOfShortSpanningFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormComponentAddLeOfGramFrameStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSeparationRegularDeterminant

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

namespace GlobalTheory.ShortDet

theorem le_choose {f r p q : ℕ} (hf : 8 ≤ f) (hr : 100 ≤ r) (hp : 1 ≤ p) (hq : 1 ≤ q) (h : p + q = r) :
    8 * f * r + 10 ≤ (f * p * q + 1).choose 2 := by
  have h1 : r ≤ p * q + 1 := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hp
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hq
    nlinarith [Nat.zero_le (a * b)]
  rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_assoc f, mul_assoc 8, Nat.le_div_iff_mul_le two_pos]
  generalize p * q = s at h1
  have h2 : f * r ≤ 2 * (f * s) := by
    rw [mul_left_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have h3 : 8 * 99 ≤ f * s := Nat.mul_le_mul hf (by omega)
  generalize f * s = N at h2 h3
  nlinarith

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem antitone_smul_hodgeWt {s : ℤ} (hs : 0 ≤ s) (τ : Psi H) : Antitone ((s • hodgeWt Dw) τ) := fun i j h => by
  have : (i : ℕ) ≤ j := h
  simp only [hodgeWt, CompHt.barWt, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> omega

theorem gap_smul_hodgeWt (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (s : ℤ) (τ : Psi H) : gap ((s • hodgeWt Dw) τ) (Dw.p - 1) = s := by
  have h : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega
  simp only [gap, dif_pos h, hodgeWt, CompHt.barWt, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> omega

theorem size_smul_hodgeWt {s : ℤ} (hs : 0 ≤ s) :
    ∑ τ, ∑ k, |((s • hodgeWt Dw) τ k : ℝ)| ≤ Module.finrank ℚ E * ((Dw.p + Dw.q : ℕ) * s) := by
  have h0 : (0 : ℝ) ≤ s := by exact_mod_cast hs
  refine (Finset.sum_le_card_nsmul _ _ (((Dw.p + Dw.q : ℕ) : ℝ) * s) fun τ _ => ?_).trans ?_
  · refine (Finset.sum_le_card_nsmul _ _ (s : ℝ) fun k _ => ?_).trans (by simp)
    simp only [hodgeWt, CompHt.barWt, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp [h0, abs_of_nonneg h0]
  · rw [nsmul_eq_mul, ← NumberField.Embeddings.card E ℂ]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Fintype.card_subtype_le _) (by positivity)

end Weight


end GlobalTheory.ShortDet
