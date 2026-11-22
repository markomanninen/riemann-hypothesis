module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDomainWeightBound
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationEStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnramifiedCurve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointLiesOnComponentCmCurveFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedPointCompletionIndexOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningFamilyMulTwistingSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyUnitPowTwistingSectionOnComponentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortIntegralFlatLineTwistingSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaWeightExponentsOfLargeGapStatement
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.BadLog
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfMemBadPrimes
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotDvdDiscrHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightAndFlatExponentSizeBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNumericalBoundsCollectStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogThetaWeightSizeLeStatement

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
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

namespace GlobalTheory.ShortSpanComp

theorem petOn_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G')
    (σ : c.F →+* ℂ) (f : Rul Xo c) : petOn U x V dict Z G σ f = petOn U x V dict Z G' σ f := by
  unfold petOn AllWt.petAt
  have hm : AllWt.modelWt (U (goodOf c σ)) G = AllWt.modelWt (U (goodOf c σ)) G' :=
    AllWt.modelWt_congr _ (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) h
  have hl : AllWt.lieFacZ Dw x G = AllWt.lieFacZ Dw x G' := by
    unfold AllWt.lieFacZ
    have hs : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), G.1 (τ, (i : ℕ)) = G'.1 (τ, (i : ℕ)) := fun τ i =>
      congrFun h (some ⟨τ, i⟩)
    simp only [hs]
  rw [hm, hl]

theorem exZ_laOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n) :
    exZ Dw (wtOf Dw (laOf Dw a n) ((n / 2 : ℕ) : ℤ)) = exZ Dw (wtZ a n) := by
  have h := AllWt.exOf_weightOf (Dw := Dw) (fun x => (a x : ℤ)) ((n / 2 : ℕ) : ℤ)
  have h2 : (2 * ((n / 2 : ℕ) : ℤ)) = (n : ℤ) := by
    obtain ⟨k, rfl⟩ := hn
    have : (k + k) / 2 = k := by omega
    rw [this]; push_cast; ring
  rw [h2] at h
  exact h

theorem cuspW_laOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n) :
    cuspW Xo c U (wtZ a n) = cuspW Xo c U (wtOf Dw (laOf Dw a n) ((n / 2 : ℕ) : ℤ)) := by
  have h := AllWt.cuspZ_weightOf (Dw := Dw) hU a (n / 2)
  have h2 : 2 * (n / 2) = n := by obtain ⟨k, rfl⟩ := hn; omega
  rw [h2] at h
  rw [AllWt.cuspW_wtZ, ← h]
  rfl

theorem lrd_bounds (K : Type) [Field K] [NumberField K] : 0 ≤ lrd K ∧ lrd K ≤ fieldSz K := by
  have hd : (1 : ℝ) ≤ |(discr K : ℝ)| := by
    have h := Int.one_le_abs (discr_ne_zero K)
    rw [← Int.cast_abs]; exact_mod_cast h
  have hdpos : (0 : ℝ) < |(discr K : ℝ)| := lt_of_lt_of_le one_pos hd
  have e : lrd K = Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
    unfold lrd
    rw [NumberField.rootDiscr_def, Int.cast_abs, Real.log_rpow hdpos]
    ring
  refine ⟨?_, ?_⟩
  · rw [e]; exact div_nonneg (Real.log_nonneg hd) (Nat.cast_nonneg _)
  · rw [e]; exact log_rd_le_fieldSz K

end GlobalTheory.ShortSpanComp

namespace GlobalTheory.ShortSpanComp


end GlobalTheory.ShortSpanComp
