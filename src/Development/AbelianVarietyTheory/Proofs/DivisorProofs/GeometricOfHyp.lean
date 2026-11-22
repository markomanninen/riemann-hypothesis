module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.DataParamsT
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
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
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqOfGenericUniqueComplexPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierCompl
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeilStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovHt.GeomBound

theorem strictAnti_of_step {N : ℕ} {f : Fin N → ℤ} (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b < f a) : StrictAnti f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_lt_mk] at hab
  induction b with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'
    · exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega) h')
    · subst h'
      exact h ⟨a, ha⟩ ⟨a + 1, hb⟩ rfl

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem quo_gaps {PP A M : ℝ} (hN : HostNum D L PP A M) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m)
    (u1 : AllWt.Weight (dat p i)) (hu : Quo p i PP u1) :
    ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 →
      (((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℤ) ≤ u1 τ a - u1 τ b := by
  obtain ⟨hsig1, hsig2, hsigr⟩ := hw.sig
  obtain ⟨h0, S, eta, -, -, -, h4T, -, hHyp⟩ := hw.hyp hi
  have hdiv := (quo_iff p i PP h0 S eta u1).1 hu
  have G := GlobalTheory.MeanTop.divided_gaps _ _ _ (hHyp u1) hdiv
  simp only [wtsAt] at G
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hp1 : 1 ≤ (dat p i).p := by rw [hsig1]; simp only [Ranks.sigW]; omega
  have hq1 : 1 ≤ (dat p i).q := by rw [hsig2]; simp only [Ranks.sigW]; omega
  have hr2 : 2 ≤ D.R.r := by omega
  have hD1 : 1 ≤ dimFlag (dat p i) := by
    rw [hw.dim]
    exact Nat.mul_pos (by have := hN.f8; omega) (Nat.choose_pos hr2)

  have hz : (4 : ℝ) ≤ zBase L := by
    unfold zBase
    have c1 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
    have c2 : (2 : ℝ) ≤ D.R.r := by exact_mod_cast hr2
    have c3 : (10 : ℝ) ≤ L.sc.L := hN.big.2.1
    have : (8 : ℝ) * 2 * 10 ≤ D.R.f * D.R.r * L.sc.L := by gcongr
    linarith
  have hPP : (4 : ℝ) ≤ PP := hz.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hN.ppLow)
  have hT : 16 * dimFlag (dat p i) ^ 2 ≤ lenT p i PP := by
    have h1 : (16 * dimFlag (dat p i) ^ 2 : ℝ) ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
      have c3 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
      have c4 : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
      have c5 : (16 : ℝ) ≤ PP ^ 2 := by nlinarith
      rw [le_div_iff₀ c3]
      have c6 : (0 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2 := by positivity
      calc (16 * (dimFlag (dat p i) : ℝ) ^ 2) * D.R.m ≤ (PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2) * D.R.m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c5 c6) c3.le
        _ ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * D.R.k := mul_le_mul_of_nonneg_left c4 (by positivity)
    have h2 := h1.trans (Nat.le_ceil _)
    unfold lenT
    exact_mod_cast h2
  intro τ a b hb
  obtain ⟨g1, g2, -⟩ := G τ a b hb
  have hTz : (16 * (dimFlag (dat p i) : ℤ) ^ 2) ≤ (lenT p i PP : ℤ) := by exact_mod_cast hT
  have hD1z : (1 : ℤ) ≤ dimFlag (dat p i) := by exact_mod_cast hD1
  have hsq : (dimFlag (dat p i) : ℤ) ≤ (dimFlag (dat p i) : ℤ) ^ 2 := by nlinarith
  push_cast at G ⊢
  by_cases hbp : (b : ℕ) = (dat p i).p
  · have g := (g2 hbp).2
    have hT0 : (0 : ℤ) < 4 * (lenT p i PP : ℤ) := by nlinarith
    have hle : (lenT p i PP : ℤ) ≤ u1 τ a - u1 τ b - 3 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hT0
      nlinarith
    push_cast at hle
    linarith
  · have g := g1 hbp
    push_cast at g
    linarith

end Point

end GlobalTheory.CovHt.GeomBound

end
