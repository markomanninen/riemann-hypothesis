module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
public import Mathlib
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

theorem GlobalTheory.spanShortSize : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (la : AllWt.Weight Dw) (n₀ : Psi H → ℤ) (hp : 1 ≤ Dw.p), laOf Dw a n = la + GlobalTheory.FlatLine.parWt Dw n₀ → (∀ τ, n₀ τ = 1 + ((n / 2 : ℕ) : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) → sizeK Dw a n ≤ (1 + ((Dw.p + Dw.q : ℕ) : ℝ)) * ∑ τ, ∑ k, |(la τ k : ℝ)| + ((Dw.p + Dw.q : ℕ) : ℝ) * (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) ∧ ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) := by
  intro E _ _ _ H Dw a n la n₀ hp hla hn₀
  have hS : ∀ τ, |(n₀ τ : ℝ)| ≤ ∑ k, |(la τ k : ℝ)| + (((n / 2 : ℕ) : ℝ) + 1) := by
    intro τ
    have h1 : (n₀ τ : ℝ) = 1 + ((n / 2 : ℕ) : ℝ) - (la τ ⟨Dw.p - 1, by omega⟩ : ℝ) := by
      rw [hn₀ τ]; simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast]
    have h2 : |(la τ ⟨Dw.p - 1, by omega⟩ : ℝ)| ≤ ∑ k, |(la τ k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(la τ k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    have h3 : (0:ℝ) ≤ ((n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [h1]
    calc |1 + ((n / 2 : ℕ) : ℝ) - (la τ ⟨Dw.p - 1, by omega⟩ : ℝ)|
        ≤ |1 + ((n / 2 : ℕ) : ℝ)| + |(la τ ⟨Dw.p - 1, by omega⟩ : ℝ)| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg (by linarith)]; linarith
  have hsum : ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) := by
    calc ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, (∑ k, |(la τ k : ℝ)| + (((n / 2 : ℕ) : ℝ) + 1)) := Finset.sum_le_sum (fun τ _ => hS τ)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]
  refine ⟨?_, hsum⟩
  have hK : sizeK Dw a n = ∑ τ, ∑ k : Fin (Dw.p + Dw.q), |((la τ k : ℝ) + (n₀ τ : ℝ))| := by
    unfold sizeK
    refine Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hla]
    simp [GlobalTheory.FlatLine.parWt]
  have hT : sizeK Dw a n ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + ((Dw.p + Dw.q : ℕ) : ℝ) * ∑ τ, |(n₀ τ : ℝ)| := by
    rw [hK, Finset.mul_sum]
    calc ∑ τ, ∑ k : Fin (Dw.p + Dw.q), |((la τ k : ℝ) + (n₀ τ : ℝ))|
        ≤ ∑ τ, ∑ k : Fin (Dw.p + Dw.q), (|(la τ k : ℝ)| + |(n₀ τ : ℝ)|) :=
          Finset.sum_le_sum (fun τ _ => Finset.sum_le_sum (fun k _ => abs_add_le _ _))
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpq : (0:ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := Nat.cast_nonneg _
  have hS0 : (0:ℝ) ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  nlinarith [mul_le_mul_of_nonneg_left hsum hpq]
