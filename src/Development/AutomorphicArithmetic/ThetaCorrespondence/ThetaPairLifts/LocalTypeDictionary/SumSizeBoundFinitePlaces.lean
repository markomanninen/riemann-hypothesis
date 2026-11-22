module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDlNonneg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Imports
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsTer
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsBis
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RatMove
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.KerStd
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.MatLat
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LatMove
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LossOne
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ExpLoss
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PairIntRatKOfThetaLocalInputs

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open GlobalTheory.SumSize
namespace GlobalTheory.SumSize
theorem finite_place_sum_size_bound (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) (hD : DictK) (hd : DepthK) : FinRowK := by
  have hG : PairInt.PairIntRatK := _root_.GlobalTheory.T.pairIntRatK_of_thetaLocalInputs hP hI hD
  obtain ⟨CF0, h⟩ := BigC.and hG hd
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C hC
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  obtain ⟨⟨dl, hL, h⟩, hDe⟩ := h D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3
  refine ⟨dl, hL, ?_⟩
  intro t w hw Φ β d hO c i a v hv
  obtain ⟨hβ, τ, hτ, hdτ⟩ := hO
  have hrat := (h3.isRatAt hβ hτ hdτ c).2 i
  obtain ⟨hk, ⟨e, -, hPz, -⟩, hcos⟩ := hτ
  have hdep := (hDe t Φ β hβ).2
  exact h t (.chi i D.R.m) ⟨i.2, rfl⟩ w hw _ (d.2 i) hk ((hcos d hdτ).2 i) ((hPz d hdτ).2 i).2.2 ((hPz d hdτ).2 i).1
    (fun l hl hlw => hdep w l hl hlw hw) _ _ hrat a v hv
end GlobalTheory.SumSize
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_size_bound_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → FinRowK := by
  first | exact @_root_.GlobalTheory.SumSize.finite_place_sum_size_bound | exact _root_.GlobalTheory.SumSize.finite_place_sum_size_bound | (intros; apply _root_.GlobalTheory.SumSize.finite_place_sum_size_bound <;> assumption)
end
