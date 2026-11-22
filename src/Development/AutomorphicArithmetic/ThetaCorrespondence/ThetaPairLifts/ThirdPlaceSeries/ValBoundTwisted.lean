module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataConjugate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataAbelian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAutCentre
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormToricRatio
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCMValueHeckeCharacterAuxiliarySetOfEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueValuationLeDivSqStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValuesAsToricSumsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToricRatioFieldDataCm
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadTwistedStatement

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
noncomputable section
namespace GlobalTheory.ThmAUpper
theorem val_bound_twisted_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → (∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c : Option Bool,
    ∃ x, IsTor d.G i j s (fam d.G p.P.A3.A.μ0 i j c) x ∧ x ≠ 0 ∧ (∀ Λ, GlobalTheory.CMVal.IsHeckeL (fam d.G p.P.A3.A.μ0 i j c) Λ → x = Λ s) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) Λ x)) →
  ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ) (z : D.what₂.LL), 1 ≤ s → s ≤ halfRank D i j →
    GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) * p.Tp.psi w) Λ →
    GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) Λd →
    D.what₂.embLL z * Λd s = Λ s →
    (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) ≤ (Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) : ℝ) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ 2 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d hp hfit hG hF hT w hw i j s Λ Λd z hs1 hs2 hΛ hΛd hz
  obtain ⟨T₀, ψc, T, hv, h0, h0ne, hd, hψ, hT', hΛs⟩ := _root_.GlobalTheory.T.toric_ratio_field_data_conjugate_alt p CF d hp hfit hG hF hT w hw i j s Λ Λd hs1 hs2 hΛ hΛd
  obtain ⟨lam, a, u, ha, he⟩ := _root_.GlobalTheory.T.toric_ratio_field_data_cm_alt p CF d hp hfit hG hF w hw i j s hs1 hs2 T₀ ψc T hv h0 h0ne hψ hT' z
    (by rw [← hd, hz, hΛs]) (_root_.GlobalTheory.T.toric_ratio_field_data_abelian_alt p CF d hp hfit hG hF w hw i j s hs1 hs2 T₀ ψc T hv h0 h0ne hψ hT')
  obtain ⟨N0, hN⟩ := hfit.1.powers
  exact GlobalTheory.T.twistedThetaValue_valuation_le_div_sq ex.nch w N0 lam a u z (hN w hw a ha) he
end GlobalTheory.ThmAUpper
end
end
