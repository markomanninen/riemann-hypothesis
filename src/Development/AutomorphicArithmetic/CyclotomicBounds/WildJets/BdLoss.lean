module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.bdLoss :
    ∀ (D : D7) (w : PlL D) (l : ℕ) [Fact l.Prime], (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → ∀ (z : ℂ) (B : ℝ), z ∈ Set.range D.what₂.embLL →
      (∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[l], GlobalTheory.NormSum.Term.Bd lam ((l : ℝ) ^ B) z) → LossLe w z ((vw w ((l : ℕ) : D.what₂.LL) : ℝ) * B) := by
  intro D w l _ hl z B hz hB
  obtain ⟨y, rfl⟩ := hz
  refine ⟨y, rfl, ?_⟩
  by_cases hy : y = 0
  · exact Or.inl hy
  · right
    have key := GlobalTheory.PadicPlaceBound.neg_mul_vw_le_vw D.what₂.LL D.what₂.embLL y l w B hy hl
      (fun lam => (hB lam).2)
    rw [mul_comm] at key
    exact key
