module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealisedChainTorusEq
public import Formalism.SharpRestriction.FamCore
public import Formalism.LocalRingCardinality.SpanPowerMembership
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowF
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
public import Formalism.LocalRingCardinality.SpanPowerMembership.GPlacesExampleNatAct
public import Formalism.CyclotomicNorms.StatementT
public import Formalism.LocalRingCardinality.SpanPowerMembership.EntPlNonempty
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.LocalRingCardinality.DataTies
public import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
public import Formalism.SharpRestriction.InertJacobiLevels.ExtraTheta
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Formalism.LocalRingCardinality.DataKerP
public import Formalism.LocalRingCardinality.DataLatDefs
public import Formalism.LocalRingCardinality.SpanPowerMembership.ClassRecordRowDimensionZero
public import Formalism.SharpRestriction.InertJacobiLevels.ExtraVal
public import Formalism.LocalRingCardinality.DataNChTie
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsHomOfBasis
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.PrincipalHermitianLattice
public import Formalism.LocalRingCardinality.DataDIVDefs
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos
public import Formalism.LocalRingCardinality.DataNChoice
public import Formalism.SharpRestriction.InertJacobiLevels.ExtraNum
public import Formalism.SharpRestriction.InertJacobiLevels.ExtraGat
public import Formalism.LocalRingCardinality.DataMink
public import Formalism.LocalRingCardinality.DataIdx
public import Formalism.LocalRingCardinality.SpanPowerMembership.DivXExample
public import Formalism.LocalRingCardinality.DataAmbForm
public import Formalism.LocalRingCardinality.DataKap
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataForms
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowC
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevD
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat
public import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices
public import Formalism.SharpRestriction.GrowthBounds.DataGChain
public import Formalism.LocalRingCardinality.SpanPowerMembership.GatSetting
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.DeterminantTwistRowActionMem
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.JOInjective
public import Formalism.SharpRestriction.InertJacobiLevels.ExtraGatC
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdOfEqMulIntegral

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.RkFamModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ GlobalTheory.Core.Rk NumberField Module

theorem xu_pos (D : D7) (u : D.what₂.Word) : 0 < (D.mem u).A.Xu := by
  have h1 := (D.mem u).A.Dstar_pos
  have h2 : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  unfold ColumnsAtT.Xu
  positivity

theorem fk_pos (R : Ranks) : (0 : ℝ) < (R.f : ℝ) * R.k := by
  have := R.m_add_three_le_k
  have h1 : 0 < R.k := by omega
  have h2 : 0 < R.f := Nat.mul_pos two_pos R.ord_pos
  positivity

theorem log_tstar (D : D7) (u : D.what₂.Word) : Real.log (D.mem u).A.Tstar =
    Real.log (D.mem u).A.Xu - 2 / ((D.R.f : ℝ) * D.R.k) * Real.log (D.mem u).A.GamP := by
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  unfold ColumnsAtT.Tstar
  rw [Real.log_mul (xu_pos D u).ne' (Real.rpow_pos_of_pos hG _).ne', Real.log_rpow hG]
  ring

theorem log_T_lt (D : D7) (u : D.what₂.Word) :
    Real.log ((D.mem u).A.T : ℝ) < Real.log (D.mem u).A.Xu + 1 / ((D.R.f : ℝ) * D.R.k) := by
  have hT : (0 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hf := fk_pos D.R
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hs : 0 < (D.mem u).A.Tstar := mul_pos (xu_pos D u) (Real.rpow_pos_of_pos hG _)
  have h1 := Real.log_le_log hT (D.T_win u).2
  rw [Real.log_mul (by positivity) hs.ne', log_tstar] at h1
  have h2 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((D.R.f : ℝ) * D.R.k))
  have h3 : 0 < 2 / ((D.R.f : ℝ) * D.R.k) * Real.log (D.mem u).A.GamP :=
    mul_pos (by positivity) (Real.log_pos (D.mem u).A.one_lt_gammaP)
  linarith


section Rank

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (N : ℕ)

variable (T : ℕ) [Fact T.Prime] (Dst : ℝ) (hD : 0 < Dst) (hT : T ≠ 2) (s : ℂ)


end Rank

end GlobalTheory.Core.RkFamModel

namespace GlobalTheory.Core.RkOverModel

open Formalism.BasicNotions GlobalTheory.Core.Rk

end GlobalTheory.Core.RkOverModel

end
