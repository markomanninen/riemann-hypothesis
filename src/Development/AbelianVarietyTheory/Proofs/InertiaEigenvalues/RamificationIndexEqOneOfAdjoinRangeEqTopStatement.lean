module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationIndexEqOneOfAdjoinRangeEqTop
public import GroundTheory.LocalFields.UnramifiedNormSurj
public import GroundTheory.LocalFields.UnramifiedGalois

@[expose] public section

open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationIndex_eq_one_of_adjoin_range_eq_top_alt : ∀ (F E K L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F E] [Algebra F K] [Algebra F L] [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L] [ValuativeExtension F E] [ValuativeExtension F K] [ValuativeExtension K L] [FiniteDimensional F E] [FiniteDimensional K L], (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = 1 → Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ → (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 := by
  first | exact @GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top | exact GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top | (intros; apply GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top <;> assumption)
