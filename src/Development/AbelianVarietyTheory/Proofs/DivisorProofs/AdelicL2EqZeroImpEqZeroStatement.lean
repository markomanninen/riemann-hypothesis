module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicL2EqZeroImpEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrArchPairAdeleJoin

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_l2_eq_zero_imp_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ D ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.l2A F μ D = 0 → D = 0 := by
  first | exact @GlobalTheory.WeilL2Words.eq_zero_of_l2A_eq_zero | exact GlobalTheory.WeilL2Words.eq_zero_of_l2A_eq_zero | (intros; apply GlobalTheory.WeilL2Words.eq_zero_of_l2A_eq_zero <;> assumption)
