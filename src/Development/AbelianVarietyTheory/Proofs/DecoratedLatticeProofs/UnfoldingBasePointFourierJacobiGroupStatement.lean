module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_base_point_fourierJacobi_group : ∀ (D : D7) (W W₀ : HSp D) (ρ : ℕ) (d : HypDec W W₀ ρ), IsBase W d.e ∧ gramQ W d.e = 0 ∧ xZero d = rat d.e ∧ Rgrp W (rat d.e) = jacGrp d ∧ Continuous d.emb0 ∧ ∀ n ∈ flagN d, ∀ h, n * d.emb0 h ∈ GQ W ↔ n ∈ GQ W ∧ h ∈ GQ W₀ := by
  first | exact @GlobalTheory.Unf.base_point | exact GlobalTheory.Unf.base_point | (intros; apply GlobalTheory.Unf.base_point <;> assumption)
