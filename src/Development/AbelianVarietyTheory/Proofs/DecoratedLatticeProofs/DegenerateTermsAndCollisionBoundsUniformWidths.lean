module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowAmplitudeBoundsUniformSingletonWidthStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTermLoopOfStandingHypotheses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsPosTypeP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallOnUnivUnconditional
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InputsOfSubsetWidths
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollSOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankTwoCountBoundsOfRowCountBoundsUniform
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CntOnSingleton
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VanishingGramBoundUniformWindowAndParams
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VanishingGramBoundWindowOfTermPairTypeBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem degenerate_and_collisions_uncond : (∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ ∀ c : ℝ, On {c} CollS := by
  have hSM : Formalism.HermitianLatticesTheory.SiegelMassRatio := GlobalTheory.Mass.siegelMassRatio_holds
  have hS : ∀ c : ℝ, SmallOn {c} := fun c =>
    (inputs_of_subset_widths {c} Set.univ (Set.subset_univ _)).2.1 smallOn_univ_unconditional
  have hP : GlobalTheory.TypeAsm.TypeP := GlobalTheory.rowsPos_typeP
  refine ⟨vanishingGramBound_uniformWindow_and_weightData.1 (vanishingGramBoundWindow_of_termPairTypeBound hP), fun c => ?_⟩
  exact collS_on hSM {c} (GlobalTheory.T.rowAmplitudeBoundsUniform_singleton_width c) (corankTwoCountBounds_of_rowCountBoundsUniform {c} (cntOn_singleton hSM c)) (hS c)
    (tieOn_singleton_uncond c)

end GlobalTheory.Core.Deg
