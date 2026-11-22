module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateTermsAndCollisionBoundsUniformWidths
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound

@[expose] public section

open GlobalTheory.Core.Deg

theorem GlobalTheory.T.degenerateTerms_and_collisionBounds_uniform_widths :
    (∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ ∀ c : ℝ, On {c} CollS :=
  degenerate_and_collisions_uncond
