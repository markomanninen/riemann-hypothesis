module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix

namespace GlobalTheory.Et.Rel

structure RActPre (X : Scheme.{0}) (Γ : Type) [Group Γ] where

  P : (Over X)ᵒᵖ ⥤ Type

  act : Γ → (P ⟶ P)
  act_one : act 1 = 𝟙 P
  act_mul : ∀ g h, act (g * h) = act g ≫ act h

variable {X : Scheme.{0}} (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

section
variable {E} (Q : RActPre X Γ) (ξ : Γ →* GL ι E)

end

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

end GlobalTheory.Et.Rel
