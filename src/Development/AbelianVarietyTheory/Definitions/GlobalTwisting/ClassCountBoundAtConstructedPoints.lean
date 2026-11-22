module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Formalism.LocalRingCardinality.DataTies

@[expose] public section

noncomputable section

namespace GlobalTheory.Fc.R0

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top GlobalTheory.Fc

def ClassCountBoundAllPoints (𝒜 : FamClass) : Prop :=
  Closed (W1 𝒜) fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev

def ClassCountBoundAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => ClassCountBoundAllPoints 𝒜

def H_jOn (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    ((Fm.D x i).what₂.V0 (Fm.D x i).what₂.mu0).map ((Fm.D x i).what₂.iota (Fm.D x i).what₂.mu0) = ⊤

def JInvariantConditionAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_jOn 𝒜

def H_la (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La

def LambdaConditionAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_la 𝒜

end GlobalTheory.Fc.R0

end
