module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ColViewOfBuilt

@[expose] public section

noncomputable section

namespace GlobalTheory.Fc.Cv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem overCols_goodE : ∀ (𝒮 : Slots) (R : V4.Slot), OverCols (IsGoodE 𝒮) ∧ OverCols (sAnd (IsGoodE 𝒮) R) := by
  intro 𝒮 R
  have h : OverCols (IsGoodE 𝒮) :=
    (overCols_built 𝒮).2 (GoodE 𝒮) fun _ _ _ _ _ _ _ g => ⟨g.1.choose⟩
  exact ⟨h, OverCols.and_left h⟩

end GlobalTheory.Fc.Cv

end
