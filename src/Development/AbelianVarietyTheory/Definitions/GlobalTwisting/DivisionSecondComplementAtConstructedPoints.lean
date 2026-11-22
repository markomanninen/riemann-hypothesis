module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top

namespace GlobalTheory.Fc.ClassTwoEntries

open GlobalTheory.Fc

def H_hInstR (𝒜 : FamClass) : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → ∀ (x : ℝ) (_ : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep (Fm.D x i) ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) ((Fm.D x i).sp.Y 0).rank

def InstanceRankAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_hInstR 𝒜

def DivisionSecondComplementAdmissible (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm

def DivisionSecondComplementAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => DivisionSecondComplementAdmissible 𝒜

end GlobalTheory.Fc.ClassTwoEntries

end
