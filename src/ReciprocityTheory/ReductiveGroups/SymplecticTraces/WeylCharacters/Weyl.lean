module

public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SqChar
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.UCharOf
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SpBlkSurj
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.BlockP

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

theorem weyl : WeylStatement :=
  weyl_of (kCharGT_of (uChar_of sqChar)) blockComb

end ReciprocityTheory.ChartRestriction.TR.Weyl
