module

public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV.Align

open Formalism.BasicNotions Formalism.MainNotions

structure PrinLev {D : D7} (V : DivX D) where

  κg : V.Lev

  κs : V.Lev
  κg_pr : V.levPr κg = {D.host.g 0, D.host.g 1}
  κs_pr : V.levPr κs = {D.host.g 0, D.host.g 1, 3, 5}

def LevB {D : D7} {V : DivX D} (P : PrinLev V) (κ : V.Lev) : Prop := κ = P.κg ∨ κ = P.κs

abbrev PrinLevF {eps : ℝ} (Fm : FamP eps) : Type :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), PrinLev (Fm.X x i)

end Formalism.MainNotions.DIV.Align

end
