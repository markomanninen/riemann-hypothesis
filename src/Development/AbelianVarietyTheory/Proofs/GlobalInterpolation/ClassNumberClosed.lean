module

public import Mathlib
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll

@[expose] public section

namespace GlobalTheory.ColClassNumber

open Formalism.MainNotions

theorem classNumber_closed (𝒞 : FamClass) :
    Closed 𝒞 fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm _ _ _ x hx i => classNumber_all (Fm.D x i) (Fm.ex x hx i).lev⟩⟩

end GlobalTheory.ColClassNumber
