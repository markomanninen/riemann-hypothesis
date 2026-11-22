module

public import Formalism.SharpRestriction.LevelLetterCocycles.UpPositionOfModels
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3upPfFilCAnti

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

theorem u3uplink_pf_of (hW : WStep) : UpSlotOfModels := by
  intro D HW F Cm CA CB CK hA hMF
  exact u3upPf_ofR D HW hMF (hW D HW F Cm CA CB CK hA) (ninlam_pf D HW F Cm CA CB CK hA)
    (gamPiCondition D HW F Cm CA CB CK hA)

end Formalism.MainNotions.N.Ln34

end
