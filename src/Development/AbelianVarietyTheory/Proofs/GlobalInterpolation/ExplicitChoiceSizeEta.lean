module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowAndImp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaBounds
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaLeW
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RbSNumeric

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeEta : SzRow (fun _ _ L => SizeEta L) := by
  refine SzRow.imp (SzRow.and szRow_eta_bounds (SzRow.and szRow_eta_le_w szRow_rbS)) ?_
  rintro C cD ch D L - - ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, h10⟩
  exact ⟨h3, h1, h2, h4, h5, h6, h7, h8, h10⟩

end GlobalTheory.EX
