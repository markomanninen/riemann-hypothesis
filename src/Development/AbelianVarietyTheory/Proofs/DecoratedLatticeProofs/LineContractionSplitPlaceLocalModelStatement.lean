module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineContraction_splitPlace_localModel : ∀ (D : D7), GlobalTheory.LocFlat.ContrFactor → ContrLoc D := by
  first | exact @GlobalTheory.ContrLocProof.contrLoc | exact GlobalTheory.ContrLocProof.contrLoc | (intros; apply GlobalTheory.ContrLocProof.contrLoc <;> assumption)
