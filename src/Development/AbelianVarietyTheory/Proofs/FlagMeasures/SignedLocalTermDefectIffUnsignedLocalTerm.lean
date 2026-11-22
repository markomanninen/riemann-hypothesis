module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOrbitsHeightsAmplitudesInCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFramesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnsignedLocalTermRowLatticeIsTerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometries
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsGenericTermIffNoLocalDefectBaseFrames

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SignDefect

theorem locBBne_iff_locU : ∀ {D : D7} (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Tn T'n : ℕ), locBBne Z p Λ F F' Tn T'n ↔ LocNG.BBne (H := locH Z p) (locU Z p Λ F F' Tn T'n) := by
  intro D Z p Λ T T' F F' Tn T'n
  exact (GlobalTheory.Unfold.GenLoc.locBBne_iff Z p Λ F F' Tn T'n).symm

end GlobalTheory.SignDefect
