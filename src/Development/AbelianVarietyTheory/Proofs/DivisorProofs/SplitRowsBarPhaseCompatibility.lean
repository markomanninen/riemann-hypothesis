module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.BigOn

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem conjugateReadingsVanishing_splitPart : BarTie (fw2 p) := p.bar


set_option maxHeartbeats 2000000 in
theorem thetaRowData_pins_splitPart (i : Fin D.R.m) : OMPins p.T (R2 p) p.κ p.v₀ (om2 p) i :=
  ⟨(p.pins i).1, { (p.pins i).2 with lift := { (p.pins i).2.lift with }, tuple := fun t => { (p.pins i).2.tuple t with } }⟩

theorem phaseCompatible_splitPart_of_liftUniformisation (hU : p.R.toRealDat.LUnif) (i : Fin D.R.m) :
    PhaseTie p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i := by
  have h := p.phase i hU
  have he : phEff p.R = fun _ => 1 := funext fun j => p.phEff_one j
  rw [he] at h
  exact h

end

end GlobalTheory.BigOn

end
