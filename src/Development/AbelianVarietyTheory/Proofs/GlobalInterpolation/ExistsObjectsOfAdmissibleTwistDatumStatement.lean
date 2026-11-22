module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatum
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsObjects_of_admissibleTwistDatum : ∀ QO : Par → ∀ D : D7, Obj D → Prop, LevelPrime → RecExP QO → ObjCP (fun κ => DC.withObj (ptO (QO κ))) := by
  first | exact @GlobalTheory.Fc.objCP_of_recExP | exact GlobalTheory.Fc.objCP_of_recExP | (intros; apply GlobalTheory.Fc.objCP_of_recExP <;> assumption)
