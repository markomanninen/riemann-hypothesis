module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.FourParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagClassConstancy.FlagOfInSFRight

@[expose] public section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem in_s_class_constant (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermInSFun D u u' :=
  fun _ Λ _ => PI.InSClassConstW.inSFun_all Λ _ _
