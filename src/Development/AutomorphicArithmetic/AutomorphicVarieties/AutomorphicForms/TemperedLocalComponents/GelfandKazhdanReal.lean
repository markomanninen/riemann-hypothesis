module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.IsHermOfInner
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.ExistsZalgOfCenterU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.ConjSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.UnitTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.PairOfTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.PairZero

@[expose] public section

open NumberField GlobalTheory.CuspRep UpperTheory.V

open GroundTheory.Automorphic in
private theorem lieMatch : UpperTheory.V.Af.Gk.LieMatch := by
  intro F _ _ _ a
  refine ⟨(Fb.lieEq F a).toLinearMap, Subtype.ext ?_, fun X φ _ =>
    congrArg Subtype.val (UpperTheory.V.Af.CuspFin.uAction_lieEq X φ)⟩
  rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← Fb.lieEq_oneL]
  rfl

theorem UpperTheory.V.Af.gelfandKazhdanReal :
    UpperTheory.V.Published.StrongMultOneReal → UpperTheory.V.Published.GelfandKazhdanReal :=
  Gk.gelfandKazhdan_of Gk.conjSub Gk.satConj Gk.satAE Gk.unitTwist Gk.pairOfTwist Gk.pairZero
    (Gk.hermEx_of (fun _ _ _ _ _ => CuspFin.mem_cuspForms_of) lieMatch)
