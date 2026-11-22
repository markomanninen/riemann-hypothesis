module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.PropEG
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.ToIdeleSq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.IsClosedSmall
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanEqTopOfIrreducibleOverAlgClosed
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeLocal

@[expose] public section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.EG GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.DirichletHecke
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)

private theorem loc_val (η : HeckeCharacter ℚ) (v : Ad3.Pl) (h : IsUnramifiedChar (localChar η v)) :
    ((localChar η v (unifUnit (Ad3.Qv v)) : ℂˣ) : ℂ) = (η (IdeleClassGroup.mk ℚ (IdeleGroup.finiteEmbedding v (uniformizer v))) : ℂ) := by
  have h1 : ord ((uniformizer v : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 1 := by
    rw [Ad3P.DihedralUnramifiedPlaces.ord_eq v (Units.ne_zero _), valued_uniformizer, WithZero.log_exp, neg_neg]
  have hord : ord (((unifUnit (Ad3.Qv v)) * (uniformizer v)⁻¹ : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 0 := by
    rw [ord_units_mul, ord_units_inv, h1, ord_unifUnit]
    norm_num
  have h2 := isUnramifiedChar_iff.1 h _ hord
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [h2, coe_localChar, HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply]
