module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsNonarchimedeanLocalField
public import GroundTheory.LocalFields.FiniteExtension
public import GroundTheory.LocalFields.UnitsPowers

@[expose] public section

open GlobalTheory.UnitLemma

namespace GlobalTheory.UnitLemma

theorem UQ.finite_units_mod_sq : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [FiniteDimensional K.E L],
    Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  intro K L _ _ _
  letI := GlobalTheory.LocFieldOfDVR.valued K.O K.E
  letI : ValuativeRel K.E := .ofValuation (GlobalTheory.LocFieldOfDVR.val K.O K.E)
  haveI : (GlobalTheory.LocFieldOfDVR.val K.O K.E).Compatible := .ofValuation _
  haveI : IsNonarchimedeanLocalField K.E := by
    have : IsValuativeTopology K.E :=
      IsValuativeTopology.of_mem_nhds_iff_vle (GlobalTheory.LocFieldOfDVR.val K.O K.E)
        (fun {s x} => Valued.mem_nhds)
    have : ValuativeRel.IsNontrivial K.E :=
      (ValuativeRel.isNontrivial_iff_isNontrivial (GlobalTheory.LocFieldOfDVR.val K.O K.E)).mpr inferInstance
    have : LocallyCompactSpace K.E := GlobalTheory.LocFieldOfDVR.locallyCompactSpace
    exact {}
  obtain ⟨vrL, topL, hlocL, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension K.E L
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K.E L).injective
  exact GroundTheory.LocalField.finite_quotient_range_pow_of_charZero (K := L) two_ne_zero

end GlobalTheory.UnitLemma
