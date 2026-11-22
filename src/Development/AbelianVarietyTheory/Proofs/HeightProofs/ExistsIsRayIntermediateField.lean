module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRichSmall
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulFinrankMemDifferentIdeal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeckeIdealEqOfRay
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LogRootDiscrLeOfNatCastMemDifferentIdeal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberSetSubsetRayField
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.SmallField

theorem exists_isRay_intermediateField (hR : GlobalTheory.NT.RayField) (K : IntermediateField ℚ ℂ) [NumberField K]
    (𝔮 : Ideal (𝓞 K)) (h𝔮 : 𝔮 ≠ ⊥) :
    ∃ (R : IntermediateField K ℂ) (_ : NumberField R) (_ : IsAbelianGalois K R), IsRay R 𝔮 := by
  obtain ⟨M, _, _, _, hM⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hR K 𝔮 h𝔮
  have := hM.1
  let f : M →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : M ≃ₐ[K] f.fieldRange := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional K f.fieldRange := e.toLinearEquiv.finiteDimensional
  have : NumberField f.fieldRange := NumberField.of_module_finite K f.fieldRange
  have h := hM.of_algEquiv e
  exact ⟨f.fieldRange, inferInstance, h.1, h.2⟩

end GlobalTheory.FieldSize.SmallField

namespace GlobalTheory.FieldSize

open SmallField GlobalTheory.Mem.BaseExt

end GlobalTheory.FieldSize
