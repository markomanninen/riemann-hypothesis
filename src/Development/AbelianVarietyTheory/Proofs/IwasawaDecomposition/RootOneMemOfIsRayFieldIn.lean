module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdHstar

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.RayRoots

theorem rootOne_mem_of_isRayFieldIn : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (φ : E →+* ℂ)
    (N n : ℕ) (M : IntermediateField ℚ ℂ), N ≠ 0 → n ∣ N → IsRayFieldIn φ (natIdeal E N) M → rootOne n ∈ M :=
  fun _ _ _ _ φ _ _ _ hN hn hM => GlobalTheory.Mem.FieldsEx.rootOne_mem_ray φ hN hn hM

end GlobalTheory.Mem.RayRoots
