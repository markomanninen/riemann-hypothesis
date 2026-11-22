module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isProjOver_id (R : Type) [CommRing R] : IsProjOver (𝟙 (Sp R)) := by
  haveI : Unique (Fin (0 + 1)) := ⟨⟨0⟩, fun i => Fin.ext (by have := i.isLt; omega)⟩
  haveI : IsIso (PSpace.str R 0) := by
    haveI : IsIso (GlobalTheory.ProjSpace.chartι R 0 0) := by
      refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
      rw [GlobalTheory.ProjSpace.opensRange_chartι, ← GlobalTheory.ProjSpace.iSup_chart R 0]
      apply le_antisymm (le_iSup _ 0)
      apply iSup_le
      intro i
      rw [Subsingleton.elim i 0]
    haveI : IsEmpty {j : Fin (0 + 1) // j ≠ 0} := ⟨fun j => j.2 (Subsingleton.elim _ _)⟩
    haveI : IsIso (GlobalTheory.ProjSpace.chartι R 0 0 ≫ PSpace.str R 0) := by
      rw [GlobalTheory.ProjSpace.chartι_str]
      exact inferInstanceAs (IsIso (Spec.map
        (MvPolynomial.isEmptyRingEquiv R {j : Fin (0 + 1) // j ≠ 0}).toCommRingCatIso.inv))
    exact IsIso.of_isIso_comp_left (GlobalTheory.ProjSpace.chartι R 0 0) _
  exact ⟨0, inv (PSpace.str R 0), inferInstance, IsIso.inv_hom_id _⟩

end GlobalTheory.Models.Point

end
