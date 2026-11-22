module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSubextensionCls
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

namespace GlobalTheory.TorusPart

theorem isCommMonObj_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {G' : Over S'} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : IsCommMonObj G' := by
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  refine ⟨?_⟩
  rw [← cancel_mono e.hom, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]

end GlobalTheory.TorusPart
