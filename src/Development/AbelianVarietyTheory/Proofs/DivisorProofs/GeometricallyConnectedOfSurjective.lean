module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyConnectedOfAlgClosedInFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

set_option autoImplicit false

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.GeomConnConst

theorem algX_top_strHom (K : Type) [Field K] (C : Scheme.{0}) [Algebra K Γ(C, ⊤)] (c : K) :
    algX (strHom K C) ⊤ c = algebraMap K Γ(C, ⊤) c := by
  rw [algebraMap_eq_strHom K C c]
  simp [algX, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]

end GlobalTheory.GeomConnConst
