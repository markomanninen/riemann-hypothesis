module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsOpenImmersionIsStandardSmoothOfRelativeD
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
public import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem kap_fg_trdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), KapFG Xo c ∧ KapTrdeg Xo c Dw.dim := by
  intro E _ _ _ H Dw l Xo c
  have hs : SmoothOfRelativeDimension Dw.dim (strK (Xo := Xo) (c := c)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  have h := fun Z : Comp Xo c =>
    GlobalTheory.residueField_genericPoint_fg_trdeg_of_smoothOfRelativeDimension c.F (Xo.XF c) strK Dw.dim hs Z.1 Z.2
  exact ⟨fun Z => (h Z).1, fun Z => (h Z).2⟩

end GlobalTheory.Reg
