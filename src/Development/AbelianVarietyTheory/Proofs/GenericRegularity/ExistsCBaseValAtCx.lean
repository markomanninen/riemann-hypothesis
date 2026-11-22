module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
public import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
public import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
public import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReduced

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem GlobalTheory.Reg.exists_cBase_valAtCx :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∃ yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)), (∀ Z, CBase h Z (yP Z)) ∧ ValAtCx h yP ∧ GenFromTest Xo c h := by
  intro E _ _ _ H Dw l Xo c hL h
  have hex : ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ), ∃ z : FrPt Xo c (CAt (sgOf P)), FrMap (PAlg P) (genFr h Z) z :=
    fun Z P => hL.bc _ _ (PAlg P) (genFr h Z)
  choose yP hyP using hex
  refine ⟨yP, fun Z P => hyP Z P, fun Z P a n f hf => ?_, fun Z => hL.test _ _⟩
  have e := GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n f hf (Om Z) (CAt (sgOf P)) (PAlg P)
    (genFr h Z) (yP Z P) (hyP Z P)
  rw [e]
  rfl
