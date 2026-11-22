module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem GlobalTheory.Exist.comp_nonempty_finite_genFr_trdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → Nonempty (Comp Xo c) ∧ Finite (Comp Xo c) ∧ ∃ h : GenFrEx Xo c, GenFromTest Xo c h ∧ (∀ Z, evC h Z 1 = 1) ∧ ∀ Z : Comp Xo c, Algebra.trdeg c.F (kap Z) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c h1
  have hB : Out.SecBaseChangeSt := GlobalTheory.allSixLaws.1.secBaseChange
  have hT : Out.SecTwistSt := GlobalTheory.allSixLaws.2.1.secTwist
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  have h : GenFrEx Xo c := genFrEx_of hT
  have hg : GenFromTest Xo c h := fun Z => hA _ _
  obtain ⟨x⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H Dw).2.2 GlobalTheory.closing_of_abelianSchemeLaws h1 l Xo c
  exact ⟨⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩⟩,
    CompFin.finite_comp Xo c, h, hg, fun Z => evalAt_one _ _ _ (hg Z),
    (GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).2⟩
