module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelStatementsOfJoint
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_zero_level_statements_of_joint : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Joint0 g.herm.lev0 u (g.forms u) → OneHyp ((g.forms u).cls0).toChart.lev (lev0At g u w hg).A ((g.forms u).cls0).toChart.y := by
  first | exact @GlobalTheory.Port.oneHyp_lev0At | exact GlobalTheory.Port.oneHyp_lev0At | (intros; apply GlobalTheory.Port.oneHyp_lev0At <;> assumption)
