module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ggeo.FracLocal

theorem isFractionRing_gat : ∀ {D : D7} (Gl : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf :=
  fun {_} Gl u w hg => GlobalTheory.TwV.Lt.fracAt Gl u w hg

end GlobalTheory.Ggeo.FracLocal
