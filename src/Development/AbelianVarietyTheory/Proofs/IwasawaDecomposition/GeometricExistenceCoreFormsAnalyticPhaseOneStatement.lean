module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricExistenceCoreFormsAnalyticPhaseOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoExV
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Formalism.LocalRingCardinality.DataKap
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricExistence_core_forms_analytic_phaseOne : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (F : Face D A3.A), VolTieG D → LawsJ C → LawsCore C.toCore → AlgTie C → Finite T0 → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Mem.R3.GeoExV A3 C F := by
  first | exact @GlobalTheory.Mem.R3.GeoExProof.geoExV_of_top | exact GlobalTheory.Mem.R3.GeoExProof.geoExV_of_top | (intros; apply GlobalTheory.Mem.R3.GeoExProof.geoExV_of_top <;> assumption)
