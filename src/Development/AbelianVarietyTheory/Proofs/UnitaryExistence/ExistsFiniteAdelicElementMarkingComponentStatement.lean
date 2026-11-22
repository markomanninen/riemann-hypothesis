module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponent
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelic_element_marking_component : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ k, ∃ h ∈ GfC V, C.Mark h k 1 := by
  first | exact @GlobalTheory.Member.exists_finite_mark | exact GlobalTheory.Member.exists_finite_mark | (intros; apply GlobalTheory.Member.exists_finite_mark <;> assumption)
