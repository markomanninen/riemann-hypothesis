module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationWithComponentAtEveryEmbeddin
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
theorem _root_.GlobalTheory.T.exists_uniformisation_with_component_at_every_embedding : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → ∀ j (σ : Q.c.F →+* ℂ), ∃ U : Unf (Q.Xo j) Q.c σ D.R.r, Nonempty U.Comp := by
  first | exact @GlobalTheory.exists_unf_nonempty_comp_all | exact GlobalTheory.exists_unf_nonempty_comp_all | (intros; apply GlobalTheory.exists_unf_nonempty_comp_all <;> assumption)
