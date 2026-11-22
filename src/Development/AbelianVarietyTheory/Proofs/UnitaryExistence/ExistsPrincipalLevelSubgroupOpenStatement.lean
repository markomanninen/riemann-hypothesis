module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
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
theorem _root_.GlobalTheory.T.exists_principalLevel_subgroup_open : ∀ (D : D7) (V : HSp D), ∀ N : ℕ, (∃ Kf : Subgroup (GA D V), IsLevelK V N Kf) ∧ (0 < N → {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V)) := by
  first | exact @GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds | exact GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds | (intros; apply GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds <;> assumption)
