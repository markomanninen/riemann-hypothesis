module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
public import Formalism.LocalToGlobal.ProjectiveLattices.ReadLeaves
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_mul_archimedean_mem_nhds : ∀ (D : D7) (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)), 0 < N → IsLevelK V N Kf → ∀ g₀ : GA D V, {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀ := by
  first | exact @GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds | exact GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds | (intros; apply GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds <;> assumption)
