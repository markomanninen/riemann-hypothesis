module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureSemiAbelianExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationClosureOfGraphStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cubicalStructure_semiAbelianExtension : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE, ∃ P : GlobalTheory.UU.CP Z.G, P.L = Z.L := by
  first | exact @GlobalTheory.ZH.exists_cp_zhOut | exact GlobalTheory.ZH.exists_cp_zhOut | (intros; apply GlobalTheory.ZH.exists_cp_zhOut <;> assumption)
