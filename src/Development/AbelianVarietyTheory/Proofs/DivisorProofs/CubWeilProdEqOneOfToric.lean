module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws3
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfPowEqOneOfLocalHom
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Raynaud.ProdToric

theorem isMonHom_lift_id_one {S : Scheme.{0}} (G G' : Over S) [GrpObj G] [GrpObj G'] :
    IsMonHom (lift (𝟙 G) (1 : G ⟶ G')) := by
  rw [Hom.one_def]; infer_instance

theorem isMonHom_lift_one_id {S : Scheme.{0}} (G G' : Over S) [GrpObj G] [GrpObj G'] :
    IsMonHom (lift (1 : G' ⟶ G) (𝟙 G')) := by
  rw [Hom.one_def]; infer_instance

end GlobalTheory.Raynaud.ProdToric
