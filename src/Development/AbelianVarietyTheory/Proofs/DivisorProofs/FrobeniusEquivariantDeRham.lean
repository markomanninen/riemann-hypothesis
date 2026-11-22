module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbDatum

open GlobalTheory.ConjSeq

theorem frobDR_primPull (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)
    {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (c : primDR B) :
    frobDR p R hR A (primPull (dp0 R) (𝟙 _) f c) = primPull (dp0 R) (𝟙 _) f (frobDR p R hR B c) := by
  have k := (frobMor p R hR B (cast_left p R hR B)).comp (homMor (dp0 R) (𝟙 _) f)
  exact (GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) f) (frobMor p R hR A (cast_left p R hR A)) k (fun _ ↦ rfl)
    (GlobalTheory.VB.frob_naturality p _ f.left _) c).trans
    (GrpMor.pull_pull (frobMor p R hR B (cast_left p R hR B)) (homMor (dp0 R) (𝟙 _) f) k (fun _ ↦ rfl) rfl c).symm

end GlobalTheory.AbDatum
