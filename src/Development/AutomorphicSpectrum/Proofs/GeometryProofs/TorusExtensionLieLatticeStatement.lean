module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionLieLattice
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_lie_lattice : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (G G' : Over (Sp O)) [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (τ : TorusExtension GK) (φ : GK.left ⟶ G.left) (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap O K)) φ → IsGrpPullback τ.B G' (spMap (algebraMap O K)) φ' → ∀ (MT : LieModel (splitTorus (Sp K) τ.X) (𝟙 _) (τ.X →+ K)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module O E] (E' : Type) [AddCommGroup E'] [Module O E'] (M : LieModel G (𝟙 _) E) (M' : LieModel G' (𝟙 _) E'), ∃ (io : (τ.X →+ O) →ₗ[O] E) (f : E →ₗ[O] E'), (∀ δ, ((MT.pt ((algebraMap O K).toAddMonoidHom.comp δ) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt (io δ)).left)) ∧ (∀ (e : E) (v : epsAt (𝟙 (Sp K)) ⟶ GK), (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt e).left) → ((v ≫ τ.q).left ≫ φ' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M'.pt (f e)).left)) ∧ Function.Injective io ∧ LinearMap.ker f = LinearMap.range io ∧ ∀ e' : E', ∃ (a : O) (e : E), a ≠ 0 ∧ f e = a • e' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ToricQuot.lie_quot_full | exact GlobalTheory.CompanionTheory.Ar.ToricQuot.lie_quot_full | (intros; apply GlobalTheory.CompanionTheory.Ar.ToricQuot.lie_quot_full <;> assumption)
