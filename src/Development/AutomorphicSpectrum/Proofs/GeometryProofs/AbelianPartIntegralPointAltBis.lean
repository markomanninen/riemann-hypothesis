module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuesOfFrame
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_integral_point_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (lab : CMType H ⊕ CMType H) (m : ℕ) (s : Fin m → 𝔐.Li), 𝔐.IsLinPtOf z P MV A → (𝔐.dR lab).IsFrameAt s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ → ∃ sL : Fin m → V, IsValues 𝔐 z P MV s sL ∧ LinearIndependent L sL ∧ Submodule.span L (Set.range sL) = eigSp A.ρ (A.σ lab) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z P V _ _ _ _ MV A lab m s hLin hfr
  obtain ⟨hact, hlab, -⟩ := hLin
  have hlat := (GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c (𝓞 c.F) (algebraMap _ _) Y S Ω K J y 𝔐
    (FaithfulSMul.algebraMap_injective _ _) ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩
    (fun r hr => FrameVal.not_inFibre _ _ r hr)).2.2
  exact FrameVal.values_core 𝔐 _ P.tK P.m MV A.ρ A.σ A.σ_bij.1 hact hlab hlat lab s hfr
