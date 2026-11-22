module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOver

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZM

theorem exists_isGaloisCover_of_isQProjOver_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0}) (s : X ⟶ Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K), π ≫ sY = s ∧ IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  intro K _ _ X s Ga _ _ ρ hs h1 hm hρ hfree
  let τ := autOfRightAction ρ h1 hm
  have horbits : GlobalTheory.OrbitsInAffineOpens τ :=
    GlobalTheory.OrbitsInAffineOpens.of_isQProjOver hs τ
  have hτg : ∀ g : Ga, (τ g).asIso.hom = ρ g⁻¹ := fun _ ↦ rfl
  have hτs : ∀ g : Ga, (τ g).asIso.hom ≫ s = s := fun g ↦ hρ g⁻¹
  have hfreeτ : GlobalTheory.IsFreeAction τ := by
    refine GlobalTheory.IsFreeAction.of_isAlgClosed.{0} (fun k _ _ x g hx ↦ ?_)
    exact inv_eq_one.mp (hfree k x g⁻¹ hx)
  obtain ⟨Y, π, hQ⟩ := (GlobalTheory.exists_isAffineQuotient_iff τ).mpr horbits
  let sY := hQ.desc s hτs
  have hπs : π ≫ sY = s := hQ.comp_desc s hτs
  obtain ⟨hsep, hlft, hqc⟩ := isSeparated_finiteType_of_isQProjOver hs
  refine ⟨Y, π, sY, hπs, ?_, ?_, ?_, ?_⟩
  · refine ⟨inferInstance, h1, hm, fun a ↦ ?_,
      hQ.isFinite_of_isFreeAction hfreeτ, hQ.etale_of_isFreeAction hfreeτ, hQ.surjective, ?_⟩
    · have := hQ.comp_eq a⁻¹
      rwa [hτg, inv_inv] at this
    · intro k _ _ y y' hyy
      obtain ⟨g, hg⟩ := (hQ.comp_eq_comp_iff y y').mp hyy
      refine ⟨g⁻¹, hg, fun b hb ↦ ?_⟩
      have key : y ≫ ρ (b * g) = y := by
        rw [hm, ← Category.assoc, hb, ← hg, hτg, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]
      exact eq_inv_of_mul_eq_one_left (hfree k y _ key)
  · haveI : IsSeparated (π ≫ sY) := by
      rw [hπs]; exact hsep
    exact hQ.isSeparated sY
  · haveI : LocallyOfFiniteType (π ≫ sY) := by
      rw [hπs]; exact hlft
    haveI : IsLocallyNoetherian (Sp K) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
    exact hQ.locallyOfFiniteType sY
  · haveI : QuasiCompact (π ≫ sY) := by
      rw [hπs]; exact hqc
    exact hQ.quasiCompact sY

end GlobalTheory.ZM
