module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominating
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialDataStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Arith

theorem idlAlong_monomial : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (φ : InvFun ℤ)
    (J : Z.IdealSheafData) (d : ℕ), ValOn F i φ J d →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ) (ga δ : Fin m → LinearMap.BilinForm ℤ X)
      (M : ℕ), IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ b : Fin m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ (δ k)) →
    ∀ (T : Trait F) (W : Type) [CommRing W] [IsLocalRing W] (σ : W →+* T.V) (c : Fin m → ℕ) (e' : T.D.toPre.X ≃+ X)
      (x : Sp W ⟶ Z) (s : Fin m → W), Function.Bijective σ → jK T.V ≫ spMap σ ≫ x = T.y ≫ i →
      (∀ k, Associated (σ (s k)) (T.ϖ ^ c k)) → (∀ a b, T.β a b = ∑ k, (c k : ℤ) * δ k (e' a) (e' b)) →
      idlAlong J x = Ideal.span {∏ k, s k ^ b k} := by
  intro o _ ζ g n F Z i φ J d hV X _ _ _ m ga δ M hcone hδ b hb T W _ _ σ c e' x s hσ hcomm hs hβ
  obtain ⟨a, ha, hid⟩ := hV T (spMap σ ≫ x) hcomm
  have heq (χ : Sp W ⟶ Z) (U : Z.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
      idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of W)).hom).hom := by
    have hx : χ (closedPoint W) ∈ U.1 := hle trivial
    unfold idlAlong
    rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  have hcomp : idlAlong J (spMap σ ≫ x) = (idlAlong J x).map σ := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens
      (show x (closedPoint W) ∈ (⊤ : Z.Opens) from trivial)
    have hle : ⊤ ≤ x ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem x hx).ge
    have hle' : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := fun y _ => hle (show spMap σ y ∈ (⊤ : (Sp W).Opens) from trivial)
    have heq' : idlAlong J (spMap σ ≫ x) = (J.ideal ⟨U, hU⟩).map
        ((spMap σ ≫ x).appLE U ⊤ hle' ≫ (Scheme.ΓSpecIso (.of T.V)).hom).hom := by
      have hx' : (spMap σ ≫ x) (closedPoint T.V) ∈ U := hle' trivial
      unfold idlAlong
      rw [ds_stalkId_eq_map J ⟨U, hU⟩ _ hx', Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
      congr 2
    rw [heq x ⟨U, hU⟩ hle, heq', Ideal.map_map]
    congr 1
    have e : (spMap σ ≫ x).appLE U ⊤ hle' = x.appLE U ⊤ hle ≫ (spMap σ).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  rw [hcomp] at hid
  have hlin : φ.LinearOn δ := by
    have := hcone.linearOn_smul M
    rwa [show δ = fun k => (M : ℤ) • ga k from funext hδ]
  have hev : φ.evalZ T.β = ∑ k, (c k : ℝ) * φ.evalZ (δ k) := by
    refine InvFun.LinearOn.eval_eq_sum (X := X) hlin (r := e'.symm.toIntLinearEquiv.toLinearMap)
      e'.symm.surjective (fun k => Nat.cast_nonneg _) ?_
    intro u v
    simp [hβ]
  have haN : a = ∑ k, c k * b k := by
    have : (a : ℝ) = ∑ k, (c k : ℝ) * b k := by
      rw [ha, hev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb k]; ring
    exact_mod_cast this
  have hassoc : Associated (∏ k, σ (s k) ^ b k) (T.ϖ ^ a) := by
    rw [haN, ← Finset.prod_pow_eq_pow_sum]
    refine Associated.prod _ _ _ fun k _ => ?_
    rw [pow_mul]
    exact (hs k).pow_pow
  have hmap : (idlAlong J x).map σ = (Ideal.span {∏ k, s k ^ b k}).map σ := by
    rw [hid, Ideal.map_span, Set.image_singleton, map_prod]
    simp only [map_pow]
    exact (Ideal.span_singleton_eq_span_singleton.2 hassoc).symm
  rw [← Ideal.comap_map_of_bijective σ hσ (I := idlAlong J x), hmap, Ideal.comap_map_of_bijective σ hσ]

end GlobalTheory.Poinc.Arith
