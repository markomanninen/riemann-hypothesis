module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPicardGroup
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveAppTopOfSection

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.IsoDescent

theorem exists_gen_pull_div_iff {X Y : Scheme.{0}} (f : Y ⟶ X) {N N' : LB X} (hN : N.IsLB) (hN' : N'.IsLB) :
    (∃ t : LB.Gen ((LB.div N N').pull f), t.IsGen) ↔ LBIso (N.pull f) (N'.pull f) := by
  obtain ⟨Pic, groups, cl, pl, iso_iff, gen_iff, -, -, linComb, div⟩ :=
    CechPicMul.exists_picardGroup
  let _ := groups
  have pull_class {L : LB X} (hL : L.IsLB) :
      (L.pull f).IsLB ∧ cl (L.pull f) = pl f (cl L) := by
    simpa only [Fintype.prod_unique, zpow_one] using
      linComb X Y L hL PUnit (fun _ => f) (fun _ => 1)
  obtain ⟨hD, eD⟩ := div X N' N hN' hN
  obtain ⟨hDf, eDf⟩ := pull_class hD
  obtain ⟨hNf, eNf⟩ := pull_class hN
  obtain ⟨hN'f, eN'f⟩ := pull_class hN'
  rw [← gen_iff Y _ hDf, eDf, eD, map_div, div_eq_one, ← eNf, ← eN'f,
    iso_iff Y _ _ hNf hN'f]

theorem lbIso_of_field : ∀ (R k : Type) [CommRing R] [IsDedekindDomain R] [Field k] (β : R →+* k), Function.Injective β → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp k), IsPullback π p A.hom (spMap β) → ∀ N N' : LB A.left, N.IsLB → N'.IsLB → LBIso (N.pull (eSec A)) (N'.pull (eSec A)) → LBIso (N.pull π) (N'.pull π) → LBIso N N' := by
  intro R k _ _ _ β hβ A _ hA X' π p H N N' hN hN' he hπ
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  let K := FractionRing R
  let δ : K →+* k := IsFractionRing.lift hβ
  have hδ : spMap δ ≫ spMap (algebraMap R K) = spMap β := by
    have e : δ.comp (algebraMap R K) = β := RingHom.ext fun x => IsFractionRing.lift_algebraMap hβ x
    rw [← e]
    exact (Spec.map_comp _ _).symm
  have H₀ := IsPullback.of_hasPullback A.hom (spMap (algebraMap R K))
  set π₀ := pullback.fst A.hom (spMap (algebraMap R K))
  set p₀ := pullback.snd A.hom (spMap (algebraMap R K))
  let q := H₀.lift π (p ≫ spMap δ) (by rw [Category.assoc, hδ, H.w])
  have hq : q ≫ π₀ = π := H₀.lift_fst _ _ _
  have H₁ : IsPullback q p p₀ (spMap δ) := by
    refine IsPullback.of_right ?_ (H₀.lift_snd _ _ _) H₀
    rw [hq, hδ]
    exact H
  obtain ⟨Pic, groups, cl, pl, iso_iff, gen_iff, -, comp, linComb, div⟩ :=
    CechPicMul.exists_picardGroup
  let _ := groups
  have pull_class {S T : Scheme.{0}} (f : T ⟶ S) {L : LB S} (hL : L.IsLB) :
      (L.pull f).IsLB ∧ cl (L.pull f) = pl f (cl L) := by
    simpa only [Fintype.prod_unique, zpow_one] using
      linComb S T L hL PUnit (fun _ => f) (fun _ => 1)
  obtain ⟨hD, eD⟩ := div A.left N' N hN' hN
  obtain ⟨hD₀, eD₀⟩ := pull_class π₀ hD
  have h₁ : ∃ t : LB.Gen (((LB.div N N').pull π₀).pull q), t.IsGen := by
    obtain ⟨hDq, eDq⟩ := pull_class q hD₀
    obtain ⟨hDπ, eDπ⟩ := pull_class π hD
    rw [← gen_iff X' _ hDq, eDq, eD₀, ← comp, hq, ← eDπ, gen_iff X' _ hDπ]
    exact (exists_gen_pull_div_iff π hN hN').2 hπ
  obtain ⟨t, ht⟩ := h₁
  have h₂ := FieldTriv.exists_gen_of_isPullback δ p₀ q p H₁ hD₀ t ht
  have h₃ := TrivDedekind.exists_gen_of_generic R K A hA _ π₀ p₀ H₀ _ hD
    ((exists_gen_pull_div_iff _ hN hN').2 he) h₂
  rwa [← gen_iff A.left _ hD, eD, div_eq_one, iso_iff A.left _ _ hN hN'] at h₃

end GlobalTheory.IsoDescent
