module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyFlatBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeBijectiveLinearEquivSquareUnivStatement

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

open KaehlerDifferential DividedPowers GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm

namespace GlobalTheory.SmoothLift

private theorem crystallineSmoothLift_natural_local :
    ∃ e₁ : ∀ D : Data, CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s,
      ∀ (D D' : Data) (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (h : φ ≫ D.s = D'.s ≫ spMap σ)
        (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c,
        IsPull1 h (e₁ D c) (e₁ D' (m.pull1 c)) := by
  let Λ : ∀ D : Data, Lift D := fun D ↦ Classical.choice (GlobalTheory.T.nonempty_smoothLiftAffineThickenings D)
  obtain ⟨hr1, -⟩ := GlobalTheory.T.crystallineCechDeRham_relations_total_detect_zero
  have E1 : ∀ D : Data, ∃ e : CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s, ∀ c h, e c = h ↔ (Λ D).Rel1 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr1 D (Λ D)).1 (hr1 D (Λ D)).2.1 (hr1 D (Λ D)).2.2
      (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).1 (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.1
  choose e₁ he₁ using E1
  refine ⟨e₁, ?_⟩
  intro D D' σ φ φ₀ h m hc c
  exact GlobalTheory.T.crystallineDeRhamRelation_natural_smoothLift_morphism.1 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _
    ((he₁ D c _).1 rfl) ((he₁ D' _ _).1 rfl)

end GlobalTheory.SmoothLift

namespace GlobalTheory.CrysFlatBC

open GlobalTheory.SmoothLift

theorem bijective_liftSemi_pull1 : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] [Module.Flat R D] (π : D →+* R) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : R, π (algebraMap R D a) = a) → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (t : X ⟶ Sp D) (φ : X ⟶ X), Smooth s → IsSeparated s → QuasiCompact s → t = s ≫ spMap π → φ = 𝟙 X → ∀ m : IsMor (dp0 R) s κ t (algebraMap R D) φ, Function.Bijective (liftSemi m.pull1) := by
  intro R D _ _ _ _ π κ hκ hπ X s t φ hs hs' hs'' ht hφ m
  subst hφ ht
  obtain ⟨e₁, n⟩ := GlobalTheory.SmoothLift.crystallineSmoothLift_natural_local
  have hb : spMap π ≫ spMap (algebraMap R D) = 𝟙 _ := by
    rw [← Cris.spMap_comp, show π.comp (algebraMap R D) = RingHom.id R from RingHom.ext hπ, Cris.spMap_id]
  obtain ⟨X', q, s', H⟩ : ∃ (X' : Scheme.{0}) (q : X' ⟶ X) (s' : X' ⟶ Sp D),
      IsPullback q s' s (spMap (algebraMap R D)) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  let i : X ⟶ X' := H.lift (𝟙 X) (s ≫ spMap π) (by rw [Category.assoc, hb]; simp)
  have hiq : i ≫ q = 𝟙 X := H.lift_fst _ _ _
  have his : i ≫ s' = s ≫ spMap π := H.lift_snd _ _ _
  have hp : IsPullback i s s' (spMap π) :=
    IsPullback.of_right (by rw [hiq, hb]; exact IsPullback.id_horiz s) his H
  have k1 : Smooth s' := MorphismProperty.of_isPullback (P := @Smooth) H hs
  have k2 : IsSeparated s' := MorphismProperty.of_isPullback (P := @IsSeparated) H hs'
  have k3 : QuasiCompact s' := MorphismProperty.of_isPullback (P := @QuasiCompact) H hs''
  let D₀ := Data.self s hs hs' hs''
  let D' := Data.ofQuot κ hκ π (fun a ↦ ⟨_, hπ a⟩) rfl s' s i k1 k2 k3 hp _ rfl
  have w : 𝟙 X ≫ 𝟙 X = i ≫ q := by rw [hiq, Category.id_comp]
  have key := n D₀ D' (algebraMap R D) q (𝟙 X) H.w m w
  obtain ⟨e, e', he⟩ : ∃ (e : Cris.H1 (dp0 R) s ≃ₗ[R] HH1 s) (e' : Cris.H1 κ (s ≫ spMap π) ≃ₗ[D] HH1 s'),
      ∀ c, IsPull1 H.w (e c) (e' (m.pull1 c)) := ⟨e₁ D₀, e₁ D', key⟩
  exact (GlobalTheory.T.liftBaseChange_bijective_linearEquiv_square_univ R D (Cris.H1 (dp0 R) s) (HH1 s) (Cris.H1 κ (s ≫ spMap π)) (HH1 s')
    e.toLinearMap e'.toLinearMap m.pull1 (pullHH1 H.w) e.bijective e'.bijective fun c ↦ (he c).eq_pullHH1).2
    (GlobalTheory.T.hyper_cohomology_flat_base_change R D X X' s s' q H hs' hs'')

end GlobalTheory.CrysFlatBC
