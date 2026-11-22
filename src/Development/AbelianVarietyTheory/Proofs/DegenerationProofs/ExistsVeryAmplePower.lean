module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmpleStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsVeryAmpleH1Zero

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Algebraise

theorem exists_veryAmple_h1Zero_pull : ∀ (A : Type) [CommRing A] (X : Over (Spec (CommRingCat.of A))) (L : LB X.left), L.IsLB → RelAmple X L → ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (g₀ : A →+* K) (X₀ : Scheme.{0}) (π : X₀ ⟶ X.left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ X.hom (Spec.map (CommRingCat.ofHom g₀)) → ∃ d : ℕ, 1 ≤ d ∧ FirstCohomologyVanishes ((AbLaw.pw L d).pull π) ∧ ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (AbLaw.pw L d)), VeryAmpleBy X.hom (AbLaw.pw L d) s := by
  intro A _ X L hL h K _ _ g₀ X₀ π f₀ hπ
  obtain ⟨d₀, hd₀, n₀, s₀, hs₀⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy A X L hL).1 h
  have isLB_pw {Y : Scheme.{0}} {H : LB Y} (hH : H.IsLB) (t : ℤ) :
      (AbLaw.pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have hH := isLB_pw hL (d₀ : ℤ)
  have hH₀ := LB.isLB_pull hH π
  let s' := fun j => GlobalTheory.Cartier.secPull (s₀ j) π
  haveI : IsClosedImmersion (pullback.lift π f₀ hπ.w) := by
    have e : pullback.lift π f₀ hπ.w = hπ.isoPullback.hom := by
      apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).trans hπ.isoPullback_hom_fst.symm
      · exact (pullback.lift_snd _ _ _).trans hπ.isoPullback_hom_snd.symm
    rw [e]
    infer_instance
  have hva : VeryAmpleBy f₀ _ s' := by
    haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) hπ.flip inferInstance
    have loc (i : Fin (n₀ + 1)) : nonzeroLocus (s' i) = π ⁻¹ᵁ nonzeroLocus (s₀ i) :=
      GlobalTheory.Cartier.nonzeroLocus_secPull (s₀ i) π
    have restrict_app {U : X.left.Opens} {V W : X₀.Opens}
        (e : V ≤ π ⁻¹ᵁ U) (hWV : W ≤ V) (a : Γ(X.left, U)) :
        rs X₀ hWV ((π.appLE U V e).hom a) = (π.appLE U W (hWV.trans e)).hom a :=
      congrArg (fun q => q.hom a) (π.appLE_map e (homOfLE hWV).op)
    refine ⟨GlobalTheory.ProjSpace.iSup_nonzeroLocus_secPull hs₀.1 π, fun i => ?_⟩
    obtain ⟨haff, r, hr, hsurj⟩ := hs₀.2 i
    refine ⟨by rw [loc]; exact haff.preimage π, fun j => (π.appLE _ _ (loc i).le).hom (r j), ?_, ?_⟩
    · intro j k
      have e := GlobalTheory.Cartier.pull_U (AbLaw.pw L (d₀ : ℤ)) π k
      change rs X₀ inf_le_right ((π.appLE _ _ e.le).hom ((s₀ j).f (k ⟨⟩))) =
        rs X₀ inf_le_left ((π.appLE _ _ (loc i).le).hom (r j)) *
          rs X₀ inf_le_right ((π.appLE _ _ e.le).hom ((s₀ i).f (k ⟨⟩)))
      rw [restrict_app, restrict_app, restrict_app]
      exact Segre.ap_ratio π (hr j (k ⟨⟩)) (inf_le_left.trans (loc i).le)
        (inf_le_right.trans e.le)
    · intro x
      refine VeryAmplePull.closure_eq_top hπ.w haff (loc i) (RingHom.range _) (fun d => ?_)
        (fun c => ?_) x
      · obtain ⟨p, rfl⟩ := hsurj d
        refine ⟨MvPolynomial.map g₀ p, ?_⟩
        rw [MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
        exact congrArg (fun q => MvPolynomial.eval₂Hom q _ p)
          (RingHom.ext fun c => (VeryAmplePull.appLE_cst hπ.w _ _ _ c).symm)
      · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.serre_vanishing_very_ample.1 K X₀ f₀ _ n₀ s' hH₀ hva _ hH₀
  have h1 := ht₀ (t₀.toNat : ℤ) (Int.self_le_toNat t₀)
  obtain ⟨w, hw⟩ := lbIso_tw hH₀ (t₀.toNat : ℤ)
  have h2 := H1Iso.firstCohomologyVanishes_of_iso_of_isGen (isLB_tw hH₀ hH₀ _).cover (isLB_pw hH₀ _) w hw h1
  have h3 := veryAmpleBy_pw A X.left X.hom _ n₀ s₀ hH hs₀ (t₀.toNat + 1) (Nat.le_add_left _ _)
  have e : AbLaw.pw (AbLaw.pw L (d₀ : ℤ)) ((t₀.toNat + 1 : ℕ) : ℤ) =
      AbLaw.pw L ((d₀ * (t₀.toNat + 1) : ℕ) : ℤ) := by
    rw [pw_pw, Nat.cast_mul]
  refine ⟨d₀ * (t₀.toNat + 1), Nat.mul_pos hd₀ (Nat.succ_pos _), ?_, ?_⟩
  · rw [← e, pw_pull, Nat.cast_add, Nat.cast_one]
    exact h2
  · rw [← e]
    exact h3

end GlobalTheory.Algebraise
