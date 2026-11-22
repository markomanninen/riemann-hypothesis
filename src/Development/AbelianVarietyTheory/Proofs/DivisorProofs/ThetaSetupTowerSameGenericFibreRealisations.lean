module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem Tower.same : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ 𝔗 : Tower X₁ act, GlobalTheory.Poinc.Same X₁.ρ act 𝔗.X₂.ρ 𝔗.act₂ 𝔗.lam (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁) := by
  intro g n F W Z i X₁ act hact 𝔗
  let f₂ : Sp 𝔗.X₂.Ω₁ ⟶ Sp 𝔗.X₂.S.R := spMap 𝔗.X₂.S.R.val.toRingHom
  let P₀ : PolAV (Sp 𝔗.X₂.Ω₁) :=
    { A := (Over.pullback f₂).obj 𝔗.X₂.ρ.P.A
      isAb := TLinPf.isAb_pullback f₂ _ 𝔗.X₂.ρ.P.isAb
      g := 𝔗.X₂.ρ.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂).1 𝔗.X₂.ρ.P.smoothDim
      L := 𝔗.X₂.ρ.P.L.pull (pullback.fst 𝔗.X₂.ρ.P.A.hom f₂)
      isLB := pull_isLB 𝔗.X₂.ρ.P.isLB _
      rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂) 𝔗.X₂.ρ.P.rigid
      sym := PolBaseChange.sym_pull (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂) 𝔗.X₂.ρ.P.sym
      ample := by
        haveI := 𝔗.X₂.ρ.P.isAb.proper
        exact AmpleBaseChange.relAmple_of_isPullback 𝔗.X₂.ρ.P.isLB 𝔗.X₂.ρ.P.ample
          (IsPullback.of_hasPullback 𝔗.X₂.ρ.P.A.hom f₂)
      ktriv := by
        obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB 𝔗.X₂.ρ.P.isLB (pullback.fst 𝔗.X₂.ρ.P.A.hom f₂))
        exact kTriv_pull (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂) 𝔗.X₂.ρ.P.isLB (pull_isLB 𝔗.X₂.ρ.P.isLB _) ((isGen_iff w).1 hw) 𝔗.X₂.ρ.P.ktriv }
  let a' : P₀.A.left ⟶ 𝔗.X₂.ρ.P.A.left := pullback.fst 𝔗.X₂.ρ.P.A.hom f₂
  have hring : (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom = 𝔗.X₂.S.R.val.toRingHom.comp 𝔗.om := by
    ext x; exact (𝔗.om_eq x).symm
  have hsp : spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) = f₂ ≫ spMap 𝔗.om := by
    rw [hring]; exact Spec.map_comp (CommRingCat.ofHom 𝔗.om) (CommRingCat.ofHom 𝔗.X₂.S.R.val.toRingHom)
  have ha' : IsGrpPullback P₀.A 𝔗.X₂.ρ.P.A f₂ a' := isGrpPullback_pullback _ _
  have hr : LBIso P₀.L (𝔗.X₂.ρ.P.L.pull a') := ⟨idIso _, idIso_isGen P₀.isLB⟩
  refine ⟨P₀, a' ≫ 𝔗.φ, a', fun E => (Over.pullback f₂).map (𝔗.act₂ E), ?_, ha', ?_, hr, ?_, ?_⟩
  · exact (ha'.comp 𝔗.cart).congr hsp.symm rfl
  · exact LBIso.trans P₀.isLB (pull_isLB 𝔗.X₂.ρ.P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hr (lbIso_pull_comp 𝔗.lb a')
  · intro E
    have h1 : ((Over.pullback f₂).map (𝔗.act₂ E)).left ≫ a' = a' ≫ (𝔗.act₂ E).left :=
      pullback.lift_fst _ _ _
    refine ⟨?_, h1⟩
    have h2 : (a' ≫ (𝔗.act₂ E).left) ≫ 𝔗.φ = a' ≫ 𝔗.φ ≫ (act E).left := by
      rw [Category.assoc, 𝔗.act_eq]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) h1).trans h2)
  · intro x
    have hc : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ ≫ f₂ := by
      rw [Category.assoc, Over.w (𝔗.X₂.ρ.pt (𝔗.lam x))]
      simp [baseOver]
    refine ⟨pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc, ?_, ?_⟩
    · have hw : pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc ≫ a' = f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left :=
        pullback.lift_fst _ _ _
      have h3 : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.φ =
          spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) ≫ (X₁.ρ.pt x).left := by
        rw [Category.assoc, 𝔗.lam_pt, hsp, Category.assoc]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) hw).trans h3)
    · exact pullback.lift_fst _ _ _
end GlobalTheory.Poinc.Sep
