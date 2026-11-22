module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidLineBundleIsoDescentAlongGaloisCover
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

open GlobalTheory.CechPic

namespace GlobalTheory.DescGalRig

variable {S : Scheme.{0}}

theorem one_left (A : Over S) [GrpObj A] : (1 : A ⟶ A).left = A.hom ≫ eSec A := by
  have hu : (toUnit A).left = A.hom := (Category.comp_id _).symm.trans (Over.w (toUnit A))
  show (toUnit A ≫ η[A]).left = _
  rw [Over.comp_left, hu]
  rfl

theorem eSec_lift_one' (A : Over S) [GrpObj A] : eSec A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left = eSec (A ⊗ A) := by
  apply pullback.hom_ext
  · change eSec A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left ≫ (fst A A).left = eSec (A ⊗ A) ≫ (fst A A).left
    show (η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) ≫ fst A A).left = (η[A ⊗ A] ≫ fst A A).left
    simp [Hom.one_def]
  · change eSec A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left ≫ (snd A A).left = eSec (A ⊗ A) ≫ (snd A A).left
    show (η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) ≫ snd A A).left = (η[A ⊗ A] ≫ snd A A).left
    simp [Hom.one_def]

variable {X Y : Scheme.{0}}

theorem one_left_comm {π : X ⟶ Y} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    (gp : IsGrpPullback A A₀ π φ) : (1 : A ⟶ A).left ≫ φ = φ ≫ (1 : A₀ ⟶ A₀).left := by
  rw [one_left, one_left, Category.assoc, GlobalTheory.PolBaseChange.eSec_comm gp, ← Category.assoc, ← gp.1.w,
    Category.assoc]

theorem lift_one_comm {π : X ⟶ Y} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left} (gp : IsGrpPullback A A₀ π φ) (sq : IsSquare φ φ₂) :
    (lift (1 : A ⟶ A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left := by
  have a₁ := congrArg (fun q => q.left) (lift_fst (1 : A ⟶ A) (𝟙 A))
  have a₂ := congrArg (fun q => q.left) (lift_snd (1 : A ⟶ A) (𝟙 A))
  have b₁ := congrArg (fun q => q.left) (lift_fst (1 : A₀ ⟶ A₀) (𝟙 A₀))
  have b₂ := congrArg (fun q => q.left) (lift_snd (1 : A₀ ⟶ A₀) (𝟙 A₀))
  simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
  apply GlobalTheory.SquareDescent.square_hom_ext A₀
  · rw [Category.assoc, sq.1, ← Category.assoc, a₁, Category.assoc, b₁, one_left_comm gp]
  · rw [Category.assoc, sq.2, ← Category.assoc, a₂, Category.assoc, b₂, Category.id_comp, Category.comp_id]

theorem lift_one_comm' {π : X ⟶ Y} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left} (gp : IsGrpPullback A A₀ π φ) (sq : IsSquare φ φ₂) :
    (lift (𝟙 A) (1 : A ⟶ A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left := by
  have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 A) (1 : A ⟶ A))
  have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 A) (1 : A ⟶ A))
  have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 A₀) (1 : A₀ ⟶ A₀))
  have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 A₀) (1 : A₀ ⟶ A₀))
  simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
  apply GlobalTheory.SquareDescent.square_hom_ext A₀
  · rw [Category.assoc, sq.1, ← Category.assoc, a₁, Category.assoc, b₁, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, sq.2, ← Category.assoc, a₂, Category.assoc, b₂, one_left_comm gp]

theorem exists_gen_of_side {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {A : Over X} [GrpObj A]
    {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left} {φ₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left}
    {P : LB (A ⊗ A).left} {P₀ : LB (A₀ ⊗ A₀).left} (hG : GlobalTheory.ZM.IsGaloisCover Ga ρ π) (hA₀ : IsAbelianScheme A₀)
    (gp : IsGrpPullback A A₀ π φ) (hP : P.IsLB) (hP₀ : P₀.IsLB) (i : LBIso P (P₀.pull φ₂))
    (h0 : ∃ t : (P₀.pull (eSec (A₀ ⊗ A₀))).Gen, t.IsGen)
    (k : A.left ⟶ (A ⊗ A).left) (k₀ : A₀.left ⟶ (A₀ ⊗ A₀).left) (hk : k ≫ φ₂ = φ ≫ k₀)
    (he : eSec A₀ ≫ k₀ = eSec (A₀ ⊗ A₀)) (hgen : ∃ t : (P.pull k).Gen, t.IsGen) :
    ∃ t : (P₀.pull k₀).Gen, t.IsGen := by
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hN := LB.isLB_pull hP₀ k₀
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π A₀ _ hA₀ hN
    inferInstance inferInstance inferInstance ?_ ?_
  · obtain ⟨t, ht⟩ := h0
    exact gen_chartPull (chartPullOut P₀ (fun _ : PUnit => k₀) (fun _ => 1) (eSec A₀)
      (fun _ => eSec (A₀ ⊗ A₀)) (fun _ => he.symm)) t ht
  · have hiso : LBIso (P.pull k) ((P₀.pull φ₂).pull k) :=
      i.chartPull (chartPullPull P k) (chartPullPull (P₀.pull φ₂) k)
    have htrans : ∀ {U : Scheme.{0}} {L M : LB U}, L.IsLB → M.IsLB → LBIso L M →
        (∃ t : L.Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
      intro U L M hL hM h H
      obtain ⟨w, hw⟩ := h.chartPull (chartPullId L) (chartPullPull M (𝟙 U))
      obtain ⟨t, ht⟩ := H
      obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull L (𝟙 U)) t ht
      obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hM hL a ha
      exact gen_chartPull (chartPullUnpull M _ (Category.id_comp _)) c hc
    obtain ⟨t, ht⟩ := htrans (LB.isLB_pull hP k) (LB.isLB_pull (LB.isLB_pull hP₀ φ₂) k) hiso hgen
    obtain ⟨u, hu⟩ := gen_chartPull (chartPullIn P₀ (fun _ : PUnit => φ₂) (fun _ => 1) k) t ht
    have hc : pullback.fst A₀.hom π ≫ k₀ = (gp.1.isoPullback.inv ≫ k) ≫ φ₂ := by
      rw [Category.assoc, hk, ← Category.assoc, gp.1.isoPullback_inv_fst]
    apply gen_chartPull (chartPullOut P₀ (fun _ : PUnit => k₀) (fun _ => 1) (pullback.fst A₀.hom π)
      (fun _ => gp.1.isoPullback.inv ≫ (k ≫ φ₂)) (fun _ => by rw [← Category.assoc, ← hc]))
      (LB.pullGen P₀ (fun _ : PUnit => k ≫ φ₂) (fun _ => 1) u gp.1.isoPullback.inv)
    exact DVR.pullGen_isGen _ _ _ u hu _

end GlobalTheory.DescGalRig

theorem GlobalTheory.DescGalRig.exists_gen_lift_of_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → (∃ t : (P₀.pull (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left).Gen, t.IsGen) ∧ (∃ t : (P₀.pull (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left).Gen, t.IsGen) := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hG _ hA₀ gp sq hP hP₀ i h0 h₁ h₂
  exact ⟨GlobalTheory.DescGalRig.exists_gen_of_side hG hA₀ gp hP hP₀ i h0 _ _ (GlobalTheory.DescGalRig.lift_one_comm gp sq)
      (GlobalTheory.SquareDescent.eSec_lift_one A₀) h₁,
    GlobalTheory.DescGalRig.exists_gen_of_side hG hA₀ gp hP hP₀ i h0 _ _ (GlobalTheory.DescGalRig.lift_one_comm' gp sq)
      (GlobalTheory.DescGalRig.eSec_lift_one' A₀) h₂⟩
