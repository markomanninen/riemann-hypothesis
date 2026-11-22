module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPull

theorem lbIso_pull {X Y Y' : Scheme.{0}} {A : LB Y} {L : LB X} {φ : Y ⟶ X} (H : LBIso A (L.pull φ)) (h : Y' ⟶ Y)
    {F : Y' ⟶ X} (e : F = h ≫ φ) : LBIso (A.pull h) (L.pull F) :=
  H.chartPull (chartPullPull A h h rfl)
    (chartPullSame L (fun _ : PUnit => F) (fun _ : PUnit => φ) (fun _ => 1) h fun _ => e)

theorem isPEL_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s') (τ : SAB H S), f ≫ s = s' → TMap t' t f → IsPEL D a bas ρ t τ → ∃ τ' : SAB H S', IsPEL D a bas ρ t' τ' := by
  intro E _ _ _ H D g k J a bas o _ b ρ S S' s s' f t t' τ hs ⟨ψ, hψ, hψL, hpt, hact⟩ ⟨φ, hφ, hφL, hφa, hgeom⟩
  obtain ⟨τ', ⟨m⟩⟩ : ∃ τ' : SAB H S', Nonempty (SABMap τ' τ f) := by
    have hC := Out.CubePf.cubePull
    have hsemi : IsSemiAbelian ((Over.pullback f).obj τ.G) := by
      refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
      · have := τ.semi.comm
        infer_instance
      · have := τ.semi.smooth
        change Smooth (pullback.snd τ.G.hom f)
        infer_instance
      · have := τ.semi.separated
        change IsSeparated (pullback.snd τ.G.hom f)
        infer_instance
      · have := τ.semi.quasiCompact
        change QuasiCompact (pullback.snd τ.G.hom f)
        infer_instance
      · have := τ.semi.geomConnected
        change GeometricallyConnected (pullback.snd τ.G.hom f)
        infer_instance
      · intro Ω _ _ q
        obtain ⟨A⟩ := τ.semi.fibres Ω (q ≫ f)
        exact ⟨torusExtOfIso (pullCompIso q f τ.G) A⟩
    have hp : ∃ (PP' : RigLB ((Over.pullback f).obj τ.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback f).obj τ.G, hsemi, OAct.pullback f τ.G τ.act, PP', cub,
          sym, adj, prim⟩ τ f), m.φ = pullback.fst τ.G.hom f := by
      have h := isGrpPullback_pullback τ.G f
      obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' τ.G _ (cubeMapOf h) τ.PP τ.cub
      have hact : ∀ a, ((OAct.pullback f τ.G τ.act).act a).left ≫ pullback.fst τ.G.hom f =
          pullback.fst τ.G.hom f ≫ (τ.act.act a).left := fun a => pullback.lift_fst _ _ _
      have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj τ.G) a,
          pushPt h.1.w (x ≫ (OAct.pullback f τ.G τ.act).act a) = pushPt h.1.w x ≫ τ.act.act a := fun x a =>
        Over.OverMorphism.ext (by
          show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
          rw [Category.assoc, hact, Category.assoc])
      refine ⟨(cubeMapOf h).rigLB τ.PP hL hr, c', hs τ.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
      · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj τ.G) ((Over.pullback f).obj τ.G)))
          (pushPt h.1.w (snd ((Over.pullback f).obj τ.G) ((Over.pullback f).obj τ.G)))
        refine LBIso.chartPull (chartPullLinComb τ.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
          (chartPullLinComb τ.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (τ.adj a)
        · fin_cases i
          · exact (pa _ a).trans (by simp [U])
          · simp [U]
        · fin_cases i
          · simp [U]
          · exact (pa _ _).trans (by simp [U])
      · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj τ.G))
        refine LBIso.chartPull (chartPullPull τ.PP.L _ U.left (Category.id_comp _))
          (chartPullLinComb τ.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) τ.prim
        fin_cases i
        · simp [U]
        · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    obtain ⟨_, _, _, _, _, m, -⟩ := hp
    exact ⟨_, ⟨m⟩⟩
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)

  have hL : LBIso τ'.PP.L (τ.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hc : IsGrpPullback τ'.G t.A f (m.cm.F ≫ φ.hom.left) :=
    (IsGrpPullback.comp m.cart (isGrpPullback_of_iso φ)).congr (Category.comp_id f) rfl
  obtain ⟨e, he, heF⟩ := grpPullback_iso hc hψ
  refine ⟨τ', e, he, ?_, fun j => ?_, fun K _ _ _ x β hx => ?_⟩
  · exact (hL.trans τ'.PP.isLB (pull_isLB τ.PP.isLB _) (pull_isLB t.isLB _) (lbIso_pull hφL m.cm.F rfl)).trans
      τ'.PP.isLB (pull_isLB t.isLB _) (pull_isLB t'.isLB _) (lbIso_pull hψL e.hom.left heF.symm).symm
  · apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · have h₁ : (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (t.act j).left :=
        congrArg (fun z => z.left) (hφa j)
      have h₂ : (τ'.act.act (a j)).left ≫ m.cm.F = m.cm.F ≫ (τ.act.act (a j)).left := m.act _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, heF, hact, ← Category.assoc, h₂,
        Category.assoc, h₁, ← Category.assoc, ← heF, Category.assoc]
    · rw [Over.w, Over.w]
  · obtain ⟨hdet, I, hI, hA⟩ := hgeom K (x ≫ f) β (by rw [Category.assoc, hs, hx])
    refine ⟨fun σ => ?_, GlobalTheory.ObjPull.tateMove (GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)) (fun c y => ?_)
      (fun n y y' c hc => ?_) I, hI, fun i => ?_⟩
    · rw [GlobalTheory.LiePull.lieMult_pull _ S S' τ.G τ'.G f m.cm.F τ.act τ'.act m.cart m.act K x σ,
        GlobalTheory.LiePull.lieMult_pull _ S S' τ.G τ'.G f m.cm.F τ.act τ'.act m.cart m.act K x σ]
      exact hdet σ
    · apply Over.OverMorphism.ext
      show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
      rw [Category.assoc, m.act, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' τ.G τ'.G f m.cm.F τ.PP.L τ'.PP.L τ.PP.isLB τ'.PP.isLB m.cart hL
        (Over.mk x) n y y' _ _ _ rfl rfl).2 hc
    · apply Over.OverMorphism.ext
      apply hψ.1.hom_ext
      · have h₁ : (I.ev k (bas (Pi.single i 1))).left ≫ φ.hom.left = (x ≫ f) ≫ (t.pt i).left :=
          congrArg (fun z => z.left) (hA i)
        have h₂ := GlobalTheory.ObjPull.pushEquiv_symm_left m.cart (Over.mk x) (I.ev k (bas (Pi.single i 1)))
        show (((GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)).symm (I.ev k (bas (Pi.single i 1)))).left ≫ e.hom.left) ≫ ψ =
          (x ≫ (t'.pt i).left) ≫ ψ
        rw [Category.assoc, heF, Category.assoc, hpt]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ.hom.left) h₂).trans (h₁.trans (Category.assoc _ _ _)))
      · rw [Over.w, Over.w]

end GlobalTheory.PELPull
