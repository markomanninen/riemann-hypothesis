module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTriple

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem GlobalTheory.OneBasis.exists_rigPull_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (K : Type) [Field K] (x : Sp K ⟶ Z), PolAt t x → ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ t.G.left) (w : LB.Iso A.L (t.PP.L.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A))), RigPull A.A t.G x φ w ρ t.PP.rig := by
  intro _ _ E _ _ _ H Z t K _ x ⟨hp, hA, hK⟩
  have hsemi : IsSemiAbelian ((Over.pullback x).obj t.G) := by
    refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
    · have := t.semi.comm
      infer_instance
    · have := t.semi.smooth
      change Smooth (pullback.snd t.G.hom x)
      infer_instance
    · have := t.semi.separated
      change IsSeparated (pullback.snd t.G.hom x)
      infer_instance
    · have := t.semi.quasiCompact
      change QuasiCompact (pullback.snd t.G.hom x)
      infer_instance
    · have := t.semi.geomConnected
      change GeometricallyConnected (pullback.snd t.G.hom x)
      infer_instance
    · intro Ω _ _ q
      obtain ⟨A⟩ := t.semi.fibres Ω (q ≫ x)
      exact ⟨torusExtOfIso (pullCompIso q x t.G) A⟩
  have hpull : ∃ (PP' : RigLB ((Over.pullback x).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
      (m : SABMap ⟨(Over.pullback x).obj t.G, hsemi,
        Geo.Tor.OAct.pullback x t.G t.act, PP', cub, sym, adj, prim⟩ t x),
      m.φ = pullback.fst t.G.hom x := by
    have h := isGrpPullback_pullback t.G x
    obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := CubePf.cubePull _ _ t.G _ (cubeMapOf h) t.PP t.cub
    have hact : ∀ a, ((Geo.Tor.OAct.pullback x t.G t.act).act a).left ≫ pullback.fst t.G.hom x =
        pullback.fst t.G.hom x ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
    have pa : ∀ {T : Over _} (y : T ⟶ (Over.pullback x).obj t.G) a,
        pushPt h.1.w (y ≫ (Geo.Tor.OAct.pullback x t.G t.act).act a) = pushPt h.1.w y ≫ t.act.act a := fun y a =>
      Over.OverMorphism.ext (by
        show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
        rw [Category.assoc, hact, Category.assoc])
    refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
    · let U := lift (pushPt h.1.w (fst ((Over.pullback x).obj t.G) ((Over.pullback x).obj t.G)))
        (pushPt h.1.w (snd ((Over.pullback x).obj t.G) ((Over.pullback x).obj t.G)))
      refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U])
        · simp [U]
      · fin_cases i
        · simp [U]
        · exact (pa _ _).trans (by simp [U])
    · let U := pushPt h.1.w (𝟙 ((Over.pullback x).obj t.G))
      refine LBIso.chartPull (chartPullPull t.PP.L _)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := hpull
  let t' : SAB H (Spec (CommRingCat.of K)) :=
    ⟨(Over.pullback x).obj t.G, hsemi,
      Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t x := m₁
  have hm₀ : m₀.cm.F = pullback.fst t.G.hom x := hm₁
  obtain ⟨w, hw, hr, -⟩ := m₀.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom x)) := hm₀ ▸ ⟨w, hw⟩
  have hM := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  have hL' : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom x)).pull (𝟙 t'.G.left)) :=
    LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) hL
  obtain ⟨v, hv⟩ := hL'
  have : IsMonHom (Iso.refl t'.G).hom := inferInstanceAs (IsMonHom (𝟙 t'.G))
  have hid : IsGrpPullback t'.G t'.G (𝟙 _) (𝟙 t'.G.left) := isGrpPullback_of_iso (Iso.refl t'.G)
  have hA' : RelAmple t'.G t'.PP.L :=
    relAmple_pull hid.1 hM t'.PP.isLB ((isGen_iff v).1 hv) ⊤ (isAffineOpen_top _) (fun _ => trivial) hA
  have hK' : KTriv t'.G t'.PP.L := kTriv_pull hid hM t'.PP.isLB ((isGen_iff v).1 hv) hK
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have : ConnectedSpace ↥t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t'.G.hom (Classical.arbitrary _)
  have hP : PMaps w (K := PUnit) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m₀.cm.e :=
    (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m₀.cm.e _
      (rigPull_le m₀.cm.F m₀.cm.e m₀.cm.e_comm t.PP.L) (fun _ => rfl)).1 hr
  rw [m₀.base] at hP
  exact ⟨GlobalTheory.GenericPol.toPolAV t' g hg hp hA' hK', m₀.cm.F, w, t'.PP.rig, m₀.cart, hw, t'.PP.rigGen, hP⟩
