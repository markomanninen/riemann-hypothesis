module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocalFibre

theorem connectedSpace_sp (R : Type) [CommRing R] [IsLocalRing R] : ConnectedSpace (Sp R) := by
  have h : _root_.IsConnected (Set.univ : Set (PrimeSpectrum R)) := by
    refine ⟨⟨IsLocalRing.closedPoint R, trivial⟩, isPreconnected_of_forall (IsLocalRing.closedPoint R) fun x _ => ?_⟩
    exact ⟨closure {x}, Set.subset_univ _, (IsLocalRing.specializes_closedPoint x).mem_closure,
      subset_closure rfl, isPreconnected_singleton.closure⟩
  exact (connectedSpace_iff_univ.2 h : ConnectedSpace (PrimeSpectrum R))

theorem exists_polAV_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}
    {t : SAB H S} (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L)
    {R : Type} [CommRing R] [IsLocalRing R] {y : Sp R ⟶ S} {t' : SAB H (Sp R)} (m : SABMap t' t y) :
    ∃ (P : Out.PolAV (Sp R)) (φ : P.A.left ⟶ t.G.left) (act : OAct (𝓞 E) P.A),
      IsGrpPullback P.A t.G y φ ∧ LBIso P.L (t.PP.L.pull φ) ∧ ∀ a, (act.act a).left ≫ φ = φ ≫ (t.act.act a).left := by
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  obtain ⟨w, g, -⟩ := m.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := y (IsLocalRing.closedPoint R)) trivial
  have hy : ∀ x, y x ∈ U := fun x =>
    (congrArg (fun V => x ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem y hc)).mpr trivial
  have am := relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) U hU hy hA
  have kt := kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) hK
  have := connectedSpace_sp R
  have : ConnectedSpace t'.G.left := GeometricallyConnected.connectedSpace t'.G.hom t'.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (eSec t'.G (IsLocalRing.closedPoint R))
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  exact ⟨{ A := t'.G, g := d, smoothDim := hd, L := t'.PP.L, isLB := t'.PP.isLB, ample := am, ktriv := kt
           isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp, ‹_›⟩
           rigid := ⟨t'.PP.rig, t'.PP.rigGen⟩
           sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ },
    m.φ, t'.act, m.cart, ⟨w, g⟩, m.act⟩

end GlobalTheory.LocalFibre

namespace GlobalTheory

theorem exists_polAV_pullback_of_isLocalRing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), IsProper t.G.hom →
      Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ S),
      ∃ (P : Out.PolAV (Sp R)) (φ : P.A.left ⟶ t.G.left) (act : OAct (𝓞 E) P.A),
        IsGrpPullback P.A t.G y φ ∧ LBIso P.L (t.PP.L.pull φ) ∧
          ∀ a, (act.act a).left ≫ φ = φ ≫ (t.act.act a).left := by
  intro E _ _ _ H S t hp hA hK R _ _ y
  have h := isGrpPullback_pullback t.G y
  obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull S (Sp R) t.G _ (cubeMapOf h) t.PP t.cub
  have hact : ∀ a, ((OAct.pullback y t.G t.act).act a).left ≫ pullback.fst t.G.hom y =
      pullback.fst t.G.hom y ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
  have pa : ∀ {T : Over (Sp R)} (x : T ⟶ (Over.pullback y).obj t.G) a,
      pushPt h.1.w (x ≫ (OAct.pullback y t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have hsemi : IsSemiAbelian ((Over.pullback y).obj t.G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := t.semi.comm; infer_instance
    · have := t.semi.smooth; change Smooth (pullback.snd t.G.hom y); infer_instance
    · have := t.semi.separated; change IsSeparated (pullback.snd t.G.hom y); infer_instance
    · have := t.semi.quasiCompact; change QuasiCompact (pullback.snd t.G.hom y); infer_instance
    · have := t.semi.geomConnected; change GeometricallyConnected (pullback.snd t.G.hom y); infer_instance
    · intro Ω _ _ q
      obtain ⟨F⟩ := t.semi.fibres Ω (q ≫ y)
      exact ⟨torusExtOfIso (pullCompIso q y t.G) F⟩
  refine LocalFibre.exists_polAV_of_sabMap hp hA hK (t' :=
    ⟨(Over.pullback y).obj t.G, hsemi,
      OAct.pullback y t.G t.act, (cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, ?_, ?_⟩) ?_
  · intro a
    let U := lift (pushPt h.1.w (fst ((Over.pullback y).obj t.G) ((Over.pullback y).obj t.G)))
      (pushPt h.1.w (snd ((Over.pullback y).obj t.G) ((Over.pullback y).obj t.G)))
    refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
    · fin_cases i
      · exact (pa _ a).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  ·
    let U := pushPt h.1.w (𝟙 ((Over.pullback y).obj t.G))
    refine LBIso.chartPull (chartPullPull t.PP.L _ U.left (Category.id_comp _))
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
    fin_cases i
    · simp [U]
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  · exact ⟨cubeMapOf h, h, rfl, hact, hc'⟩

end GlobalTheory
