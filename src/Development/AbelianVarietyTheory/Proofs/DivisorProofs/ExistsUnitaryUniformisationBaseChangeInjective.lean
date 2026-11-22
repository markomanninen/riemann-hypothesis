module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPullbackLocalMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnOfPsiOn
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USepBC


set_option maxHeartbeats 1600000 in
theorem exists_pelUnif_baseChange_of_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (y : Sp (FractionRing V) ⟶ Xo.XF c) (P : PELUnif (maximalIdeal V) t), GenOf Xo c y t → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁) (fK : FractionRing V →+* FractionRing V₁), IsCN V₁ → Function.Injective ρ → IsLocalHom ρ → (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) → ∃ (t₁ : SAB H (Sp V₁)) (P₁ : PELUnif (maximalIdeal V₁) t₁) (p : IsPullDeg ρ P.D.toPre P₁.D.toPre), GenOf Xo c (spMap fK ≫ y) t₁ ∧ (∀ (a : 𝓞 E) x, p.xe (a • x) = a • p.xe x) ∧ ∀ x r, Formalism.L2.Pj.PsiCoord P.D.toPre (p.xe x) r → ∃ w : V₁ˣ, Formalism.L2.Pj.PsiCoord P₁.D.toPre x (w * ρ r) := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hV t y P hG V₁ _ _ _ ρ fK hV₁ hρ hl hfK
  have hR : GlobalTheory.Mum.Base V := ⟨⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩, hV.2.2.2⟩
  have hR₁ : GlobalTheory.Mum.Base V₁ := ⟨⟨hV₁.1, inferInstance, hV₁.2.1, hV₁.2.2.1⟩, hV₁.2.2.2⟩
  obtain ⟨-, -, -, -, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨Wo, hWo, ⟨hψ⟩⟩ := h5.psiOnExists V (maximalIdeal V) hR.1 P.D
  let WS : Set (PrimeSpectrum V) := (Wo : Set (Sp V))
  have hWS : IsOpen WS := Wo.isOpen
  have hbot : (⊥ : PrimeSpectrum V) ∈ WS := by
    have := hWo
    rw [genericPoint_eq_bot_of_affine] at this
    exact this
  obtain ⟨_, ⟨f, rfl⟩, hf, hfW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hbot hWS
  have hf0 : f ≠ 0 := by
    intro e
    apply hf
    rw [e]
    show (0 : V) ∈ (⊥ : PrimeSpectrum V).asIdeal
    exact Ideal.zero_mem _
  have hψW : ∀ x, PsiUnitOn P.D.toPre x (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum V)) := by
    intro x j U hU hUW
    exact GlobalTheory.PsiUnitOfPsiOn.psiUnitOn_of_psiOn V P.D.toPre Wo hψ x j U hU (hUW.trans hfW)
  have hρf : ρ f ≠ 0 := fun e => hf0 (hρ (e.trans (map_zero ρ).symm))
  obtain ⟨t₁, P₁, p, ⟨m₀⟩, hlin, -⟩ := GlobalTheory.LocalPull.exists_pelUnif_pull V V₁ hR hR₁ t P ρ hl f hρf hψW
  refine ⟨t₁, P₁, p, ?_, hlin, fun x r hr => GlobalTheory.PelCoordPull.psiCoord_pull p x r hr⟩
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hG
  have semiPull {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G]
      (h : IsSemiAbelian G) : IsSemiAbelian ((Over.pullback f).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h.comm; infer_instance
    · have := h.smooth; change Smooth (pullback.snd G.hom f); infer_instance
    · have := h.separated; change IsSeparated (pullback.snd G.hom f); infer_instance
    · have := h.quasiCompact; change QuasiCompact (pullback.snd G.hom f); infer_instance
    · have := h.geomConnected; change GeometricallyConnected (pullback.snd G.hom f); infer_instance
    · intro Ω _ _ q
      obtain ⟨e⟩ := h.fibres Ω (q ≫ f)
      exact ⟨torusExtOfIso (pullCompIso q f G) e⟩
  have sabPull (hC : Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
      ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback f).obj t.G, semiPull f t.G t.semi, OAct.pullback f t.G t.act, PP', cub,
          sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
    have h := isGrpPullback_pullback t.G f
    obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
    have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
        pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
    have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
        pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
      Over.OverMorphism.ext (by
        show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
        rw [Category.assoc, hact, Category.assoc])
    refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
    · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
        (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U])
        · simp [U]
      · fin_cases i
        · simp [U]
        · exact (pa _ _).trans (by simp [U])
    · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
      refine LBIso.chartPull (chartPullPull t.PP.L _)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  obtain ⟨PP, cub, sym, adj, prim, n, -⟩ := sabPull CubePf.cubePull (jK V₁) t₁
  let tK₁ : SAB H (Sp (FractionRing V₁)) := ⟨(Over.pullback (jK V₁)).obj t₁.G, semiPull _ t₁.G t₁.semi,
    OAct.pullback _ t₁.G t₁.act, PP, cub, sym, adj, prim⟩
  have n' : SABMap tK₁ t₁ (jK V₁) := n
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ t t₁ tK₁ _ _ m₀ n'
  have sq : jK V₁ ≫ spMap ρ = spMap fK ≫ jK V := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact (hfK a).symm
  rw [sq] at b
  obtain ⟨c', -⟩ := sabCancel pullCubCancel E H _ _ _ t tK tK₁ _ _ m₁ b
  obtain ⟨d, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t tK tK₁ _ _ m₂ c'
  refine ⟨tK₁, ⟨n'⟩, ⟨?_⟩⟩
  rw [Category.assoc]
  exact d

end GlobalTheory.USepBC
