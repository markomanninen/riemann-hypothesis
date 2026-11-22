module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolAdjointRing

theorem polForm_adjoint : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm S (HdR A)}, IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
   intro P E _ _ _ H Dw l Xo S _ x A _ π hπ a ha ψ hψ z u v
   have hG := ObjDim.isAbelianScheme Xo.univ
   have hA : IsAbelianScheme A := by
     have := hG.comm
     have hc : IsCommMonObj A := by
       rw [isCommMonObj_iff_isMulCommutative]
       intro T
       refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
       rw [← hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl,
         ← hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl, _root_.mul_comm]
     exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hπ.1 hG.smooth,
       MorphismProperty.of_isPullback (P := @IsProper) hπ.1 hG.proper,
       MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ.1 hG.geomConnected⟩
   have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
     (ObjDim.smoothOfRelativeDimension Xo.univ)
   have := hA.comm
   have := a.hom
   exact GlobalTheory.PolAdjoint.adjoint_of_lbIso P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hψ (a.act z)
     (a.act (H.bar z)) (GlobalTheory.PolAdjoint.lbIso_cube hπ _ (ha z) (ha (H.bar z)) (Xo.univ.t.adj z)) u v
end GlobalTheory.PolAdjointRing
