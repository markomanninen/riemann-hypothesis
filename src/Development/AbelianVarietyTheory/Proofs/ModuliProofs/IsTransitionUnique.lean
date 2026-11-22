module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DominatesLiftUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.TransitionUnique

open GlobalTheory.ModelCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem isReduced_XF (Xo : Moduli D l) (c : Coeff l) : IsReduced (Xo.XF c) :=
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).1

theorem map_unique {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} [IsReduced S]
    {t : SAB H S} {r r' : S ⟶ Xo.XF c} (ν : SABMap t Y.oF.t r) (ν' : SABMap t Y.oF.t r')
    (hr : r ≫ pullback.snd _ _ = r' ≫ pullback.snd _ _)
    (hM : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.eta a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.eta a).left)
    (hA : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.etaA a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.etaA a).left) : r = r' := open GlobalTheory.ObjPull in by
  let o : Obj D l _ (r ≫ _) :=
    have hL : LBIso t.PP.L (Y.oF.t.PP.L.pull ν.cm.F) := by
      obtain ⟨w, hw, -⟩ := ν.lin
      exact ⟨w, hw⟩
    have hpr := Y.oF.proper
    have hp := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
      (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.PP.L t.PP.L Y.oF.t.PP.isLB t.PP.isLB
      (AbelianSchemeGerms.isAbelianScheme_of_proper Y.oF.t.G Y.oF.t.semi) ν.cart hL
    { t := t
      proper := MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 hpr
      ample := hp.2.1 Y.oF.ample
      ktriv := hp.2.2 Y.oF.ktriv
      eta := fun a => secPull ν.cart (Y.oF.eta a)
      eta_add := fun a c => by rw [Y.oF.eta_add, map_mul]
      eta_ker := fun a ha => by rw [Y.oF.eta_ker a ha, map_one]
      etaA := fun a => secPull ν.cart (Y.oF.etaA a)
      etaA_add := fun a c => by rw [Y.oF.etaA_add, map_mul]
      etaA_ker := fun a => by rw [Y.oF.etaA_ker a, map_one]
      geom := fun k _ _ x β hx => by
        obtain ⟨hdet, I, hI, hA, hM⟩ := Y.oF.geom k (x ≫ r) β (by rw [Category.assoc, hx])
        refine ⟨fun τ => ?_, tateMove (pushEquiv ν.cart (Over.mk x)) (fun c g => ?_) (fun n g g' u hc => ?_) I,
          hI, fun a => ?_, fun a ha => ?_⟩
        · rw [GlobalTheory.LiePull.lieMult_pull _ (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.act t.act ν.cart ν.act k x τ,
            GlobalTheory.LiePull.lieMult_pull _ (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.act t.act ν.cart ν.act k x τ]
          exact hdet τ
        · apply Over.OverMorphism.ext
          show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
          rw [Category.assoc, ν.act, Category.assoc]
        · exact (GlobalTheory.weilIs_grpPullback_of_comm (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.PP.L t.PP.L Y.oF.t.PP.isLB t.PP.isLB
            ν.cart hL (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
        · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull ν.cart _ _).trans (hA a))
        · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull ν.cart _ _).trans (hM a ha)) }
  let n : ObjMap o Y.oF r := ⟨ν, fun _ => secPull_left ν.cart _, fun _ => secPull_left ν.cart _⟩
  have sec_eq {e : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G} {e' : 𝟙_ (Over S) ⟶ t.G}
      (h : e'.left ≫ ν.φ = r ≫ e.left) : e' = secPull ν.cart e := by
    apply Over.OverMorphism.ext
    apply ν.cart.1.hom_ext
    · exact h.trans (secPull_left ν.cart _).symm
    · rw [Over.w, Over.w]
  let n' : ObjMap o Y.oF r' := ⟨ν', fun a => by
      obtain ⟨x, h, h'⟩ := hM a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq h)).symm.trans h', fun a => by
      obtain ⟨x, h, h'⟩ := hA a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq h)).symm.trans h'⟩
  obtain ⟨k, -⟩ := ObjComp.objMap_comp Y.m0 n
  obtain ⟨k', -⟩ := ObjComp.objMap_comp Y.m0 n'
  refine pullback.hom_ext ((Xo.rep S _ ‹_› o).unique ⟨Category.assoc _ _ _, ⟨k⟩⟩ ⟨?_, ⟨k'⟩⟩) hr
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hr, Category.assoc]

end GlobalTheory.TransitionUnique
