module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.LatticeTransfer
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CutPull

variable {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X}

theorem homEquiv_pullbackZIso_hom (hL : L.IsLB) (G : X.Modules) (n : ℤ) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackZIso G f hL n).hom =
      Twist.map (lbZPow L n) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) ≫
        (projZIso f hL ((Scheme.Modules.pullback f).obj G) n).inv := by
  have e : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (twist G (lbZPow L n)) ≫
      (Scheme.Modules.pushforward f).map (pullbackHom G (lbZPow L n) f) =
        Twist.map (lbZPow L n) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) ≫
          (projIso (lbZPow L n) f _).inv :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  rw [Adjunction.homEquiv_unit, pullbackZIso, Iso.trans_hom, Functor.map_comp, ← Category.assoc,
    pullbackIso_hom, e, projZIso, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_hom, Category.assoc]

theorem pullback_mulSecOfEq (hL : L.IsLB) (G : X.Modules) {n m k : ℤ} (σ : LB.Sec (lbZPow L m))
    (h : n + m = k) :
    (Scheme.Modules.pullback f).map (mulSecOfEq G σ h) ≫ (pullbackZIso G f hL k).hom =
      (pullbackZIso G f hL n).hom ≫ mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f σ) h := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_pullbackZIso_hom, homEquiv_pullbackZIso_hom, Category.assoc]
  have e : (Scheme.Modules.pushforward f).map
      (mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f σ) h) ≫
        (projZIso f hL ((Scheme.Modules.pullback f).obj G) k).hom =
      (projZIso f hL ((Scheme.Modules.pullback f).obj G) n).hom ≫
        mulSecOfEq ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj G)) σ h := by
    refine zhom_ext fun V (s : Γ(twistZ ((Scheme.Modules.pullback f).obj G) (L.pull f) n, f ⁻¹ᵁ V)) i => ?_
    refine (zcoord_projZIso_hom_app f hL _ ((mulSecOfEq _ (zpull f σ) h).app _ s) i).trans ?_
    refine Eq.trans ?_ (zcoord_mulSecOfEq_app σ h ((projZIso f hL _ n).hom.app V s) i).symm
    have e : (f.app (V ⊓ L.U i)).hom (resG X inf_le_right (zfun σ i)) =
        (f.appLE (L.U i) _ (f.preimage_mono (inf_le_right : V ⊓ L.U i ≤ L.U i))).hom (zfun σ i) := by
      rw [← Scheme.Hom.appLE_eq_app, LB.appLE_resG]
    rw [zcoord_mulSecOfEq_app, resM_smul, resG_resG, zfun_zpull, LB.resG_appLE]
    refine Eq.trans (congrArg (· • resM _ (le_pidx_inf f V i) (zcoord s (pidx L f i))) e.symm) ?_
    exact congrArg (fun t : Γ((Scheme.Modules.pullback f).obj G, f ⁻¹ᵁ (V ⊓ L.U i)) =>
      (f.app (V ⊓ L.U i)).hom (resG X inf_le_right (zfun σ i)) • t)
      (zcoord_projZIso_hom_app f hL _ s i).symm
  have e' : (projZIso f hL ((Scheme.Modules.pullback f).obj G) n).inv ≫
      (Scheme.Modules.pushforward f).map (mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f σ) h) =
        mulSecOfEq ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj G)) σ h ≫
          (projZIso f hL ((Scheme.Modules.pullback f).obj G) k).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact e
  rw [e', ← Category.assoc, ← Category.assoc]
  congr 1
  symm
  refine zhom_ext fun V s i => ?_
  change zcoord ((mulSecOfEq _ σ h).app V ((Twist.map (lbZPow L n) _).app V s)) i =
    zcoord ((Twist.map (lbZPow L k) _).app V ((mulSecOfEq G σ h).app V s)) i
  rw [zcoord_mulSecOfEq_app, zcoord_map_app, zcoord_map_app, zcoord_mulSecOfEq_app,
    Scheme.Modules.Hom.app_smul]

end GlobalTheory.CutPull

namespace GlobalTheory


open GlobalTheory.CutPull in
theorem cut_pullback_iso : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [G.IsQuasicoherent] {L : LB X} (hL : L.IsLB) (s : L.Sec) (hL' : (L.pull f).IsLB), Nonempty ((Scheme.Modules.pullback f).obj (cut G hL s) ≅ cut ((Scheme.Modules.pullback f).obj G) hL' (secPull s f)) := by
  intro X Y f G _ L hL s hL'
  have : PreservesColimits (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  have hz : ∀ j, zfun (zpull f (zofSec s)) j = zfun (zofSec (secPull s f)) j := fun j => by
    rw [zfun_zpull, zfun_zofSec, zfun_zofSec]
    rfl
  have hM : mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f (zofSec s)) (neg_add_cancel (1 : ℤ)) =
      mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zofSec (secPull s f)) (neg_add_cancel (1 : ℤ)) :=
    zhom_ext fun V t j => by rw [zcoord_mulSecOfEq_app, zcoord_mulSecOfEq_app, hz]
  have e := pullback_mulSecOfEq f hL G (zofSec s) (neg_add_cancel (1 : ℤ))
  rw [hM, ← Iso.eq_comp_inv] at e
  have key : (Scheme.Modules.pullback f).map (cutHom G hL s) =
      (pullbackZIso G f hL (-1)).hom ≫
        (mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zofSec (secPull s f)) (neg_add_cancel (1 : ℤ)) ≫
          ((pullbackZIso G f hL 0).symm ≪≫ (Scheme.Modules.pullback f).mapIso (twistZZeroIso G hL).symm).hom) := by
    rw [cutHom, Functor.map_comp, e]
    simp
  exact ⟨PreservesCokernel.iso (Scheme.Modules.pullback f) (cutHom G hL s) ≪≫ cokernelIsoOfEq key ≪≫
    cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫
    (cokernelCompIsIso _ (twistZZeroIso ((Scheme.Modules.pullback f).obj G) hL').inv).symm⟩

end GlobalTheory
