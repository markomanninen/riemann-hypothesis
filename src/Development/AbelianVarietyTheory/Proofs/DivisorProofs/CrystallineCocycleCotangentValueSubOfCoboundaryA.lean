module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

attribute [local instance] cotOp cotCentral cotTower

theorem cotSnd_cotPt_eq_dUnit (R : Type) [CommRing R] (D : Type) [CommRing D] [Bialgebra R D] (z : D) :
    cotSnd R D (cotPt R D z) = dUnit (R := R) z := by
  change TrivSqZeroExt.snd (algebraMap R (TrivSqZeroExt R (Cot R D)) (Coalgebra.counit z) +
    TrivSqZeroExt.inr (AugCot.d (Bialgebra.counitAlgHom R D) z)) = _
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

theorem crystallineCocycleCotangentValue_sub_of_coboundary (R : Type) [CommRing R]
    (X : Over (Sp R)) (D : Type) [CommRing D] [Bialgebra R D] (y : Pt X D)
    (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (k : C0 (O (dp0 R) (X.hom ≫ 𝟙 _)))
    (h : d0 _ k = f.1 - f'.1) :
    cotVal f y - cotVal f' y = dUnit (R := R) (A := D) (k (trivAt y)) := by
  have hf : f - f' = ⟨d0 _ k, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ k⟩ := Subtype.ext h.symm
  let E := cotExt R D
  let p : D →ₐ[R] E.C := cotPt R D
  let y' : Pt X E.C := spOver p ≫ y
  let k₀ : E.B := k (Thick.triv E.B _ (E.red_w y'.w))
  let i : E.C := E.i k₀
  have h1 : E.val y'.left y'.w f - E.val y'.left y'.w f' = k (trivAt y') - i := by
    rw [← map_sub, hf]
    exact E.tangentValue_coboundary y'.left y'.w k
  have h2 : fv f D E.C p y - fv f' D E.C p y = k (trivAt y') - p (k (trivAt y)) := by
    let τ : trivAt y ⟶ trivAt y' := trivMap p y
    have e := congrArg (fun g : C1 (O (dp0 R) (X.hom ≫ 𝟙 _)) ↦ g _ _ τ) h
    change d0 _ k _ _ τ = _ at e
    rw [amitsur_d0_apply, mp_O] at e
    exact e.symm
  have hi : cotSnd R D i = 0 := by
    exact TrivSqZeroExt.snd_inl (M := Cot R D) k₀
  change cotSnd R D (E.val y'.left y'.w f - fv f D E.C p y) -
    cotSnd R D (E.val y'.left y'.w f' - fv f' D E.C p y) = _
  rw [← map_sub, sub_sub_sub_comm, h1, h2, sub_sub_sub_cancel_left, map_sub]
  rw [show p (k (trivAt y)) = cotPt R D (k (trivAt y)) from rfl,
    cotSnd_cotPt_eq_dUnit, hi, sub_zero]

end GlobalTheory.PtExt
