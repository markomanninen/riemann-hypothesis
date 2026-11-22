module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.UnifAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ObjAt

theorem exists_obj_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (f : X ⟶ Y.X) (t : SAB H X) (_ : SABMap t Y.t f) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (x : Sp Ω ⟶ Xo.XF c), ξ ≫ f = x ≫ Y.j → ∃ (s : Sp Ω ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s), Nonempty (SABMap o.t t ξ) := by
  intro E _ _ _ H D l Xo c O _ β Y X f t h Ω _ ξ x hx
  obtain ⟨o, ⟨mP⟩⟩ := GlobalTheory.obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l)
    (RingHom.id _) _ _ _ (x ≫ (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)) x rfl rfl (by rw [show spMap (RingHom.id (KA l)) = 𝟙 (Sp (KA l)) by simp [spMap], Category.comp_id]) Y.oF
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t o.t Y.j x Y.m mP.toSABMap
  have n' : SABMap o.t Y.t (ξ ≫ f) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast n hx.symm
  obtain ⟨k, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t t o.t f ξ h n'
  exact ⟨_, o, ⟨k⟩⟩

end GlobalTheory.CompanionTheory.Ar.ObjAt
