module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StdSmoothMvPolynomial
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GaExp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieInh

def ev {A : Type} [CommRing A] {T : Scheme.{0}} (x : Sp A ⟶ T) : Γ(T, ⊤) →+* A :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

private theorem ev_eps_eq_ev {T : Scheme.{0}} (x : Sp (DualNumber ℂ) ⟶ T) (h) (f : Γ(T, ⊤)) :
    GlobalTheory.FibreDeriv.evEps x ⊤ h f = ev x f := by
  have hx : x.appLE ⊤ ⊤ h = x.app ⊤ := by
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  simp only [GlobalTheory.FibreDeriv.evEps, ev, hx]

theorem valAt'_top {T : Scheme.{0}} (x : Sp ℂ ⟶ T) (f : Γ(T, ⊤)) : valAt' x ⊤ f = ev x f := by
  have hx : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x) = x := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext z
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have h1 := GlobalTheory.FibreDeriv.fst_evEps (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x) x hx ⊤ le_rfl f
  rw [← h1, ev_eps_eq_ev]
  have key : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom =
      (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, Category.assoc]
  have h2 := congrArg (fun g => (g.hom f).fst) key
  simpa [ev, TrivSqZeroExt.algebraMap_eq_inl] using h2

variable {R : Type} [CommRing R]

variable {G : Over (Sp R)} [GrpObj G] {g n : ℕ} {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)}
  {ψ : (Fin n → ℂ) → (R →+* ℂ)}

end GlobalTheory.CompanionTheory.Ar.Flat.GaExp
