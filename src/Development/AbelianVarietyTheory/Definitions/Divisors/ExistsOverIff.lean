module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

def UValOn (Xo : Moduli D l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) (φ : InvFun (𝓞 E)) (J : S.IdealSheafData)
    (d : ℕ) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ S) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ j = jK W ≫ χ →
    ∀ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))), Nonempty (SABMap tK t (jK W)) →
      Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∀ P : PELUnif (maximalIdeal W) t,
      ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
        ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong J χ = Ideal.span {ϖ ^ n}

def GenOf (Xo : Moduli D l) (c : Coeff l) {R : Type} [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c)
    (t : SAB H (Sp R)) : Prop :=
  ∃ tK : SAB H (Sp (FractionRing R)), Nonempty (SABMap tK t (jK R)) ∧ Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _))

variable {Xo : Moduli D l} {c : Coeff l}

theorem exists_over_iff {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (y : Sp (FractionRing R) ⟶ Xo.XF c) :
    (∃ σ : Sp R ⟶ Sp c.F, jK R ≫ σ = y ≫ pullback.snd _ _) ↔ ∀ n : ℕ, n ≠ 0 → IsUnit (n : R) := by
  constructor
  · rintro ⟨σ, -⟩ n hn
    have := (IsUnit.mk0 (n : c.F) (Nat.cast_ne_zero.2 hn)).map (Spec.preimage σ).hom
    rwa [map_natCast] at this
  · intro hu
    haveI := c.fin
    let g : c.F →+* FractionRing R := (Spec.preimage (y ≫ pullback.snd _ _)).hom
    have hint : ∀ a : c.F, ∃ r : R, algebraMap R (FractionRing R) r = g a := fun a => by
      obtain ⟨m, hm, ha⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2
        (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
      have hint : IsIntegral R (g (m • a)) := by
        obtain ⟨p, hp, h0⟩ := ha
        refine ⟨p.map (Int.castRingHom R), hp.map _, ?_⟩
        rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap R (FractionRing R)).comp (Int.castRingHom R))
          (g.comp (algebraMap ℤ c.F)), ← Polynomial.hom_eval₂, h0, map_zero]
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
      have hum : IsUnit (m : R) := by
        have := hu m.natAbs (by simpa using hm)
        rcases Int.natAbs_eq m with e | e <;> rw [e] <;> simpa using this
      obtain ⟨u, hu'⟩ := hum
      refine ⟨(↑u⁻¹ : R) * r, ?_⟩
      have e : g (m • a) = algebraMap R (FractionRing R) u * g a := by simp [hu']
      rw [map_mul, hr, e, ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    choose f hf using hint
    have hi := IsFractionRing.injective R (FractionRing R)
    let b : c.F →+* R :=
      { toFun := f
        map_one' := hi (by simp [hf])
        map_mul' := fun _ _ => hi (by simp [hf])
        map_zero' := hi (by simp [hf])
        map_add' := fun _ _ => hi (by simp [hf]) }
    refine ⟨spMap b, ?_⟩
    rw [← Spec.map_preimage (y ≫ pullback.snd _ _), ← Spec.map_comp]
    congr 1
    ext a
    exact hf a

end GlobalTheory.UPoinc
