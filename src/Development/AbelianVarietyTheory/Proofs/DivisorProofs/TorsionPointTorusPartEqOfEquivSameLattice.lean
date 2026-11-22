module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem qkPt_g_eq_of_equiv : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D F k, p.y = p'.y → QkPt.Equiv D F p p' → p.g = p'.g := by
  intro V _ _ D hB F _ _ k hk p p' hy ⟨z, hz, h, hi, ha⟩
  letI := GlobalTheory.TorusExt.gtGroup D F
  have hkz : k • z = 0 := by
    rw [hy] at hz
    exact left_eq_add.mp hz
  have z0 : z = 0 := by
    have : ((k : ℤ)) • z = 0 := by rw [natCast_zsmul]; exact hkz
    rcases smul_eq_zero.mp this with h0 | h0
    · omega
    · exact h0
  subst z0
  have h0 : h = 0 := by
    obtain ⟨w, hw, g, hg, hadd⟩ := qk_equiv_refl hB p
    have hw0 : w = 0 := by
      have hkw : k • w = 0 := left_eq_add.mp hw
      have hwz : (k : ℤ) • w = 0 := by rw [natCast_zsmul]; exact hkw
      rcases smul_eq_zero.mp hwz with hk0 | hw0
      · omega
      · exact hw0
    subst w
    have he : h = g := GlobalTheory.TorusExt.isIota_unique hi hg
    have heq := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 hadd
    have hg0 : g = 0 := by
      have : p.g + g = p.g + 0 := by simpa using heq.symm
      exact add_left_cancel this
    exact he.trans hg0
  rw [(GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 ha, h0, add_zero]

end GlobalTheory.TInj
