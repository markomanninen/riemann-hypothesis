module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

namespace GlobalTheory.QkDescent

theorem exists_qkExt_of_isAlgClosed : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), D.TauBimult → ∀ (F F' : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ k : ℕ, 1 ≤ k → ∀ p' : QkPt D F' k, ∃ p : QkPt D F k, QkExt f p p' := by
  intro hL R _ _ _ D hB F F' _ _ _ _ _ _ _ f hf k hk p'
  have hk' : (k : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  letI := GlobalTheory.TorusExt.gtGroup (D := D) (F := F)
  letI := GlobalTheory.TorusExt.gtGroup (D := D) (F := F')
  have hk0 : k ≠ 0 := by omega
  obtain ⟨q, hq⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) hL.mulN (Or.inr hL.polBaseChange) hB hk0 p'.y
  obtain ⟨h₀, h₁, h₂⟩ := q.eq
  obtain rfl := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 h₁
  obtain ⟨h', h₁', h₂'⟩ := p'.eq
  obtain rfl := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 h₁'
  have hh₀ : GtPtF.IsIota p'.y (k • q.g) := hq ▸ h₂
  have hext : GtPtF.IsIota p'.y (GlobalTheory.TorusExt.gtExt D f hf (k • q.g)) := by
    obtain ⟨b, -⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 hh₀
    refine (GlobalTheory.TorusExt.isIota_iff_val _ _).2 ⟨by rw [GlobalTheory.TorusExt.gtExt_b, b, ReciprocityTheory.ChartRestriction.G.DVR.comp_cP], fun χ y J hJ => ?_⟩
    rw [GlobalTheory.TorusExt.gtExt_val f hf _ χ hJ, GlobalTheory.TorusExt.tauVal, ← GlobalTheory.TorusExt.extMap_jFK f hf]
    exact (val_corr hJ (hh₀.2 χ) _).trans (val_pull hJ _ _ _)
  have e₀ : GlobalTheory.TorusExt.gtExt D f hf (k • q.g) = k • p'.g := GlobalTheory.TorusExt.isIota_unique hext h₂'
  have ht' : k • (p'.g - GlobalTheory.TorusExt.gtExt D f hf q.g) = 0 := by
    rw [nsmul_sub, ← map_nsmul, e₀, sub_self]
  obtain ⟨t, ht⟩ := GlobalTheory.ArcExt.exists_gtExt_of_torsion f hf hL hk' _ ht'
  have ht0 : k • t = 0 := GlobalTheory.ArcExt.gtExt_injective f hf (by rw [map_nsmul, ht, ht', map_zero])
  have e : p'.g = GlobalTheory.TorusExt.gtExt D f hf (q.g + t) := by rw [map_add (f := _), ht, add_sub_cancel]
  refine ⟨⟨p'.y, q.g + t, k • q.g, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_, hh₀⟩, rfl, (GlobalTheory.TorusExt.eq_gtExt_iff f hf _ _).1 e⟩
  rw [nsmul_add, ht0, add_zero]

end GlobalTheory.QkDescent
