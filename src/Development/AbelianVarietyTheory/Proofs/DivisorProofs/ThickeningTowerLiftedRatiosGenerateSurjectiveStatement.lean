module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosGenerateSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e (V : (Y e).left.Opens), towerIdeal Y e (I ^ (e + 1)) V = ⊥) ∧ ∀ e i, Function.Surjective (C.ev e i) := by
  first | exact @GlobalTheory.FormalAlg.LevSurj.ev_surjective | exact GlobalTheory.FormalAlg.LevSurj.ev_surjective | (intros; apply GlobalTheory.FormalAlg.LevSurj.ev_surjective <;> assumption)
