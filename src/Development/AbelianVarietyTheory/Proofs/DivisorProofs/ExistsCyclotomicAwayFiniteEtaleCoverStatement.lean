module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclotomicAwayFiniteEtaleCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomicAway_finiteEtale_cover : ∀ (M : ℕ) (S : Scheme.{0}), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∃ (S' : Over S) (t₀ : S'.left ⟶ Sp (cycAway M)), IsFinite S'.hom ∧ Etale S'.hom ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t₁ : T ⟶ Sp (cycAway M)), ∃! g : T ⟶ S'.left, g ≫ S'.hom = f ∧ g ≫ t₀ = t₁ := by
  first | (exact @GlobalTheory.CycAwayCover.exists_cycAway_cover) | (exact GlobalTheory.CycAwayCover.exists_cycAway_cover) | (intros; apply GlobalTheory.CycAwayCover.exists_cycAway_cover  <;> assumption)
