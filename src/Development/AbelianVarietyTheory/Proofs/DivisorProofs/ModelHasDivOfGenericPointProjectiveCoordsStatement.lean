module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHasDivOfGenericPointProjectiveCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (n : ℕ) (g : M.Z ⟶ PSpace o n) (e : Fin (n + 1) → Ω), PCrd (M.pt ≫ g) e → M.HasDiv e := by
  first | exact @GlobalTheory.UMin.hasDiv_of_pCrd_pt | exact GlobalTheory.UMin.hasDiv_of_pCrd_pt | (intros; apply GlobalTheory.UMin.hasDiv_of_pCrd_pt <;> assumption)
