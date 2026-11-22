module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8FormValueCoprimeOddPrimePow
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_e8Form_value_coprime_oddPrimePow : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (p k : ℕ), p.Prime → p ≠ 2 → ∃ ε : Fin 8 → ℤ, Nat.Coprime ((p ^ k) ^ 2) (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs) := by
  first | exact @GlobalTheory.exists_e8Form_value_coprime_oddPrimePow' | exact GlobalTheory.exists_e8Form_value_coprime_oddPrimePow' | (intros; apply GlobalTheory.exists_e8Form_value_coprime_oddPrimePow' <;> assumption)
