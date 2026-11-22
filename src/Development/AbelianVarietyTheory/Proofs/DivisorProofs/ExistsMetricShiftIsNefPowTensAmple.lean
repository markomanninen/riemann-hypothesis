module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsNefPlusAmpleGeneratedGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefShiftOfGeneratedAtCharZeroPointsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOnFiniteFieldFibresPowTensStatement

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem exists_isNef_shift_pow_tens : GlobalTheory.Published.ArCalc → GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), L.SemiPos D → NefFib L → IsAmpleLB A.B → A.IsNef D → ∃ t : ℝ, (((L.pow n).tens A).shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro hC hN k _ X _ p D hX L A n hL hLf hA hAn
  obtain ⟨m, N, s, hm, hs⟩ := GlobalTheory.T.exists_sections_nefPlusAmple_generated_genericFibre hN k X p D hX L A n hLf hA
  obtain ⟨t, -, ht⟩ := GlobalTheory.NefOfGen.nef_of_gen hC k X p D hX ((L.pow n).tens A) m N s hm hs
    ((hL.pow n).tens hAn.semiPos) (GlobalTheory.T.nefOnFiniteFieldFibres_pow_tens k X p D hX L A n hLf (nefFib_of_isNef hAn))
  exact ⟨t, ht⟩

end GlobalTheory.VolBr
