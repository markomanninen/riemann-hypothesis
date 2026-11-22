module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthArchSectionEqSmulOfSameWeight
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constLengthArchSection_eq_smul_of_same_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → FnAlgClosed (Xo := Xo) (c := c) → ∀ (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (s t : ArchSec U x Z la), ∃ a : c.F, a ≠ 0 ∧ t.sig = a • s.sig := by
  first | exact @GlobalTheory.FlatCore.archSec_exists_eq_smul | exact GlobalTheory.FlatCore.archSec_exists_eq_smul | (intros; apply GlobalTheory.FlatCore.archSec_exists_eq_smul <;> assumption)
