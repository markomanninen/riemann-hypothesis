module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
public import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.HarderNarasimhan.QuotRealize
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.PassageScaleFree
public import Formalism.QuotientMetricDivisors.FinalW

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix MatrixOrder ComplexOrder
open Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.PairingDivisionLocalBalance Formalism.HN

noncomputable section

namespace GlobalTheory.Proof.DualMatrixMetricMeans

section Mat
open scoped Matrix.Norms.L2Operator

end Mat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

theorem meanInf_eq [_root_.NumberField.IsTotallyComplex K] (g : InfinitePlace K → ℝ) :
    meanInf K g = (1 / (nPl K : ℝ)) * ∑ v, g v := by
  have hn : (nPl K : ℝ) ≠ 0 := by
    have := Formalism.HN.twist_finrank_eq K
    have h0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    intro h; rw [h] at this; linarith
  unfold meanInf
  rw [Formalism.HN.twist_finrank_eq K]
  field_simp

theorem meanInf_const [_root_.NumberField.IsTotallyComplex K] (c : ℝ) : meanInf K (fun _ => c) = c := by
  have hn : (nPl K : ℝ) ≠ 0 := by
    have := Formalism.HN.twist_finrank_eq K
    have h0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    intro h; rw [h] at this; linarith
  rw [meanInf_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change 1 / (nPl K : ℝ) * ((nPl K : ℝ) * c) = c
  field_simp


end GlobalTheory.Proof.DualMatrixMetricMeans
